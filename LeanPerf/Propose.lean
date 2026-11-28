import LeanPerf.Blocks
import LeanPerf.Signature
import LeanPerf.SyntaxDedup

/-!
# Rewrites that a proposer suggests

The lints in this package each try one kind of edit, and on a development that people have
already shortened by hand they find a few percent. The compact edition of the Riemann development
is four times smaller than the readable one because its proofs were written again: other
arguments, fewer steps, fewer lemmas. Finding such proofs is search that no fixed rule does, but
checking one is what LeanPerf already does well.

So this pass separates the two. For each theorem, together with the theorems right above it that
only it uses and no other module mentions, it sends a JSON request to a proposer, any command that
reads the request on standard input and writes `{"candidates": [...]}` on standard output. The
request holds the declaration, the source above it, and the theorems its proof uses. Each candidate
is elaborated in place of the commands from the state before them. It is accepted when the theorem
keeps its statement, universe parameters and docstring, no name is new, no proof has `sorry`, no
proof uses an axiom that the original does not, apart from Lean's three standard ones, and it
elaborates at most about twice as slowly. The
helpers may go: nothing else uses them. The shortest accepted candidate wins. When none is
accepted, the proposer is asked again with each candidate and Lean's errors for it, for a few
rounds.

The proposer can be a script around a language model, as `scripts/propose-claude` is, or any
other search. Its output is never trusted: only Lean's verdict decides.
-/

open Lean Elab Meta

namespace LeanPerf.Propose

/-- Run the shell command `cmd` with `req` on standard input and read its candidates. A proposer
    that fails or writes something else proposes nothing. -/
def ask (cmd : String) (req : Json) : IO (Array String) := do
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", cmd], stdin := .piped, stdout := .piped, stderr := .inherit }
  -- The pipe's only reference ends with this block, which closes the proposer's input.
  let child ← do
    let (stdin, child) ← child.takeStdin
    stdin.putStr req.compress
    stdin.flush
    pure child
  let out ← IO.asTask child.stdout.readToEnd
  let _ ← child.wait
  let some text := (out.get).toOption | return #[]
  match Json.parse text >>= (·.getObjValAs? (Array String) "candidates") with
  | .ok cs => return cs
  | .error _ => return #[]

/-- The theorems `name`'s proof uses, by names that resolve in the command's scope. -/
private def premisesOf (env : Environment) (scope : Command.Scope) (ctx : Command.Context)
    (name : Name) : IO (Array String) := do
  let some (.thmInfo t) := env.find? name | return #[]
  let x : MetaM (Array String) := Blocks.premises t.value
  try
    let (r, _) ← (x.run' {} {}).toIO
      { fileName := ctx.fileName, fileMap := ctx.fileMap, openDecls := scope.openDecls,
        currNamespace := scope.currNamespace, maxHeartbeats := 0 } { env }
    return r
  catch _ => return #[]

/-- Elaborate the commands of `text` from `before`. The final state, or what went wrong. -/
private def elabAll (text : String) (ctx : Command.Context) (before : Command.State) :
    IO (Except (Array String) Command.State) := do
  let ictx := Parser.mkInputContext text ctx.fileName
  let mut s := { before with messages := {}, infoState := { enabled := false } }
  let mut ps : Parser.ModuleParserState := {}
  repeat
    let scope := s.scopes.head!
    let pctx : Parser.ParserModuleContext :=
      { env := s.env, options := scope.opts
        currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let pos := ps.pos
    let (cmd, ps', msgs) := Parser.parseCommand ictx pctx ps {}
    if msgs.hasErrors then
      return .error (← msgs.toList.toArray.mapM fun m => return s!"parse error: {← m.data.toString}")
    if Parser.isTerminalCommand cmd then break
    ps := ps'
    let c := { ctx with fileMap := ictx.fileMap, cmdPos := pos }
    match ← ((Command.elabCommandTopLevel cmd).run c |>.run s).toIO' with
    | .ok ((), s') => s := s'
    | .error e => return .error #[← e.toMessageData.toString]
  let errs ← (s.messages.toList.filter (·.severity == .error)).toArray.mapM fun m =>
    return s!"{m.pos.line}:{m.pos.column}: {← m.data.toString}"
  return if errs.isEmpty then .ok s else .error errs

/-- Elaborate `text` in place of commands that took `before` to `after`. `none` when the theorems
    in `keep` have the statements they had, no other constant is new, and no proof has `sorry` or
    an axiom beyond Lean's standard ones that the original does not use; otherwise what is wrong,
    for the proposer. -/
def verify (text : String) (ctx : Command.Context) (before after : Command.State)
    (keep : Array Name) (docs := false) (budget : Option Nat := none) : IO (Option (Array String)) := do
  let h0 ← IO.getNumHeartbeats
  let s ← match ← elabAll text ctx before with
    | .ok s => pure s
    | .error errs => return some errs
  let used := (← IO.getNumHeartbeats) - h0
  if let some b := budget then
    if used > b then
      return some #[s!"it elaborates in {used / 1000} heartbeats, more than twice the original; find a faster proof"]
  let original := after.env.constants.map₂
  for (n, info') in s.env.constants.map₂.toList do
    if before.env.contains n || Replay.generated n then continue
    unless original.contains n do
      return some #[s!"`{n}` is new; declare no names besides the original ones"]
    if let .thmInfo t := info' then
      if t.value.hasSorry then return some #[s!"the proof of `{n}` uses `sorry`"]
  for n in keep do
    let some info := after.env.find? n | continue
    let some info' := s.env.find? n | return some #[s!"`{n}` is no longer declared; keep it"]
    unless info.type.equal info'.type && info.levelParams == info'.levelParams do
      return some #[s!"the statement of `{n}` changed; keep it exactly as it is"]
    unless info' matches .thmInfo _ do return some #[s!"`{n}` must stay a theorem"]
    if docs && (← findDocString? after.env n) != (← findDocString? s.env n) then
      return some #[s!"keep the docstring of `{n}` as it is"]
  let axioms (env : Environment) (n : Name) := (collectAxioms (m := CoreM) n).toIO'
    { fileName := ctx.fileName, fileMap := ctx.fileMap } { env }
  -- Lean's three standard axioms are always allowed; any other, such as `sorryAx` or
  -- `Lean.ofReduceBool`, only where the original already uses it.
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for n in keep do
    let some (old, new) ← (try pure (some (← axioms after.env n, ← axioms s.env n)) catch _ => pure none)
      | return some #["cannot check the axioms"]
    let extra := new.filter fun a => !old.contains a && !standard.contains a
    unless extra.isEmpty do return some #[s!"the proof uses axioms the original does not: {extra.toList}"]
  return none

/-- The start of the line at or before byte `i`. A newline byte never occurs inside a character. -/
private def lineStart (bytes : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := min i bytes.size
  while j > 0 && bytes[j-1]! != 10 do j := j - 1
  return j

/-- The source above `pos`, at most about `limit` bytes: the start of the file, which holds the
    imports and opens, and the part just above, both cut at line starts. -/
private def contextOf (input : String) (pos : String.Pos.Raw) (limit := 24000) : String :=
  if pos.byteIdx ≤ limit then String.Pos.Raw.extract input 0 pos
  else
    let bytes := input.toUTF8
    let head := String.Pos.Raw.extract input 0 ⟨lineStart bytes 4000⟩
    let tail := String.Pos.Raw.extract input ⟨lineStart bytes (pos.byteIdx - (limit - 4000))⟩ pos
    head ++ "-- …\n" ++ tail

/-- The JSON request for one round. -/
def request (file text : String) (keep free : Array Name) (context : String) (premises : Array String)
    (round : Nat) (failures : Array Json) : Json :=
  Json.mkObj [("file", file), ("declaration", text), ("keep", toJson (keep.map toString)),
    ("free", toJson (free.map toString)), ("context", context), ("premises", toJson premises),
    ("round", round), ("failures", toJson failures)]

/-- A command of the module as it was elaborated. -/
structure Record where
  cmd : Syntax
  ctx : Command.Context
  before : Command.State
  after : Command.State
  /-- Raw heartbeats its elaboration took. -/
  heartbeats : Nat := 0

/-- The text of commands `a` to `b` that a proposer sees and a rewrite replaces. A single command
    keeps its docstring. -/
def span (input : String) (records : Array Record) (a b : Nat) : Option Syntax.Range := do
  let first ← records[a]?
  let r0 ← first.cmd.getRange? (canonicalOnly := true)
  let r1 ← (← records[b]?).cmd.getRange? (canonicalOnly := true)
  if a != b then return ⟨r0.start, r1.stop⟩
  let some docEnd := first.cmd[0][0].getTailPos? (canonicalOnly := true) | return ⟨r0.start, r1.stop⟩
  let mut p := docEnd
  while p < r1.stop && (p.get input).isWhitespace do p := p.next input
  return ⟨p, r1.stop⟩

/-- Ask `proposer` for a shorter text in place of the commands `records[a:b+1]`, which take
    `records[a].before` to `records[b].after`, keeping the statements of `keep`, at most twice as
    slowly as they elaborated plus `slack` raw heartbeats. The theorems in
    `free` are used only there and may go. Returns the range replaced, the text and how many rounds
    it took. `first?` is the proposer's answer to the first round, when it is already known. -/
def rewrite? (input : String) (records : Array Record) (a b : Nat) (keep free : Array Name)
    (proposer : String) (rounds := 3) (minBytes := 160) (first? : Option (Array String) := none)
    (slack := 2000000) : IO (Option (Syntax.Range × String × Nat)) := do
  let some first := records[a]? | return none
  let some last := records[b]? | return none
  let some ⟨start, stop⟩ := span input records a b | return none
  let text := String.Pos.Raw.extract input start stop
  if text.utf8ByteSize < minBytes then return none
  let scope := first.before.scopes.head!
  let mut premises := #[]
  for n in keep ++ free do
    for p in ← premisesOf last.after.env scope first.ctx n do
      unless premises.contains p do premises := premises.push p
  let context := contextOf input start
  let mut failures : Array Json := #[]
  for round in [:rounds] do
    let req := request first.ctx.fileName text keep free context premises round failures
    let answer ← match round, first? with
      | 0, some cs => pure cs
      | _, _ => ask proposer req
    let candidates := answer.map (·.trimAscii.toString)
    let shorter := (candidates.filter (·.utf8ByteSize < text.utf8ByteSize)).qsort
      (·.utf8ByteSize < ·.utf8ByteSize)
    if shorter.isEmpty then return none
    failures := #[]
    for c in shorter do
      -- A single command's docstring is outside the text; a group's are inside it.
      let budget := 2 * ((records.extract a (b + 1)).foldl (· + ·.heartbeats) 0) + slack
      match ← verify c first.ctx first.before last.after keep (docs := a != b) (budget := some budget) with
      | none =>
        -- Accepted rewrites are training data for a proposer of one's own.
        if let some log ← IO.getEnv "LEANPERF_PROPOSE_LOG" then
          let h ← IO.FS.Handle.mk log .append
          h.putStrLn (Json.mkObj [("file", first.ctx.fileName), ("before", text), ("after", c),
            ("keep", toJson (keep.map toString)), ("free", toJson (free.map toString)),
            ("rounds", toJson (round + 1))]).compress
        return some (⟨start, stop⟩, c, round + 1)
      | some errs => failures := failures.push (Json.mkObj [("candidate", c), ("errors", toJson errs)])
  return none

/-- The first-round request for commands `a` to `b`, if they are long enough to send. -/
def firstRequest (input : String) (records : Array Record) (a b : Nat) (keep free : Array Name)
    (minBytes := 160) : IO (Option Json) := do
  let some first := records[a]? | return none
  let some last := records[b]? | return none
  let some ⟨start, stop⟩ := span input records a b | return none
  let text := String.Pos.Raw.extract input start stop
  if text.utf8ByteSize < minBytes then return none
  let scope := first.before.scopes.head!
  let mut premises := #[]
  for n in keep ++ free do
    for p in ← premisesOf last.after.env scope first.ctx n do
      unless premises.contains p do premises := premises.push p
  return some (request first.ctx.fileName text keep free (contextOf input start) premises 0 #[])

/-- The identifiers' name components in `text`. -/
private def components (text : String) : Std.HashSet String := Id.run do
  let chars := text.toList.toArray
  let mut out := {}
  for (t, _) in SyntaxDedup.tokenize chars do
    for c in t.splitOn "." do
      unless c.isEmpty do out := out.insert c
  return out

/-- Groups of commands to rewrite together: a theorem with the theorems right above it that only the
    group uses and that no other module mentions (`external` lists the last name components that
    other modules mention). Each group is `(a, b, keep, free)` for the commands `a` to `b`. -/
def groups (input : String) (records : Array Record) (external : Std.HashSet String)
    (maxBytes := 8000) (maxCommands := 6) : Array (Nat × Nat × Array Name × Array Name) := Id.run do
  let n := records.size
  -- Each command's theorem, if it is one without attributes, and the components it mentions.
  let info := records.map fun r =>
    let thm := Signature.asTheorem? r.cmd
    let name := thm.bind fun t => Signature.theoremName? t[1] r.before r.after
    let attributed := r.cmd[0][1].getNumArgs > 0
    let text := match r.cmd.getRange? (canonicalOnly := true) with
      | some rg => String.Pos.Raw.extract input rg.start rg.stop
      | none => ""
    (if attributed then none else name, text.utf8ByteSize, components text)
  let last (k : Nat) : Option String := (info[k]!.1.map (·.componentsRev.head!.toString))
  -- A helper is used by a later command of the group and by no command outside it. A theorem that
  -- nothing uses is a result of the module, or dead code for `--unused`, and stays.
  let helperOf (k hi : Nat) : Bool := Id.run do
    let some l := last k | return false
    let mut used := false
    for j in [:n] do
      if j == k then continue
      if info[j]!.2.2.contains l then
        if k < j && j ≤ hi then used := true else return false
    return used
  let mut out := #[]
  let mut b := n
  while b > 0 do
    b := b - 1
    let some anchor := info[b]!.1 | continue
    let mut a := b
    let mut size := info[b]!.2.1
    while a > 0 do
      let k := a - 1
      let some l := last k | break
      if external.contains l || b - k + 1 > maxCommands || size + info[k]!.2.1 > maxBytes then break
      unless helperOf k b do break
      a := k
      size := size + info[k]!.2.1
    let free := ((List.range (b - a)).map (a + ·)).toArray.filterMap (info[·]!.1)
    out := out.push (a, b, #[anchor], free)
    b := a
  return out.reverse

end LeanPerf.Propose
