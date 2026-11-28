import LeanPerf.Blocks
import LeanPerf.Steps
import LeanPerf.Combine
import LeanPerf.Lints
import LeanPerf.Instances
import LeanPerf.Layout
import LeanPerf.Golf
import LeanPerf.Fold
import LeanPerf.Propose
import LeanPerf.ProofCompression
import LeanPerf.Redundant
import LeanPerf.Prune
import LeanPerf.Reprove
import LeanPerf.Signature

/-!
# Cheaper tactics and unneeded option overrides

Elaborates a module once with info trees enabled. For every tactic occurrence that a rule names, it
replays the original and each candidate on the same goals, in the same metavariable context, and
counts heartbeats. A candidate is suggested when every goal the occurrence ran on

* is closed or transformed into exactly the same goals (up to fvar identity) as the original,
* has no errors, no `sorry` in its proof, and
* costs fewer heartbeats than the original.

`set_option o v in cmd` overrides are re-elaborated without the option from the state before the
command and reported when the command still elaborates without errors.

Heartbeats measure elaboration only. Kernel checking is not included, so an accepted edit should
still be confirmed by elaborating the whole edited module (`--check`).
-/

open Lean Elab Meta

namespace LeanPerf.Tactics

open Replay (Run)

structure Edit where
  rule : String
  message : String
  range : Lsp.Range
  newText : String
  /-- The steps the edit takes out of its command, or 1000 for each declaration (`Steps.worth`). -/
  gain : Nat := 0
  deriving ToJson, FromJson, Inhabited

/-- The leading identifier-like token of a tactic, e.g. `simp_all` or `nlinarith`. -/
def head (text : String) : String :=
  (text.takeWhile fun c => c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!').toString

/-- Text after the head token. -/
def rest (text : String) : String := (text.drop (head text).length).toString

/-- Candidate replacements. A candidate ending in a `?`-variant is a request for a suggestion,
    which is then tried in its place. The queue takes candidates from the end, so cheap closers
    come last: the first success bounds the heartbeats of every later attempt. -/
def candidates (text : String) : Array String :=
  let h := head text
  let r := rest text
  let bare := r.trimAscii.isEmpty
  let only := (r.trimAsciiStart.toString.startsWith "only")
  match h with
  | "nlinarith" => #["linarith" ++ r] ++ (if bare then #["positivity"] else #[])
  | "linarith" => if bare then #["assumption", "omega"]
      else if r.trimAsciiStart.startsWith "[" then #["assumption"] else #[]
  | "norm_num" => if only then #[] else #["simp" ++ r]
  -- A rewrite with the same lemmas, when they rewrite in order and `rfl` closes what is left.
  | "simp" | "simp_rw" =>
    let args := (if only then (r.trimAsciiStart.drop 4).toString else r).trimAsciiStart.toString
    (if only || h == "simp_rw" then #[] else #[h ++ "?" ++ r]) ++
      (if args.startsWith "[" then #["rw " ++ args] else #[])
  | "simp_all" | "simpa" => if only then #[] else #[h ++ "?" ++ r]
  -- `erw` unfolds instances to match; an ordinary rewrite is cheaper when it finds the same motive.
  | "erw" => #["rw" ++ r]
  -- `grind?` reports the `grind only [...]` call that closes the goal.
  | "grind" => if only then #[] else
      #["grind?" ++ r] ++ (if bare then #["linarith", "positivity", "simp_all", "simp", "omega"] else #[])
  | "aesop" => if bare then #["simp_all", "simp"] else #[]
  | _ => #[]

/-- The overrides worth trying to remove. -/
def overridable : List Name :=
  [`maxHeartbeats, `synthInstance.maxHeartbeats, `maxRecDepth, `synthInstance.maxSize,
   `backward.isDefEq.lazyWhnfCore, `backward.isDefEq.lazyProjDelta]

/-- Try restricting arithmetic search to the named hypotheses used by the original proof.
    Dependencies found in the proof term are only a hint; each candidate is replayed. -/
private def arithmeticSuggestions (text : String) (stx : Syntax) (proof : Expr) : MetaM (Array String) := do
  let tactic := head text
  unless tactic == "linarith" || tactic == "nlinarith" do return #[]
  let suffix := (rest text).trimAscii.toString
  let mut explicit := #[]
  unless suffix.isEmpty do
    -- Locate the original bracket group in the parsed tactic. An argument can itself contain
    -- commas, nested brackets or an entire proof. Slice complete terms by their source ranges.
    let some group := stx.find? fun node => Id.run do
      let n := node.getNumArgs
      if n < 3 || node[n-3].getAtomVal != "[" || node[n-1].getAtomVal != "]" then return false
      let some start := node[n-3].getPos? | return false
      let some stop := node[n-1].getTailPos? | return false
      return String.Pos.Raw.extract text start stop == suffix
      | return #[]
    for arg in group[group.getNumArgs-2].getSepArgs do
      let some r := arg.getRange? | return #[]
      explicit := explicit.push (String.Pos.Raw.extract text r.start r.stop)
  let ctx ← getLCtx
  let used := (collectFVars {} proof).fvarSet
  let mut names := #[]
  for d in ctx do
    unless used.contains d.fvarId && !d.isImplementationDetail && !d.userName.hasMacroScopes do continue
    unless (ctx.findFromUserName? d.userName).any (·.fvarId == d.fvarId) do continue
    if ← isProp d.type then names := names.push d.userName.toString
  let restricted (hs : Array String) := Id.run do
    let args := " only [" ++ ", ".intercalate hs.toList ++ "]"
    return if tactic == "nlinarith" then #["nlinarith" ++ args, "linarith" ++ args] else #["linarith" ++ args]
  let mut hints := restricted names
  unless explicit.isEmpty do
    hints := hints ++ restricted explicit
    let combined := names ++ explicit.filter (!names.contains ·)
    unless combined == names || combined == explicit do hints := hints ++ restricted combined
  return hints

/-- Run tactic `text` on `goal`. `budget` is in raw heartbeats; `none` means failure or over budget. -/
def runOn (ci : ContextInfo) (map : FileMap) (mctx : MetavarContext) (goal : MVarId) (text : String)
    (budget : Nat) (minePremises := false) (site : Option Syntax.Range := none) : IO (Option Run) := do
  let .ok stx := Parser.runParserCategory ci.env `tactic text "<leanperf>" | return none
  Replay.run ci map mctx goal (site.elim stx (Replay.relocate · stx)) budget fun goal proof gs => do
    unless minePremises && gs.isEmpty do return #[]
    let mut sugg ← arithmeticSuggestions text stx proof
    if ["linarith", "nlinarith"].contains (head text) then
      let paths ← Relations.candidates (← instantiateMVars (← goal.getType))
      sugg := sugg ++ paths.map ("exact " ++ ·)
    return sugg

/-- One syntactic occurrence and every goal it ran on. -/
structure Site where
  range : Lean.Syntax.Range
  text : String
  runs : Array (ContextInfo × MetavarContext × MVarId)

private def sites (input : String) (tree : InfoTree) (select : String → Bool) : Array Site := Id.run do
  let found := tree.foldInfo (init := #[]) fun ci i acc => match i with
    | .ofTacticInfo ti =>
      match ti.stx.getRange? (canonicalOnly := true), ti.goalsBefore with
      | some r, g :: _ => acc.push (r, ci, ti.mctxBefore, g)
      | _, _ => acc
    | _ => acc
  let mut out : Array Site := #[]
  for (r, ci, mctx, g) in found do
    let text := String.Pos.Raw.extract input r.start r.stop
    unless select text do continue
    match out.findIdx? (·.range == r) with
    | some k =>
      -- Macro expansions record the same occurrence more than once.
      let dup := match out[k]? with | some s => s.runs.any (·.2.2 == g) | none => true
      unless dup do
        out := out.modify k fun s => { s with runs := s.runs.push (ci, mctx, g) }
    | none => out := out.push { range := r, text, runs := #[(ci, mctx, g)] }
  return out

/-- Total cost of `text` over all goals of the site, and whether it matches `reference` goals. -/
private def trySite (map : FileMap) (s : Site) (text : String) (budget : Nat)
    (reference : Option (Array (List (Expr × List Name)))) :
    IO (Option (Nat × Array (List (Expr × List Name)) × Array String)) := do
  let mut total := 0
  let mut goals := #[]
  let mut sugg := #[]
  for h : k in [:s.runs.size] do
    let (ci, mctx, g) := s.runs[k]
    if budget > 0 && total ≥ budget then return none
    let some r ← runOn ci map mctx g text (if budget == 0 then 0 else budget - total) reference.isNone s.range
      | return none
    if let some ref := reference then
      unless ref[k]? == some r.goals do return none
    total := total + r.heartbeats
    goals := goals.push r.goals
    sugg := sugg ++ r.suggestions
  return some (total, goals, sugg)

/-- `text` written at column `col`: its lines after the first move right by `col`, keeping their
    indentation relative to the first. Lean wraps a long `Try this:` suggestion at its own width and
    starts the next line at column 4; after an inline `by`, as in `have h : t := by simpa … using`,
    that is left of the tactic block, and the term after `using` ends at its head. -/
def placeAt (text : String) (col : Nat) : String :=
  match text.splitOn "\n" with
  | first :: rest@(_ :: _) =>
    let pad := String.ofList (List.replicate col ' ')
    "\n".intercalate (first :: rest.map fun l => if l.trimAscii.isEmpty then l else pad ++ l)
  | _ => text

def tacticEdits (input : String) (map : FileMap) (tree : InfoTree) (minSaving : Nat) (shorter : Bool) :
    IO (Array Edit) := do
  let mut edits := #[]
  for s in sites input tree (fun text => !(candidates text).isEmpty) do
    if s.text.contains "/-" || s.text.contains "--" then continue
    let some (base, ref, hints) ← trySite map s s.text 0 none | continue
    if base < minSaving then continue
    let mut best : Option (String × Nat) := none
    let mut queue := candidates s.text ++ hints
    let mut tried : Array String := #[]
    while let some c := queue.back? do
      queue := queue.pop
      if tried.contains c then continue
      tried := tried.push c
      let isQuery := (head c).endsWith "?"
      if shorter && !isQuery && c.utf8ByteSize ≥ s.text.utf8ByteSize then continue
      let limit := if isQuery then 0 else (best.map (·.2)).getD base
      let some (cost, _, sugg) ← trySite map s c limit (some ref)
        | continue
      if isQuery then
        queue := queue ++ sugg.filter (· != s.text)
      else if cost < base && cost + minSaving ≤ base && best.all (cost < ·.2) then
        best := some (c, cost)
    if let some (c, cost) := best then
      edits := edits.push {
        rule := "fasterTactic"
        message := s!"{s.text.take 60} → {c.take 60}: {base / 1000} → {cost / 1000} heartbeats"
        range := map.utf8RangeToLspRange s.range, newText := placeAt c (map.toPosition s.range.start).column }
  return edits

/-- The optional `only` and bracketed arguments of a simplifier call. -/
private def simpArgs? (stx : Syntax) : Option (Syntax × Syntax) := do
  let (only, args) ←
    if stx.isOfKind ``Parser.Tactic.simpa || stx.isOfKind ``Parser.Tactic.simpaUsingBang then
      some (stx[3][2], stx[3][3][0])
    else if [``Parser.Tactic.simp, ``Parser.Tactic.simpAll, ``Parser.Tactic.dsimp].contains stx.getKind then
      some (stx[3], stx[4])
    else none
  guard (args.getNumArgs == 3 && args[0].getAtomVal == "[" && args[2].getAtomVal == "]")
  return (only, args)

/-- Check parser trivia so comment delimiters inside a lemma's string literal are harmless. -/
private def simpHasComment (stx : Syntax) : Bool :=
  (stx.find? fun node =>
    let atom := node.getAtomVal
    atom.startsWith "/-" ||
      match node.getInfo? with
      | some (.original leading _ trailing _) =>
        !leading.toString.trimAscii.isEmpty || !trailing.toString.trimAscii.isEmpty
      | _ => false).isSome

/-- The shortest checked rewrite found by dropping the list, then pruning it with and without `only`. -/
private def shorterSimp? (map : FileMap) (s : Site) : IO (Option String) := do
  let some (ci, _, _) := s.runs[0]? | return none
  let .ok stx := Parser.runParserCategory ci.env `tactic s.text | return none
  let some (only, args) := simpArgs? stx | return none
  if (s.text.contains "/-" || s.text.contains "--") && simpHasComment stx then return none
  let some bracket := args.getRange? | return none
  let slice := String.Pos.Raw.extract s.text
  let size := s.text.utf8ByteSize
  let beforeList := slice 0 bracket.start
  let suffix := slice bracket.stop ⟨size⟩
  let beforeOnly := only.getPos?.map (slice 0)
  let plain := beforeOnly.getD beforeList
  let withoutList (p : String) :=
    let sep := if suffix.isEmpty || suffix.front.isWhitespace then "" else " "
    p.trimAsciiEnd.toString ++ sep ++ suffix
  let some (base, ref, _) ← trySite map s s.text 0 none | return none
  let accepts (text : String) : IO Bool := do
    let saved := size - text.utf8ByteSize
    if saved == 0 then return false
    let budget := 2 * base + 5000 * saved
    let some (cost, _, _) ← trySite map s text budget (some ref) | return false
    return cost ≤ budget
  let bare := withoutList plain
  if ← accepts bare then return if bare.utf8ByteSize + 4 ≤ size then some bare else none

  let nodes := args[1].getSepArgs
  let some ranges := nodes.mapM fun arg => do
    guard ([``Parser.Tactic.simpLemma, ``Parser.Tactic.simpErase, ``Parser.Tactic.simpStar].contains arg.getKind)
    arg.getRange?
    | return none
  -- Each retained lemma keeps its own following separator and the indentation it provides.
  let elems := ranges.mapIdx fun i r =>
    (slice r.start r.stop, (ranges[i+1]?).elim "" (fun next => slice r.stop next.start))
  let mut best := s.text
  for p in (if beforeOnly.isSome then #[plain, beforeList] else #[beforeList]) do
    let mut kept := elems
    for i in (List.range elems.size).reverse do
      let reduced := kept.eraseIdx! i
      let text := if reduced.isEmpty then withoutList p else Id.run do
        let mut text := p ++ slice bracket.start ranges[0]!.start
        for ((arg, sep), j) in reduced.toList.zipIdx do
          text := text ++ arg ++ (if j + 1 < reduced.size then sep else "")
        return text ++ "]" ++ suffix
      if reduced.isEmpty && text == bare then continue
      if ← accepts text then
        kept := reduced
        if text.utf8ByteSize < best.utf8ByteSize then best := text
  return if best.utf8ByteSize + 4 ≤ size then some best else none

/-- Shorten simplifier calls that leave the same goals on every run of the step. -/
def simpEdits (input : String) (map : FileMap) (tree : InfoTree) : IO (Array Edit) := do
  let mut edits := #[]
  for s in sites input tree (fun text => ["simp", "simp_all", "simpa", "dsimp"].contains (head text) &&
      text.contains '[') do
    if let some text ← shorterSimp? map s then
      edits := edits.push {
        rule := "shorterSimp", message := "Shorten the simplifier arguments",
        range := map.utf8RangeToLspRange s.range, newText := text }
  return edits

/-- `set_option o v in cmd` for an overridable `o`: the option and the inner command. -/
def override? (cmd : Syntax) : Option (Name × Syntax) :=
  if cmd.isOfKind ``Parser.Command.in && cmd[0].isOfKind ``Parser.Command.set_option then
    let o := cmd[0][1].getId
    if overridable.contains o then some (o, cmd[2]) else none
  else none

/-- A declaration, whose elaboration leaves the parser as it was unless an attribute or a nested
    command extends the grammar. -/
def declarationLike (input : String) (cmd : Syntax) : Bool := Id.run do
  let inner := if cmd.isOfKind ``Parser.Command.in then cmd[2] else cmd
  unless inner.isOfKind ``Parser.Command.declaration || (inner.getKind matches .str _ "lemma") do return false
  let some r := cmd.getRange? | return false
  let head := String.Pos.Raw.extract input r.start ⟨min r.stop.byteIdx (r.start.byteIdx + 400)⟩
  return !["parser", "macro", "elab", "syntax", "notation"].any (head.contains ·)

/-- Lints whose edits rest only on replaying a step, not on elaborating the whole command. -/
def replayed : List String :=
  ["fasterTactic", "reuseProof", "shorterBlock", "shorterSimp", "unneededStep", "contractPair"] ++ Lints.redundant

/-- `seal f in cmd` or `unseal f in cmd`: the keyword and the inner command. -/
def sealed? (cmd : Syntax) : Option (String × Syntax) := do
  guard (cmd.isOfKind ``Parser.Command.in)
  let kw := cmd[0][0].getAtomVal.trimAscii.toString
  guard (kw == "seal" || kw == "unseal")
  return (kw, cmd[2])

/-- The start of the line above `pos` when it holds only a `--` comment and a blank line or the
    start of the file comes before it: a comment that explains the line at `pos`. -/
private def commentAbove (input : String) (map : FileMap) (pos : String.Pos.Raw) : String.Pos.Raw := Id.run do
  let line := (map.toPosition pos).line
  if line < 2 then return pos
  let above := map.ofPosition { line := line - 1, column := 0 }
  let text := (String.Pos.Raw.extract input above (map.ofPosition { line, column := 0 })).trimAscii
  unless text.startsWith "--" do return pos
  if line > 2 then
    let twoAbove := map.ofPosition { line := line - 2, column := 0 }
    unless (String.Pos.Raw.extract input twoAbove above).trimAscii.isEmpty do return pos
  return above

/-- Heartbeats to elaborate `cmd` from `s` without info trees, and the resulting state, when it
    elaborates without errors. -/
private def cost (cmd : Syntax) (ctx : Command.Context) (s : Command.State) : IO (Option (Nat × Command.State)) := do
  let plain := { s with messages := {}, infoState := { enabled := false } }
  let h0 ← IO.getNumHeartbeats
  match ← ((Command.elabCommandTopLevel cmd).run ctx |>.run plain).toIO' with
  | .ok ((), s') =>
    if s'.messages.hasErrors then return none
    return some ((← IO.getNumHeartbeats) - h0, s')
  | .error _ => return none

/-- Whether both states declare the constants new since `before` with the same types. -/
private def sameDecls (before a b : Environment) : Bool :=
  a.constants.map₂.toList.all fun (n, c) =>
    before.contains n || (b.find? n).any (·.type.equal c.type)

/-- Rules whose edit can leave a proof with as many steps as before: an edit of theirs must take
    steps out of its command. -/
def stepGated : List String := ["reprove", "reuseProof", "termCompile"]

/-- Whether `e`, applied alone, takes tactic steps out of the command `cmd`. An edit outside the
    command, or one after which the command does not parse alone, is kept: elaboration decides. -/
def fewerSteps (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (fileName : String) (e : Edit) : Bool := Id.run do
  let some r := cmd.getRange? (canonicalOnly := true) | return true
  let er := map.lspRangeToUtf8Range e.range
  unless r.start ≤ er.start && er.stop ≤ r.stop do return true
  let kinds := Steps.tacticKinds pctx.env
  let text := String.Pos.Raw.extract input r.start er.start ++ e.newText ++ String.Pos.Raw.extract input er.stop r.stop
  match Steps.ofCommand kinds text pctx fileName with
  | some n => decide (n < Steps.count kinds cmd)
  | none => true

structure Result where
  edits : Array Edit := #[]
  errors : Array String := #[]
  /-- The tactic steps (`Steps.count`) and declarations of the module as it was read. -/
  steps : Nat := 0
  decls : Nat := 0
  deriving Inhabited

/-- Elaborate `input` on top of `env` (its imports), collecting edits. -/
def analyze (env : Environment) (main : Name) (fileName input : String) (opts : Options)
    (minSaving : Nat := 1000) (tactics options : Bool := true) (shorter := false)
    (compression : Option ProofCompression.Index := none)
    (signatures prune searchProofs := compression.isSome) (redundant : List String := [])
    (instances : Option (Name → Bool) := none) (seals := false) (blocks := false) (steps := false) (layout := false)
    (proposer : Option String := none) (external : Array String := #[]) (comments := false)
    (golf : List String := []) (fold := false) (simpArgs := false) (pairs := false) : IO Result := do
  let ictx := Parser.mkInputContext input fileName
  let (_, ps0, _) ← Parser.parseHeader ictx
  let mut s := Command.mkState (env.setMainModule main) {} opts
  let mut ps := ps0
  let mut res : Result := {}
  let mut localProofs : ProofCompression.Index := {}
  let mut records : Array Propose.Record := #[]
  let needInfo := tactics || signatures || searchProofs || compression.isSome || !redundant.isEmpty || blocks || steps ||
    simpArgs || pairs || golf.contains "shortNames" || golf.contains "obtainProjection"
  -- Joining lines needs only the parser state, which declarations do not change.
  let parseOnly := (layout || comments) && !needInfo && !options && !seals && !prune && instances.isNone && proposer.isNone
  repeat
    let scope := s.scopes.head!
    let pctx : Parser.ParserModuleContext :=
      { env := s.env, options := scope.opts
        currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', log) := Parser.parseCommand ictx pctx ps {}
    if log.hasErrors && res.errors.size < 5 then
      res := { res with errors := res.errors.push s!"parse error at byte {ps.pos.byteIdx}" }
    let pos := ps.pos
    ps := ps'
    if Parser.isTerminalCommand cmd then break
    res := { res with steps := res.steps + Steps.count (Steps.tacticKinds pctx.env) cmd
                      decls := res.decls + (if Steps.isDeclaration cmd then 1 else 0) }
    let ctx : Command.Context :=
      { fileName, fileMap := ictx.fileMap, cmdPos := pos, snap? := none, cancelTk? := none }
    if comments then
      for (rg, t) in Layout.stripComments input cmd pctx fileName do
        res := { res with edits := res.edits.push {
          rule := "stripComments", message := "Delete this comment", newText := t
          range := ictx.fileMap.utf8RangeToLspRange rg } }
    if layout then
      for j in Layout.joins input cmd pctx fileName do
        res := { res with edits := res.edits.push {
          rule := "joinLines", message := "Join this line to the one above", newText := " "
          range := ictx.fileMap.utf8RangeToLspRange j } }
    if parseOnly && declarationLike input cmd then continue
    let before := { s with messages := {}, infoState := { enabled := needInfo } }
    let h0 ← IO.getNumHeartbeats
    match ← ((Command.elabCommandTopLevel cmd).run ctx |>.run before).toIO' with
    | .error e =>
      -- Without the declarations, a command that names one fails; parsing does not need it.
      unless parseOnly do res := { res with errors := res.errors.push (← e.toMessageData.toString) }
      if proposer.isSome || fold then records := records.push { cmd, ctx, before, after := before }
    | .ok ((), after) =>
      -- What the command cost to elaborate bounds what replaying its steps may cost.
      let spent := (← IO.getNumHeartbeats) - h0
      if proposer.isSome || fold then
        records := records.push { cmd, ctx, before, after := if after.messages.hasErrors then before else after
                                  heartbeats := spent }
      if after.messages.hasErrors then
        for m in after.messages.toList do
          if m.severity == .error && res.errors.size < 5 && !parseOnly then
            res := { res with errors := res.errors.push s!"{m.pos.line}:{m.pos.column + 1}: {← m.data.toString}" }
      else
        let mark := res.edits.size
        if signatures then
          if let some e ← Signature.compress input ictx.fileMap cmd ctx before after then
            res := { res with edits := res.edits.push {
              rule := "shorterSignature", message := "Shorten the theorem statement",
              range := e.range, newText := e.newText } }
        if searchProofs then
          if let some e ← Reprove.proof? input ictx.fileMap cmd ctx before after then
            res := { res with edits := res.edits.push {
              rule := "reprove", message := s!"Re-prove with {e.newText}",
              range := e.range, newText := e.newText } }
        if let some cited := instances then
          for r in ← Instances.edits input ictx.fileMap cmd pctx ctx before after cited do
            res := { res with edits := res.edits.push {
              rule := "unusedInstance", message := "Neither the statement nor the proof uses this instance",
              range := ictx.fileMap.utf8RangeToLspRange r, newText := "" } }
        unless golf.isEmpty do
          for e in ← Golf.edits input ictx.fileMap cmd pctx ctx before after golf do
            res := { res with edits := res.edits.push {
              rule := e.rule, message := e.message,
              range := ictx.fileMap.utf8RangeToLspRange e.range, newText := e.newText } }
        if prune then
          if let some e ← Prune.proof? input ictx.fileMap cmd pctx ctx before after then
            res := { res with edits := res.edits.push {
              rule := "unusedHave", message := "Remove unused local proofs",
              range := e.range, newText := e.newText } }
        if tactics || compression.isSome || !redundant.isEmpty || blocks || steps || simpArgs || pairs then
          let mut names : NameSet := {}
          for t in after.infoState.trees do
            let t := Replay.withEnv before.env t
            if tactics then
              res := { res with edits := res.edits ++ (← tacticEdits input ictx.fileMap t minSaving shorter) }
            if simpArgs then
              res := { res with edits := res.edits ++ (← simpEdits input ictx.fileMap t) }
            if pairs then
              -- The theorem up to its proof, for a model that proposes contractions.
              let statement := match Signature.asTheorem? cmd, cmd.getPos? (canonicalOnly := true) with
                | some thm, some p => match thm[1][3].getPos? (canonicalOnly := true) with
                  | some q => String.Pos.Raw.extract input p q ++ ":= by"
                  | none => ""
                | _, _ => ""
              for e in ← Blocks.contractPairs input ictx.fileMap t (statement := statement) (spent := spent) do
                res := { res with edits := res.edits.push {
                  rule := "contractPair", message := e.message,
                  range := ictx.fileMap.utf8RangeToLspRange e.range, newText := e.newText } }
            if steps then
              for e in ← Blocks.unneededSteps input ictx.fileMap t (spent := spent) do
                res := { res with edits := res.edits.push {
                  rule := "unneededStep", message := e.message,
                  range := ictx.fileMap.utf8RangeToLspRange e.range, newText := e.newText } }
            if blocks then
              for e in ← Blocks.edits input ictx.fileMap t (spent := spent) do
                res := { res with edits := res.edits.push {
                  rule := "shorterBlock", message := e.message,
                  range := ictx.fileMap.utf8RangeToLspRange e.range, newText := e.newText } }
            for e in ← Redundant.edits input ictx.fileMap t redundant (spent := spent) do
              res := { res with edits := res.edits.push {
                rule := e.rule, message := e.message,
                range := ictx.fileMap.utf8RangeToLspRange e.range, newText := e.newText } }
          for t in after.infoState.trees do
            if let some imports := compression then
              let (edits, decls) ← ProofCompression.scan input ictx.fileMap (Replay.withEnv before.env t)
                imports localProofs
              names := names.merge decls
              for e in edits do
                res := { res with edits := res.edits.push {
                  rule := "reuseProof", message := s!"Reuse {e.newText}",
                  range := e.range, newText := e.newText } }
          if compression.isSome then localProofs := ProofCompression.addDecls localProofs after.env names
        if options then
          if let some (o, inner) := override? cmd then
            let plain := { before with infoState := { enabled := false } }
            let ok ← match ← ((Command.elabCommandTopLevel inner).run ctx |>.run plain).toIO' with
              | .ok ((), s') => pure !s'.messages.hasErrors
              | .error _ => pure false
            if ok then
              if let (some a, some b) := (cmd.getPos?, inner.getPos?) then
                res := { res with edits := res.edits.push {
                  rule := "unneededOption", message := s!"`set_option {o}` is not needed here"
                  range := ictx.fileMap.utf8RangeToLspRange ⟨a, b⟩, newText := "" } }
        if seals then
          if let some (kw, inner) := sealed? cmd then
            -- A seal keeps definitional checks from unfolding a definition, so dropping it must
            -- not make elaboration slower.
            if let (some (a, sa), some (b, sb)) := (← cost cmd ctx before, ← cost inner ctx before) then
              if b ≤ a && sameDecls before.env sa.env sb.env then
                if let (some p, some q) := (cmd.getPos?, inner.getPos?) then
                  res := { res with edits := res.edits.push {
                    rule := "unneededSeal", message := s!"`{kw}` is not needed here: {a / 1000} → {b / 1000} heartbeats"
                    range := ictx.fileMap.utf8RangeToLspRange ⟨commentAbove input ictx.fileMap p, q⟩, newText := "" } }
        -- Edits that were each checked alone must also work together. An edit checked only by
        -- replaying its step is also checked in the command: the info tree can record a nested
        -- `by` block in a state the elaborator does not reach, as in a `calc` step.
        -- Renaming touches every use of a name, so it waits until nothing else changes the command.
        if res.edits.size == mark && golf.contains "shortNames" then
          for e in ← Golf.checkedNames input ictx.fileMap cmd pctx ctx before after after.infoState.trees.toArray do
            res := { res with edits := res.edits.push {
              rule := e.rule, message := e.message,
              range := ictx.fileMap.utf8RangeToLspRange e.range, newText := e.newText } }
        -- `--compress` takes steps out of proofs; a rewrite that does not is left out.
        let fresh := (res.edits.extract mark res.edits.size).map fun e =>
          let d := Steps.removed input cmd pctx (ictx.fileMap.lspRangeToUtf8Range e.range) e.newText
          { e with gain := d.toNat }
        let fresh := fresh.filter fun e =>
          !stepGated.contains e.rule || fewerSteps input ictx.fileMap cmd pctx fileName e
        res := { res with edits := res.edits.extract 0 mark ++ fresh }
        let mine := res.edits.extract mark res.edits.size
        if mine.size > 1 || mine.any (replayed.contains ·.rule) then
          let kept ← Combine.check input ictx.fileMap cmd pctx ctx before after (shorter := shorter) (trials := 15)
            (mine.map fun e => { range := ictx.fileMap.lspRangeToUtf8Range e.range, newText := e.newText,
                                 dropsInstances := e.rule == "unusedInstance", gain := e.gain })
          res := { res with edits := res.edits.extract 0 mark ++ kept.map (mine[·]!) }
      s := { after with infoState := { enabled := needInfo } }
  -- Helpers fold into their users once the whole module is elaborated. When a group fails, each
  -- of its helpers is tried alone, largest first; the next round can fold the rest.
  if fold then
    let debug := (← IO.getEnv "LEANPERF_GOLF_DEBUG").isSome
    for (a, b, keep, free) in Fold.groups records (Std.HashSet.ofArray external) do
      if free.isEmpty then continue
      let (some first, some last) := (records[a]?, records[b]?) | continue
      let size (n : Name) : Nat := (records.findSome? fun r =>
        match Signature.asTheorem? r.cmd with
        | some t => if Signature.theoremName? t[1] r.before r.after == some n then
            r.cmd.getRange?.map fun rg => rg.stop.byteIdx - rg.start.byteIdx else none
        | none => none).getD 0
      let tries := #[free] ++ (if free.size > 1 then (free.qsort (size · > size ·)).map (#[·]) else #[])
      for fs in tries do
        -- The span starts at the first helper folded; the helpers left out stay theorems.
        let some a' := (List.range (b - a)).map (a + ·) |>.find? fun k => (records[k]?.bind fun r =>
          (Signature.asTheorem? r.cmd).bind fun t => Signature.theoremName? t[1] r.before r.after).any fs.contains
          | continue
        let keep' := keep ++ free.filter (!fs.contains ·)
        let t ← match Fold.fold input ictx.fileMap records a' b fs with
          | .ok t => pure t
          | .error why =>
            if debug then IO.eprintln s!"fold {fs.toList} into {keep.toList}: {why}"
            continue
        let some rg := Propose.span input records a' b | continue
        let some first' := records[a']? | continue
        let budget := 2 * ((records.extract a' (b + 1)).foldl (· + ·.heartbeats) 0) + 2000000
        let _ := first
        match ← Propose.verify t first'.ctx first'.before last.after keep' (docs := true) (budget := some budget) with
        | none =>
          res := { res with edits := res.edits.push {
            rule := "foldHelper", newText := t, range := ictx.fileMap.utf8RangeToLspRange rg
            gain := 1000 * fs.size
            message := s!"Fold {", ".intercalate (fs.toList.map fun n => s!"`{n}`")} into the theorem that uses it" } }
          break
        | some errs =>
          if debug then IO.eprintln s!"fold {fs.toList} rejected: {errs.toList.take 2}"
  -- A theorem that only applies another moves that one's proof into itself, and takes its place.
  if fold then
    let debug := (← IO.getEnv "LEANPERF_GOLF_DEBUG").isSome
    for (t, w, last, keep) in Fold.wrappers input records (Std.HashSet.ofArray external) do
      let (some first, some lastR) := (records[t]?, records[last]?) | continue
      let txt ← match Fold.mergeWrapper input records t w last with
        | .ok x => pure x
        | .error why =>
          if debug then IO.eprintln s!"merge wrapper {t} {w}: {why}"
          continue
      let some rg := Propose.span input records t last | continue
      let budget := 2 * ((records.extract t (last + 1)).foldl (· + ·.heartbeats) 0) + 2000000
      match ← Propose.verify txt first.ctx first.before lastR.after keep (docs := true) (budget := some budget) with
      | none =>
        res := { res with edits := res.edits.push {
          rule := "foldHelper", newText := txt, range := ictx.fileMap.utf8RangeToLspRange rg
          gain := 1000
          message := s!"Move the proof of `{(Fold.nameAt records t).getD .anonymous}` into `{(Fold.nameAt records w).getD .anonymous}`, which only applies it" } }
      | some errs =>
        if debug then IO.eprintln s!"merge wrapper {t} {w} rejected: {errs.toList.take 2}"
  -- A proposer rewrites groups of commands, which it sees only once the module is elaborated.
  if let some p := proposer then
    let groups := Propose.groups input records (Std.HashSet.ofArray external)
    -- Proposers are slow and the groups independent: first rounds run a few at a time.
    let jobs := ((← IO.getEnv "LEANPERF_PROPOSE_JOBS").bind (·.toNat?)).getD 4
    let mut firsts : Array (Option (Array String)) := #[]
    for batch in (List.range ((groups.size + jobs - 1) / max jobs 1)).map (fun i => groups.extract (i * jobs) ((i + 1) * jobs)) do
      let tasks ← batch.mapM fun (a, b, keep, free) => do
        let some req ← Propose.firstRequest input records a b keep free | pure none
        pure (some (← IO.asTask (Propose.ask p req)))
      for t in tasks do
        firsts := firsts.push (← t.mapM fun t => IO.ofExcept t.get)
    for ((a, b, keep, free), first?) in groups.zip firsts do
      if first?.isNone then continue
      if let some (rg, t, n) ← Propose.rewrite? input records a b keep free p (first? := first?) then
        let dropped := if free.isEmpty then "" else s!", with {free.size} helper lemma{if free.size == 1 then "" else "s"} it may fold in"
        res := { res with edits := res.edits.push {
          rule := "rewrite", newText := t, range := ictx.fileMap.utf8RangeToLspRange rg
          message := s!"Lean accepts the proposer's rewrite after {n} round{if n == 1 then "" else "s"}{dropped}" } }
  return res

/-- Apply non-overlapping edits, later ones first. Returns the new text and how many applied. -/
def applyEdits (text : String) (edits : Array Edit) : String × Nat := Id.run do
  let map := FileMap.ofString text
  let rs := edits.map fun e => (map.lspRangeToUtf8Range e.range, e.newText)
  let rs := rs.qsort fun a b => a.1.start.byteIdx > b.1.start.byteIdx
  let mut out := text
  let mut limit := text.rawEndPos
  let mut n := 0
  for (r, t) in rs do
    if r.stop.byteIdx > limit.byteIdx then continue
    out := String.Pos.Raw.extract out 0 r.start ++ t ++ String.Pos.Raw.extract out r.stop out.rawEndPos
    limit := r.start
    n := n + 1
  return (out, n)

end LeanPerf.Tactics
