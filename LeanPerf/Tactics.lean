import LeanPerf.ProofCompression
import LeanPerf.Prune
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

structure Edit where
  rule : String
  message : String
  range : Lsp.Range
  newText : String
  deriving ToJson, FromJson, Inhabited

/-- The leading identifier-like token of a tactic, e.g. `simp_all` or `nlinarith`. -/
def head (text : String) : String :=
  (text.takeWhile fun c => c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!').toString

/-- Text after the head token. -/
def rest (text : String) : String := (text.drop (head text).length).toString

/-- Candidate replacements. A candidate ending in a `?`-variant is a request for a suggestion,
    which is then tried in its place. -/
def candidates (text : String) : Array String :=
  let h := head text
  let r := rest text
  let only := (r.trimAsciiStart.toString.startsWith "only")
  match h with
  | "nlinarith" => #["linarith" ++ r] ++ (if r.trimAscii.isEmpty then #["positivity"] else #[])
  | "linarith" => if r.trimAscii.isEmpty || r.trimAsciiStart.startsWith "[" then #["assumption"] else #[]
  | "norm_num" => if only then #[] else #["simp" ++ r]
  | "simp" | "simp_all" | "simpa" => if only then #[] else #[h ++ "?" ++ r]
  | _ => #[]

/-- The overrides worth trying to remove. -/
def overridable : List Name :=
  [`maxHeartbeats, `synthInstance.maxHeartbeats, `maxRecDepth, `synthInstance.maxSize,
   `backward.isDefEq.lazyWhnfCore, `backward.isDefEq.lazyProjDelta]

/-- A goal as a closed term, so that goals from different runs compare structurally, together with
    its hypothesis names. -/
def goalKey (g : MVarId) : MetaM (Option (Expr × List Name)) := g.withContext do
  let mut fvars := #[]
  let mut names := []
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      fvars := fvars.push d.toExpr
      names := d.userName :: names
  let e ← instantiateMVars (← mkForallFVars fvars (← g.getType))
  if e.hasMVar || e.hasFVar then return none
  return some (e, names)

/-- Strip `Try this:` and an optional `[apply]` marker from a suggestion message. -/
def suggestion? (msg : String) : Option String := do
  let i ← (msg.splitOn "Try this:")[1]?
  let s := i.trimAscii.toString
  let s := ((s.dropPrefix? "[apply]").map (·.toString)).getD s
  let s := s.trimAscii.toString
  if s.isEmpty then none else some s

structure Run where
  heartbeats : Nat
  goals : List (Expr × List Name)
  suggestions : Array String

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
def runOn (ci : ContextInfo) (mctx : MetavarContext) (goal : MVarId) (text : String)
    (budget : Nat) (minePremises := false) : IO (Option Run) := do
  let some decl := mctx.findDecl? goal | return none
  let .ok stx := Parser.runParserCategory ci.env `tactic text "<leanperf>" | return none
  ci.runMetaM decl.lctx do
    setMCtx mctx
    let h0 ← IO.getNumHeartbeats
    let attempt : MetaM (Option Run) := do
      let gs ← Term.TermElabM.run' <| Term.withoutErrToSorry <|
        Tactic.run goal (Tactic.evalTactic stx)
      let used := (← IO.getNumHeartbeats) - h0
      let msgs := (← Core.getMessageLog).toList
      if msgs.any (·.severity == .error) then return none
      let proof ← instantiateMVars (mkMVar goal)
      if proof.hasSorry then return none
      let mut keys := []
      for g in gs do
        let some k ← goalKey g | return none
        keys := k :: keys
      let mut sugg ← if minePremises && gs.isEmpty then arithmeticSuggestions text stx proof else pure #[]
      if minePremises && gs.isEmpty && ["linarith", "nlinarith"].contains (head text) then
        let paths ← Relations.candidates (← instantiateMVars (← goal.getType))
        sugg := sugg ++ paths.map ("exact " ++ ·)
      for m in msgs do
        if let some s := suggestion? (← m.data.toString) then sugg := sugg.push s
      return some { heartbeats := used, goals := keys.reverse, suggestions := sugg }
    tryCatchRuntimeEx
      (withTheReader Core.Context ({ · with maxHeartbeats := budget, initHeartbeats := h0 }) attempt)
      fun _ => return none

/-- One syntactic occurrence and every goal it ran on. -/
structure Site where
  range : Lean.Syntax.Range
  text : String
  runs : Array (ContextInfo × MetavarContext × MVarId)

private def sites (input : String) (tree : InfoTree) : Array Site := Id.run do
  let found := tree.foldInfo (init := #[]) fun ci i acc => match i with
    | .ofTacticInfo ti =>
      match ti.stx.getRange? (canonicalOnly := true), ti.goalsBefore with
      | some r, g :: _ => acc.push (r, ci, ti.mctxBefore, g)
      | _, _ => acc
    | _ => acc
  let mut out : Array Site := #[]
  for (r, ci, mctx, g) in found do
    let text := String.Pos.Raw.extract input r.start r.stop
    if (candidates text).isEmpty then continue
    match out.findIdx? (·.range == r) with
    | some k =>
      -- Macro expansions record the same occurrence more than once.
      let dup := match out[k]? with | some s => s.runs.any (·.2.2 == g) | none => true
      unless dup do
        out := out.modify k fun s => { s with runs := s.runs.push (ci, mctx, g) }
    | none => out := out.push { range := r, text, runs := #[(ci, mctx, g)] }
  return out

/-- Total cost of `text` over all goals of the site, and whether it matches `reference` goals. -/
private def trySite (s : Site) (text : String) (budget : Nat)
    (reference : Option (Array (List (Expr × List Name)))) :
    IO (Option (Nat × Array (List (Expr × List Name)) × Array String)) := do
  let mut total := 0
  let mut goals := #[]
  let mut sugg := #[]
  for h : k in [:s.runs.size] do
    let (ci, mctx, g) := s.runs[k]
    if budget > 0 && total ≥ budget then return none
    let some r ← runOn ci mctx g text (if budget == 0 then 0 else budget - total) reference.isNone
      | return none
    if let some ref := reference then
      unless ref[k]? == some r.goals do return none
    total := total + r.heartbeats
    goals := goals.push r.goals
    sugg := sugg ++ r.suggestions
  return some (total, goals, sugg)

def tacticEdits (input : String) (map : FileMap) (tree : InfoTree) (minSaving : Nat) (shorter : Bool) :
    IO (Array Edit) := do
  let mut edits := #[]
  for s in sites input tree do
    if s.text.contains "/-" || s.text.contains "--" then continue
    let some (base, ref, hints) ← trySite s s.text 0 none | continue
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
      let some (cost, _, sugg) ← trySite s c limit (some ref)
        | continue
      if isQuery then
        queue := queue ++ sugg.filter (· != s.text)
      else if cost < base && cost + minSaving ≤ base && best.all (cost < ·.2) then
        best := some (c, cost)
    if let some (c, cost) := best then
      edits := edits.push {
        rule := "fasterTactic"
        message := s!"{s.text.take 60} → {c.take 60}: {base / 1000} → {cost / 1000} heartbeats"
        range := map.utf8RangeToLspRange s.range, newText := c }
  return edits

/-- `set_option o v in cmd` for an overridable `o`: the option and the inner command. -/
def override? (cmd : Syntax) : Option (Name × Syntax) :=
  if cmd.isOfKind ``Parser.Command.in && cmd[0].isOfKind ``Parser.Command.set_option then
    let o := cmd[0][1].getId
    if overridable.contains o then some (o, cmd[2]) else none
  else none

structure Result where
  edits : Array Edit := #[]
  errors : Array String := #[]
  deriving Inhabited

/-- Elaborate `input` on top of `env` (its imports), collecting edits. -/
def analyze (env : Environment) (main : Name) (fileName input : String) (opts : Options)
    (minSaving : Nat := 1000) (tactics options : Bool := true) (shorter := false)
    (compression : Option ProofCompression.Index := none) : IO Result := do
  let ictx := Parser.mkInputContext input fileName
  let (_, ps0, _) ← Parser.parseHeader ictx
  let mut s := Command.mkState (env.setMainModule main) {} opts
  let mut ps := ps0
  let mut res : Result := {}
  let mut localProofs : ProofCompression.Index := {}
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
    let ctx : Command.Context :=
      { fileName, fileMap := ictx.fileMap, cmdPos := pos, snap? := none, cancelTk? := none }
    let before := { s with messages := {}, infoState := { enabled := tactics } }
    match ← ((Command.elabCommandTopLevel cmd).run ctx |>.run before).toIO' with
    | .error e =>
      res := { res with errors := res.errors.push (← e.toMessageData.toString) }
    | .ok ((), after) =>
      if after.messages.hasErrors then
        for m in after.messages.toList do
          if m.severity == .error && res.errors.size < 5 then
            res := { res with errors := res.errors.push s!"{m.pos.line}:{m.pos.column + 1}: {← m.data.toString}" }
      else
        if compression.isSome then
          if let some e ← Signature.compress input ictx.fileMap cmd ctx before after then
            res := { res with edits := res.edits.push {
              rule := "shorterSignature", message := "Shorten the theorem statement",
              range := e.range, newText := e.newText } }
          if let some e ← Prune.proof? input ictx.fileMap cmd pctx ctx before after then
            res := { res with edits := res.edits.push {
              rule := "unusedHave", message := "Remove unused local proofs",
              range := e.range, newText := e.newText } }
        if tactics then
          let mut names : NameSet := {}
          for t in after.infoState.trees do
            res := { res with edits := res.edits ++ (← tacticEdits input ictx.fileMap t minSaving shorter) }
            if let some imports := compression then
              let (edits, decls) ← ProofCompression.scan input ictx.fileMap t imports localProofs
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
      s := { after with infoState := { enabled := tactics } }
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
