import LeanPerf.Replay
import LeanPerf.Signature
import Lean.Meta.Tactic.SolveByElim

open Lean Elab Meta

namespace LeanPerf.Reprove

/-- Search for a short derivation using the hypotheses at the start of the proof and a
    bounded set of facts from its elaborated body. Instantiate polymorphic lemmas afresh
    at each use, so a chain can use the same lemma at different types or indices. -/
private def search (goal original : Expr) : MetaM (Option String) := do
  let env ← getEnv
  let mut facts := #[]
  for name in original.getUsedConstants do
    let some decl := env.find? name | continue
    if name.isInternalDetail || name.hasMacroScopes || name == ``sorryAx then continue
    if ← isProp decl.type then
      facts := facts.push name
      if facts.size == 16 then break
  let lemmas : List (TermElabM Expr) := facts.toList.map fun name => liftM (mkConstWithFreshMVarLevels name)
  let locals _ := do return (← getLocalHyps).toList
  -- Iterative deepening gives a short application chain priority over a long detour.
  for depth in [1:6] do
    if let some text ← observing? do
      let g ← mkFreshExprSyntheticOpaqueMVar goal
      let remaining ← SolveByElim.solveByElim { maxDepth := depth, exfalso := false, symm := false }
        lemmas locals [g.mvarId!]
      guard remaining.isEmpty
      let proof ← instantiateMVars g
      guard (!proof.hasMVar && !proof.hasSorry && !proof.getUsedConstants.any Replay.generated)
      let text := (← withOptions (fun o => o.setBool `pp.proofs true) (ppExpr proof)).pretty 200
      guard (!text.contains '\n')
      return text
    then return some text
  return none

/-- Find the tactic goal for the entire written proof. Nested tactics can have extra locals
    which are unavailable at the replacement site. -/
private def replacement (trees : PersistentArray InfoTree) (r : Syntax.Range) : IO (Option String) := do
  for tree in trees do
    let site := tree.foldInfo (init := none) fun ci info acc => Id.run do
      let .ofTacticInfo ti := info | return acc
      unless ti.stx.isOfKind ``Parser.Term.byTactic && ti.stx.getRange? (canonicalOnly := true) == some r do return acc
      let [g] := ti.goalsBefore | return acc
      return some (ci, ti, g)
    if let some (ci, ti, g) := site then
      let some decl := ti.mctxBefore.findDecl? g | continue
      return ← ci.runMetaM decl.lctx do
        tryCatchRuntimeEx (withCurrHeartbeats <| withTheReader Core.Context
          ({ · with maxHeartbeats := 1000000 }) do
            setMCtx ti.mctxAfter
            let original ← instantiateMVars (mkMVar g)
            if original.hasMVar || original.hasSorry then return none
            setMCtx ti.mctxBefore
            g.withContext do
              let goal ← instantiateMVars (← g.getType)
              if goal.hasMVar then return none
              search goal original) fun _ => return none
  return none

/-- Try an alternative argument for a whole theorem. Audit the *written* replacement in
    the original command scope, including dependencies introduced by implicit arguments. -/
def proof? (input : String) (map : FileMap) (cmd : Syntax) (ctx : Command.Context)
    (before after : Command.State) : IO (Option Lsp.TextEdit) := do
  let some cmd := Signature.asTheorem? cmd | return none
  let d := cmd[1]
  unless d[3].isOfKind ``Parser.Command.declValSimple do return none
  let body := d[3][1]
  unless body.isOfKind ``Parser.Term.byTactic do return none
  let some r := body.getRange? | return none
  let source := String.Pos.Raw.extract input r.start r.stop
  if source.utf8ByteSize < 32 || source.contains "--" || source.contains "/-" then return none
  let some name := Signature.theoremName? d before after | return none
  let some (.thmInfo old) := after.env.find? name | return none
  let some text ← replacement after.infoState.trees r | return none
  if text.utf8ByteSize ≥ source.utf8ByteSize then return none
  let .ok parsed := Parser.runParserCategory before.env `term text | return none
  let parsed := Replay.relocate r parsed
  let candidate := cmd.setArg 1 (d.setArg 3 (d[3].setArg 1 parsed))
  let probe := { before with messages := {}, infoState := { enabled := false } }
  let .ok ((), checked) ← ((Command.elabCommandTopLevel candidate).run ctx |>.run probe).toIO' | return none
  if checked.messages.hasErrors then return none
  let some (.thmInfo new) := checked.env.find? name | return none
  unless old.type.equal new.type && old.levelParams == new.levelParams && !new.value.hasSorry do return none
  let axioms (env : Environment) := (collectAxioms (m := CoreM) name).toIO'
    { fileName := ctx.fileName, fileMap := map } { env }
  let used ← axioms checked.env
  let allowed ← axioms after.env
  if used.contains ``sorryAx || !used.all allowed.contains then return none
  return some { range := map.utf8RangeToLspRange r, newText := text }

end LeanPerf.Reprove
