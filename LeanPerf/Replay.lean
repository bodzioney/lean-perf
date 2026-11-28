import Lean

/-!
# Replaying a tactic on a recorded goal

Every checked tactic rewrite works the same way: run the original tactic and a candidate on the
goal where the original ran, in the metavariable context recorded by the info tree, and compare
what each leaves behind. Remaining goals are compared as closed terms together with their
hypothesis names, so the rest of the proof sees the same state after either one.
-/

open Lean Elab Meta

namespace LeanPerf.Replay

/-- A goal as a closed term, so that goals from different runs compare structurally, together with
    its hypothesis names. Metadata around the target is ignored. -/
def goalKey (g : MVarId) : MetaM (Option (Expr × List Name)) := g.withContext do
  let mut fvars := #[]
  let mut names := []
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      fvars := fvars.push d.toExpr
      names := d.userName :: names
  -- Elaborating a `by` block marks its goal `noImplicitLambda`; `show` and `change` drop the mark.
  let target := (← instantiateMVars (← g.getType)).consumeMData
  let e ← instantiateMVars (← mkForallFVars fvars target)
  if e.hasMVar || e.hasFVar then return none
  return some (e, names)

/-- Syntax parsed from a candidate's own text has offsets into that text. Messages about it are
    rendered against the source file, so every node is placed at the site it would replace. -/
partial def relocate (r : Syntax.Range) : Syntax → Syntax
  | .node _ k args => .node (.synthetic r.start r.stop) k (args.map (relocate r))
  | .atom _ v => .atom (.synthetic r.start r.stop) v
  | .ident _ raw n pre => .ident (.synthetic r.start r.stop) raw n pre
  | .missing => .missing

/-- A constant that elaboration generates, such as `inst._proof_11`. Its number depends on what
    was elaborated before it, so source text must not name it. -/
def generated (n : Name) : Bool := (privateToUserName n).isInternalDetail

/-- Strip `Try this:` and an optional `[apply]` marker from a suggestion message. -/
def suggestion? (msg : String) : Option String := do
  let i ← (msg.splitOn "Try this:")[1]?
  let s := i.trimAscii.toString
  let s := ((s.dropPrefix? "[apply]").map (·.toString)).getD s
  let s := s.trimAscii.toString
  if s.isEmpty then none else some s

/-- The info tree with every command context in `env`. A context records the environment at the end
    of its command, which already holds the declaration being proved and its attributes: replayed in
    it, `simp` could close the goal of a `@[simp]` lemma with that lemma. -/
partial def withEnv (env : Environment) : InfoTree → InfoTree
  | .context (.commandCtx ci) t => .context (.commandCtx { ci with env }) (withEnv env t)
  | .context i t => .context i (withEnv env t)
  | .node i cs => .node i (cs.map (withEnv env))
  | t => t

/-- `ContextInfo.runMetaM` with the source file's `FileMap`. The info tree's context has an empty
    one, and rendering a hint at a position in the file would read past its end. -/
def inFile (map : FileMap) (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : IO α :=
  ci.runMetaM lctx (withTheReader Core.Context (fun c => { c with fileMap := map }) x)

/-- A budget for replaying steps that Lean elaborated in the file: twice the heartbeats that the
    declaration was allowed (`maxHeartbeats`, or its default when that is unlimited), in raw
    heartbeats. The original proof ran within it, and a replay that takes a slower path than the
    original elaboration would otherwise run without end. -/
def cap (ci : ContextInfo) : Nat :=
  let h := maxHeartbeats.get ci.options
  2 * 1000 * (if h == 0 then maxHeartbeats.defValue else h)

structure Run where
  heartbeats : Nat
  goals : List (Expr × List Name)
  suggestions : Array String

/-- Run tactic syntax `stx` on `goal`. `budget` is in raw heartbeats, and `0` means unlimited.
    The result is `none` on an error, a `sorry`, a remaining goal that is not closed, or when
    the budget runs out. `extra` adds suggestions from the goal, its proof and the new goals. -/
def run (ci : ContextInfo) (map : FileMap) (mctx : MetavarContext) (goal : MVarId) (stx : Syntax) (budget : Nat)
    (extra : MVarId → Expr → List MVarId → MetaM (Array String) := fun _ _ _ => pure #[]) :
    IO (Option Run) := do
  let some decl := mctx.findDecl? goal | return none
  inFile map ci decl.lctx do
    setMCtx mctx
    let h0 ← IO.getNumHeartbeats
    let attempt : MetaM (Option Run) := do
      -- A tactic block inside a term, as in `obtain rfl := f (by simp)`, can be postponed past the
      -- step. The enclosing proof runs it before it ends, and so does a replay.
      let gs ← Term.TermElabM.run' <| Term.withoutErrToSorry do
        let gs ← Tactic.run goal (Tactic.evalTactic stx)
        Term.synthesizeSyntheticMVarsNoPostponing
        return gs
      let used := (← IO.getNumHeartbeats) - h0
      let msgs := (← Core.getMessageLog).toList
      if msgs.any (·.severity == .error) then return none
      let proof ← instantiateMVars (mkMVar goal)
      if proof.hasSorry then return none
      -- Every hole left in the proof must be one of the goals the step reports.
      unless (← getMVarsNoDelayed proof).all gs.contains do return none
      let mut keys := []
      for g in gs do
        let some k ← goalKey g | return none
        keys := k :: keys
      let mut sugg ← extra goal proof gs
      for m in msgs do
        if let some s := suggestion? (← m.data.toString) then sugg := sugg.push s
      return some { heartbeats := used, goals := keys.reverse, suggestions := sugg }
    tryCatchRuntimeEx
      (withTheReader Core.Context ({ · with maxHeartbeats := budget, initHeartbeats := h0 }) attempt)
      fun _ => return none

end LeanPerf.Replay
