import LeanPerf.Prune

/-!
# Instance arguments a theorem does not use

Contributors to the Riemann development deleted hundreds of instance binders such as
`[S.IsAdmissible]` from theorem statements. Instance arguments are synthesized at every use, so
deleting one never changes a caller, except an `@`-application that passes arguments by position.

Deleting a binder that the statement mentions would change it: a `[DecidablePred p]` binder in a
statement about `Finset.filter p s`, for example, would be replaced by whatever instance the
context provides. So a deletion is accepted only when the new exported type is the old one without
instance binders that nothing after them mentions, and the proof still elaborates.
-/

open Lean Elab Meta

namespace LeanPerf.Instances

/-- Whether the theorem has an instance binder that neither the rest of its type nor its proof
    mentions. Only such a theorem is worth elaborating again. -/
partial def hasUnusedInstance (type value : Expr) : Bool :=
  match type.consumeMData, value.consumeMData with
  | .forallE _ _ b bi, .lam _ _ v _ =>
    (bi.isInstImplicit && !b.hasLooseBVar 0 && !v.hasLooseBVar 0) || hasUnusedInstance b v
  | _, _ => false

/-- Whether `new` is `old` without some instance binders that nothing after them mentions. Anonymous
    instance binders are named hygienically, so names are compared without macro scopes. -/
partial def dropsInstances (old new : Expr) : MetaM Bool := do
  let .forallE n t b bi := old.consumeMData | return old == new
  if let .forallE n' t' b' bi' := new.consumeMData then
    if n.eraseMacroScopes == n'.eraseMacroScopes && bi == bi' && t == t' then
      return ← withLocalDecl n bi t fun x => dropsInstances (b.instantiate1 x) (b'.instantiate1 x)
  return bi.isInstImplicit && !b.hasLooseBVars && (← dropsInstances b new)

private def accept : Prune.Accept := fun env old new => do
  if old.levelParams != new.levelParams || old.type.equal new.type then return false
  let check := (dropsInstances old.type new.type).run' {} {}
  try check.toIO' { fileName := "<leanperf>", fileMap := default, maxHeartbeats := 0 } { env }
  catch _ => return false

/-- The source to delete for a binder: the binder and the spaces before it, or its whole line
    when nothing else is on it. -/
private def span (input : String) (map : FileMap) (r : Syntax.Range) : Syntax.Range := Id.run do
  if let some whole := Prune.wholeLines? input map r then return whole
  let mut start := r.start
  while start.byteIdx > 0 && ((start.prev input).get input == ' ') do start := start.prev input
  if start == r.start || (start.prev input).get input == '\n' then
    -- At the start of a line, the spaces after it go instead.
    let mut stop := r.stop
    while stop < input.rawEndPos && stop.get input == ' ' do stop := stop.next input
    return ⟨r.start, stop⟩
  return ⟨start, r.stop⟩

/-- Delete the anonymous instance binders of a theorem's signature that it does not need.
    `cited` holds the names some module applies with `@`; such a theorem keeps its arguments. -/
def edits (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (ctx : Command.Context) (before after : Command.State) (cited : Name → Bool) :
    IO (Array Syntax.Range) := do
  let some thm := Signature.asTheorem? cmd | return #[]
  -- Attributes such as `to_additive` derive declarations that would change too.
  unless thm[0][1].getNumArgs == 0 do return #[]
  let d := thm[1]
  let some name := Signature.theoremName? d before after | return #[]
  if cited name then return #[]
  let some (.thmInfo val) := after.env.find? name | return #[]
  unless hasUnusedInstance val.type val.value do return #[]
  let candidates := d[2][0].getArgs.filterMap fun b => do
    guard (b.isOfKind ``Parser.Term.instBinder && b[1].getNumArgs == 0)
    let r ← b.getRange? (canonicalOnly := true)
    let text := String.Pos.Raw.extract input r.start r.stop
    guard (!text.contains "--" && !text.contains "/-")
    return span input map r
  Prune.deletions input map cmd pctx ctx before after candidates (accept := accept)

end LeanPerf.Instances
