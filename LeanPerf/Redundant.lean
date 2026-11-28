import LeanPerf.Prune
import LeanPerf.Replay

/-!
# Redundant proof steps

Contributors to the Riemann development removed three kinds of step by hand, hundreds of times:

* `restatedType` drops the type of `have h : T := e` or `obtain pat : T := e` when Lean infers
  the same type from `e`,
* `redundantShow` deletes a `show T` line when the goal already has the form `T`, and
* `unneededClassical` deletes a `classical` line when the proof needs no classical instance.

Each candidate runs on every goal where the step ran, in the recorded metavariable context. It must
leave the same goals, with the same hypothesis names, and types that agree up to unfolding
instances: an inferred type often reaches a coercion through another path of instances than the
written one. The rest of the proof might notice such a difference, and a replay can differ from
elaboration, so the caller then elaborates the declaration with its edits to confirm them.
-/

open Lean Elab Meta

namespace LeanPerf.Redundant

structure Edit where
  rule : String
  message : String
  range : Syntax.Range
  newText : String

private structure Site where
  rule : String
  message : String
  original : Syntax
  /-- Candidate steps with the edits that produce them, tried in order. -/
  options : Array (Syntax × Syntax.Range × String)
  key : Syntax.Range
  /-- The step can act on goals other than the main one, so it is checked only alone. -/
  single : Bool := false

private def uncommented (input : String) (r : Syntax.Range) : Bool :=
  let t := String.Pos.Raw.extract input r.start r.stop
  !t.contains "--" && !t.contains "/-"

/-- The range of ` : T`, from the spaces before the colon of `spec` to the end of the type. A
    value written as a tactic block needs its type as the goal, so it is never a candidate. -/
private def ascription? (input : String) (spec value : Syntax) : Option Syntax.Range := do
  guard (!value.isOfKind ``Parser.Term.byTactic)
  let colon ← spec.getPos? (canonicalOnly := true)
  let stop ← spec.getTailPos? (canonicalOnly := true)
  let mut start := colon
  while start.byteIdx > 0 && ((start.prev input).get input == ' ') do start := start.prev input
  let r : Syntax.Range := ⟨start, stop⟩
  guard (start < stop && uncommented input r)
  return r

private def site? (input : String) (map : FileMap) (stx : Syntax) : Option Site := do
  let key ← stx.getRange? (canonicalOnly := true)
  -- `have h : T := e`: `tacticHave__` is `"have" letConfig letDecl`.
  if stx.getNumArgs == 3 && stx[0].getAtomVal == "have" && stx[2].isOfKind ``Parser.Term.letDecl then
    let decl := stx[2][0]
    guard (decl.isOfKind ``Parser.Term.letIdDecl && decl[1].getNumArgs == 0 && decl[2].getNumArgs == 1)
    let edit ← ascription? input decl[2] decl[4]
    return { rule := "restatedType", message := "Lean infers the same type for this `have`", original := stx,
             options := #[(stx.setArg 2 (stx[2].setArg 0 (decl.setArg 2 mkNullNode)), edit, "")], key }
  -- `obtain pat : T := e` is `"obtain" pat? (" : " T)? (" := " e,+)?`.
  if stx.isOfKind ``Parser.Tactic.obtain then
    guard (stx[2].getNumArgs == 2 && stx[3].getNumArgs == 2)
    let [value] := stx[3][1].getSepArgs.toList | none
    let edit ← ascription? input stx[2] value
    return { rule := "restatedType", message := "Lean infers the same type for this `obtain`", original := stx,
             options := #[(stx.setArg 2 mkNullNode, edit, "")], key }
  -- `show` can select a later goal, so it is a candidate only where it sees one goal.
  if stx.isOfKind ``Parser.Tactic.«show» then
    let edit ← Prune.wholeLines? input map key
    return { rule := "redundantShow", message := "The goal already has this form", original := stx,
             options := #[(mkNode ``Parser.Tactic.skip #[mkAtom "skip"], edit, "")], key, single := true }
  -- `classical tacs`: the block must start in the column of `classical`, so that deleting the
  -- line leaves it in the enclosing block.
  if stx.isOfKind ``Parser.Tactic.classical then
    let kw ← stx[0].getRange? (canonicalOnly := true)
    let edit ← Prune.wholeLines? input map kw
    let first ← stx[1].getPos? (canonicalOnly := true)
    guard ((map.toPosition first).column == (map.toPosition kw.start).column)
    return { rule := "unneededClassical", message := "The proof needs no classical instance", original := stx,
             options := #[(stx[1], edit, "")], key, single := true }
  -- `simp [-f]`: the unused-argument linter checks lemmas but not erasures. `simp`, `simp_all`
  -- and `dsimp` keep their arguments at the same position.
  if stx.isOfKind ``Parser.Tactic.simp || stx.isOfKind ``Parser.Tactic.simpAll ||
      stx.isOfKind ``Parser.Tactic.dsimp then
    guard (stx[4].getNumArgs == 3)
    let params := stx[4][1].getSepArgs
    let erased := (Array.range params.size).filter (params[·]!.isOfKind ``Parser.Tactic.simpErase)
    guard (!erased.isEmpty)
    let bracket ← stx[4].getRange? (canonicalOnly := true)
    guard (uncommented input bracket)
    let option (drop : Array Nat) : Option (Syntax × Syntax.Range × String) := do
      let kept := (Array.range params.size).filter (!drop.contains ·)
      let cand := (Elab.Tactic.setSimpParams ⟨stx⟩ (kept.map (params[·]!))).raw
      if kept.isEmpty then
        let mut start := bracket.start
        while start.byteIdx > 0 && ((start.prev input).get input == ' ') do start := start.prev input
        return (cand, ⟨start, bracket.stop⟩, "")
      -- Each kept argument keeps the separator that followed it.
      let mut text := "["
      for h : j in [:kept.size] do
        let r ← params[kept[j]]!.getRange? (canonicalOnly := true)
        text := text ++ String.Pos.Raw.extract input r.start r.stop
        if j + 1 < kept.size then
          let next ← params[kept[j] + 1]!.getPos? (canonicalOnly := true)
          text := text ++ String.Pos.Raw.extract input r.stop next
      return (cand, bracket, text ++ "]")
    let options := (#[erased] ++ (if erased.size > 1 then erased.map (#[·]) else #[])).filterMap option
    return { rule := "unneededErasure", message := "The simplifier needs no erased lemma here",
             original := stx, options, key }
  none


/-- Replace the node of `target`'s kind at `target`'s position. -/
private partial def replaceNode (target new : Syntax) : Syntax → Syntax
  | s@(.node info k args) =>
    if k == target.getKind && s.getRange? (canonicalOnly := true) == target.getRange? (canonicalOnly := true) then new
    else .node info k (args.map (replaceNode target new))
  | s => s

/-- An annotation in a step: `(e : T)`, a typed `fun` binder, or a `fun` with a type. -/
private structure Annotation where
  stx : Syntax
  /-- A binder records no expected type, so only the replay decides. -/
  binder : Bool
  /-- `e` can stand without the parentheses of `(e : T)`, as an argument of `exact` or `⟨…⟩`. -/
  bare : Bool

/-- The annotations of a step, without those of the steps nested in it, which have sites of their
    own. -/
private partial def annotations (tactics : Parser.SyntaxNodeKindSet) (stx : Syntax) : Array Annotation :=
  stx.getArgs.foldl (fun acc a => go stx a acc) #[]
where
  typed (s : Syntax) : Bool := s.isOfKind ``Parser.Term.typeAscription && s[3].getNumArgs == 1
  open_ (parent : Syntax) : Bool :=
    parent.isOfKind ``Parser.Tactic.exact || parent.isOfKind ``Parser.Tactic.refine ||
    parent.isOfKind ``Parser.Term.letIdDecl ||
    parent.isOfKind ``Parser.Term.typeAscription || parent.isOfKind ``Parser.Term.paren
  go (parent s : Syntax) (acc : Array Annotation) : Array Annotation :=
    if tactics.contains s.getKind then acc else
    let acc := if typed s then acc.push ⟨s, false, open_ parent⟩ else acc
    let acc := if s.isOfKind ``Parser.Term.basicFun then
      let acc := if s[1].getNumArgs == 1 then acc.push ⟨s, true, false⟩ else acc
      s[0].getArgs.foldl (fun acc b => if typed b && b[1].isIdent then acc.push ⟨b, true, true⟩ else acc) acc
    else acc
    -- The binders of a `fun` are not terms, so a typed one is not an ascription.
    let args := if s.isOfKind ``Parser.Term.basicFun then s.getArgs.extract 1 s.getNumArgs else s.getArgs
    -- A list node passes its parent on. The arguments of `⟨a, b⟩` each stand alone.
    let next := if s.isOfKind nullKind then parent
      else if s.isOfKind ``Parser.Term.anonymousCtor then Syntax.node .none ``Parser.Term.paren #[] else s
    args.foldl (fun acc a => go next a acc) acc

/-- The candidate and edit that drop the type of an annotation. `(e : T)` becomes `e` when `e` is
    a name, a literal or bracketed or where it stands alone, and `(e)` otherwise. -/
private def unannotate (input : String) (a : Annotation) : Option (Syntax × Syntax.Range × String) := do
  let stx := a.stx
  let whole ← stx.getRange? (canonicalOnly := true)
  guard (uncommented input whole)
  if stx.isOfKind ``Parser.Term.basicFun then
    let stop ← stx[1].getTailPos? (canonicalOnly := true)
    let start ← stx[0].getTailPos? (canonicalOnly := true)
    return (stx.setArg 1 mkNullNode, ⟨start, stop⟩, "")
  let e := stx[1]
  let er ← e.getRange? (canonicalOnly := true)
  let text := String.Pos.Raw.extract input er.start er.stop
  -- `(e)` keeps the hygiene of the original parenthesis.
  let paren := mkNode ``Parser.Term.paren #[stx[0], e, stx[4]]
  let atomic := e.isIdent || e.isOfKind ``Parser.Term.num || e.isOfKind ``Parser.Term.str ||
    e.isOfKind ``Parser.Term.paren || e.isOfKind ``Parser.Term.anonymousCtor ||
    e.isOfKind ``Parser.Term.typeAscription
  if !text.contains '·' && (atomic || a.bare) && !text.contains '\n' then return (e, whole, text)
  let close ← stx[4].getPos? (canonicalOnly := true)
  return (paren, ⟨er.stop, close⟩, "")

/-- Whether the ascription restates the type that its position expects, as recorded where it was
    elaborated. Otherwise it converts or fixes the type of a term and is never redundant. -/
private def restates (ci : ContextInfo) (ti : TermInfo) : IO Bool := do
  let some expected := ti.expectedType? | return false
  try
    ci.runMetaM ti.lctx do
      let x ← instantiateMVars expected
      if x.hasExprMVar then return false
      withReducible (isDefEq x (← instantiateMVars (← inferType ti.expr)))
  catch _ => return false

/-- Goals with the same hypothesis names whose closed types unify when only instances unfold, as
    when an inferred type reaches a coercion through a different instance path. -/
private def sameUpToInstances (ci : ContextInfo) (a b : List (Expr × List Name)) : IO Bool := do
  if a.length != b.length then return false
  ci.runMetaM {} do
    for ((x, xs), (y, ys)) in a.zip b do
      unless xs == ys && (← withReducibleAndInstances (isDefEqGuarded x y)) do return false
    return true

/-- Checked deletions inside the tactic proofs of one info tree, for the selected `rules`. -/
def edits (input : String) (map : FileMap) (tree : InfoTree) (rules : List String) : IO (Array Edit) := do
  let mut found := tree.foldInfo (init := #[]) fun ci info acc => Id.run do
    let .ofTacticInfo ti := info | return acc
    let some s := site? input map ti.stx | return acc
    unless rules.contains s.rule do return acc
    let g :: others := ti.goalsBefore | return acc
    return acc.push (s, if s.single && !others.isEmpty then none else some (ci, ti.mctxBefore, g))
  if rules.contains "redundantAscription" then
    let terms := tree.foldInfo (init := ({} : Std.HashMap (Nat × Nat) (ContextInfo × TermInfo)))
      fun ci info acc => Id.run do
        let .ofTermInfo ti := info | return acc
        unless ti.stx.isOfKind ``Parser.Term.typeAscription do return acc
        let some r := ti.stx.getRange? (canonicalOnly := true) | return acc
        return acc.insert (r.start.byteIdx, r.stop.byteIdx) (ci, ti)
    let steps := tree.foldInfo (init := #[]) fun ci info acc => Id.run do
      let .ofTacticInfo ti := info | return acc
      let g :: _ := ti.goalsBefore | return acc
      return acc.push (ci, ti, g)
    for (ci, ti, g) in steps do
      let some cat := (Parser.parserExtension.getState ci.env).categories.find? `tactic | continue
      for a in annotations cat.kinds ti.stx do
        unless a.binder do
          let some r := a.stx.getRange? (canonicalOnly := true) | continue
          let some (tci, tti) := terms[(r.start.byteIdx, r.stop.byteIdx)]? | continue
          unless ← restates tci tti do continue
        let some (cand, range, text) := unannotate input a | continue
        let site : Site := {
          rule := "redundantAscription", message := "Lean expects this type here", original := ti.stx
          options := #[(replaceNode a.stx cand ti.stx, range, text)], key := range }
        found := found.push (site, some (ci, ti.mctxBefore, g))
  -- Macro expansions and combinators such as `<;>` record one occurrence more than once.
  let mut sites : Array (Site × Option (Array (ContextInfo × MetavarContext × MVarId))) := #[]
  for (s, run) in found do
    match sites.findIdx? (·.1.key == s.key) with
    | some k => sites := sites.modify k fun (s, runs) => (s, do
        let rs ← runs
        let (ci, m, g) ← run
        return if rs.any (·.2.2 == g) then rs else rs.push (ci, m, g))
    | none => sites := sites.push (s, run.map (#[·]))
  let mut out := #[]
  for (s, runs?) in sites do
    let some runs := runs? | continue
    let mut bases := #[]
    for (ci, mctx, g) in runs do
      let some base ← Replay.run ci map mctx g s.original (Replay.cap ci) | break
      bases := bases.push base
    if bases.size < runs.size then continue
    for (candidate, range, newText) in s.options do
      let mut same := true
      for ((ci, mctx, g), base) in runs.zip bases do
        -- The candidate may cost a little more; a step that is much slower is not worth its bytes.
        let some cand ← Replay.run ci map mctx g candidate (2 * base.heartbeats + 100000)
          | same := false; break
        if cand.goals == base.goals then continue
        unless ← sameUpToInstances ci base.goals cand.goals do same := false; break
      if same then
        out := out.push { rule := s.rule, message := s.message, range, newText }
        break
  return out

end LeanPerf.Redundant
