import Lean

open Lean Elab Meta

namespace LeanPerf.ProofCompression

/--
Elaborate `term` as a proof of `concl`. Called in the context of the proof's binders, under
their own names, as when the proof is elaborated in its source file.
-/
def confirm (concl : Expr) (term : String) : MetaM Bool := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term term | return false
  let check : TermElabM Bool := do
    let e ← Term.elabTermEnsuringType stx concl
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    return !e.hasMVar && !e.hasSorry && (← isDefEq (← inferType e) concl)
  try
    withoutModifyingState do
      modifyThe Core.State fun s => { s with messages := {} }
      -- Cached instances and unfoldings may come from a larger environment than this one.
      modifyThe Meta.State fun s => { s with cache := {} }
      let ok ← check.run' {} {}
      return ok && !(← getThe Core.State).messages.hasErrors
  catch _ => return false

/-- Bounded structural fingerprint for retrieving proof candidates. A theorem parameter and a
    local variable have the same fingerprint. The actual proof is elaborated in the use site. -/
private def fingerprint : Nat → Expr → UInt64
  | 0, _ => 0
  | k+1, e => match e with
    | .app f a => mixHash (fingerprint k f) (fingerprint k a)
    | .const n _ => hash n
    | .lit v => hash v
    | .proj s i a => mixHash (hash (s, i)) (fingerprint k a)
    | .lam _ a b _ | .forallE _ a b _ => mixHash (fingerprint k a) (fingerprint k b)
    | .mdata _ a => fingerprint k a
    | _ => 1

abbrev Index := Std.HashMap UInt64 (Array Name)

private def addTheorem (idx : Index) (c : ConstantInfo) : Index := Id.run do
  let .thmInfo t := c | return idx
  let n := t.name
  if n.isInternal || n.hasMacroScopes || n.isInternalDetail || isPrivateName n then return idx
  let key := fingerprint 8 t.type.getForallBody
  return idx.alter key fun names => some ((names.getD #[]).push n)

def importIndex (env : Environment) : Index := Id.run do
  let mut idx := {}
  for data in env.header.moduleData do
    for c in data.constants do idx := addTheorem idx c
  return idx

private def reversed? (goal : Expr) : Option (Expr × Name) := do
  let .app (.app rel a) b := goal.consumeMData | none
  let symm ← match rel.getAppFn.constName? with
    | some ``Eq => some ``Eq.symm
    | some ``Iff => some ``Iff.symm
    | _ => none
  return (mkApp2 rel b a, symm)

/-- Apply one named theorem, discharging remaining arguments from the local context. -/
private def applyTheorem (p : Expr) (n : Name) : MetaM (Option Expr) := observing? do
  let g ← mkFreshExprSyntheticOpaqueMVar p
  let lemma ← mkConstWithFreshMVarLevels n
  for sub in ← g.mvarId!.apply lemma do sub.assumption
  let proof ← instantiateMVars g
  guard (!proof.hasMVar && !proof.hasSorry)
  return proof

private def suggestion (goal : Expr) (originalProof : Option Expr) (original : String) (imports locals : Index) (atomic : Bool) :
    MetaM (Option String) := do
  let mut best := none
  let mut bound := original.utf8ByteSize
  let mut orientations := #[(goal, none)]
  if let some (rev, symm) := reversed? goal then orientations := orientations.push (rev, some symm)
  let ctx ← getLCtx
  for (p, symm) in orientations do
    let key := fingerprint 8 p
    let mut proofs := if symm.isNone then originalProof.toArray else #[]
    for d in ctx do
      unless !d.isImplementationDetail && fingerprint 8 d.type == key do continue
      if (← withReducible (isDefEqGuarded d.type p)) then proofs := proofs.push d.toExpr
    for group in [locals[key]?.getD #[], imports[key]?.getD #[]] do
      -- A common shape such as "x = y" can have thousands of matches. Leave it to local facts.
      if group.size > 32 then continue
      for n in group do
        if Linter.isDeprecated (← getEnv) n then continue
        if let some proof ← applyTheorem p n then proofs := proofs.push proof
    for proof in proofs do
      let e ← if let some n := symm then mkAppM n #[proof] else pure proof
      let text := (← withOptions (fun o => o.setBool `pp.proofs true) (Meta.ppExpr e)).pretty 200
      if text.contains '\n' then continue
      let text := if atomic && text.contains ' ' then "(" ++ text ++ ")" else text
      if text.utf8ByteSize < bound && (← confirm goal text) then
        best := some text
        bound := text.utf8ByteSize
  return best

/-- A `by` can appear as an unparenthesized function argument. Protect applications there. -/
private def needsParens (input : String) (pos : String.Pos.Raw) : Bool :=
  let before := (input.sliceTo (input.pos! pos)).trimAsciiEnd
  !(before.endsWith ":=" || before.endsWith "=>" || before.endsWith "(" || before.endsWith "⟨" ||
    before.endsWith " from")

def scan (input : String) (map : FileMap) (tree : InfoTree) (imports locals : Index) :
    IO (Array Lsp.TextEdit × NameSet) := do
  let (terms, names) := tree.foldInfo (init := (#[], ({} : NameSet))) fun ci i (ts, ns) => Id.run do
    let ns := ci.parentDecl?.elim ns ns.insert
    let .ofTacticInfo ti := i | return (ts, ns)
    unless ti.stx.isOfKind ``Parser.Term.byTactic do return (ts, ns)
    let [g] := ti.goalsBefore | return (ts, ns)
    let some r := ti.stx.getRange? (canonicalOnly := true) | return (ts, ns)
    return (ts.push (ci, ti, g, r), ns)
  let mut edits := #[]
  for (ci, ti, g, r) in terms do
    let original := String.Pos.Raw.extract input r.start r.stop
    unless original.startsWith "by" && !original.contains "--" && !original.contains "/-" do continue
    let some decl := ti.mctxBefore.findDecl? g | continue
    let replacement ← ci.runMetaM decl.lctx do
      tryCatchRuntimeEx (withCurrHeartbeats <| withTheReader Core.Context
        ({ · with maxHeartbeats := 3000000 }) do
          setMCtx ti.mctxAfter
          let proof ← instantiateMVars (mkMVar g)
          let small := if proof.approxDepth ≤ 12 && !proof.hasMVar && !proof.hasSorry then some proof else none
          setMCtx ti.mctxBefore
          g.withContext do
            let goal ← instantiateMVars (← g.getType)
            if goal.hasMVar || !(← isProp goal) then return none
            return ← suggestion goal small original imports locals (needsParens input r.start))
        fun _ => return none
    if let some text := replacement then
      edits := edits.push { range := map.utf8RangeToLspRange r, newText := text }
  return (edits, names)

def addDecls (idx : Index) (env : Environment) (names : NameSet) : Index := Id.run do
  let mut idx := idx
  for n in names do
    if let some c := env.find? n then idx := addTheorem idx c
  return idx

end LeanPerf.ProofCompression
