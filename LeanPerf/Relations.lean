import Lean

open Lean Meta

namespace LeanPerf.Relations

private inductive Relation where
  | eq | iff | le | lt
  deriving BEq, Hashable, Inhabited

private def sides? (type : Expr) : Option (Relation × Expr × Expr) := do
  let .app (.app f a) b := type.consumeMData | none
  let r ← match f.getAppFn.constName? with
    | some ``Eq => some .eq
    | some ``Iff => some .iff
    | some ``LE.le => some .le
    | some ``LT.lt => some .lt
    | _ => none
  return (r, a, b)

private structure Edge where
  dst : Expr
  rel : Relation
  proof : String
  deriving Inhabited

private abbrev Graph := Std.HashMap Expr (Array Edge)

private def insertFact (edges : Graph) (type : Expr) (proof : String) : Graph := Id.run do
  let some (r, a, b) := sides? type | return edges
  let add (g : Graph) (x y : Expr) (r : Relation) (p : String) :=
    g.alter x fun es => some ((es.getD #[]).push ⟨y, r, p⟩)
  let edges := add edges a b r proof
  if r == .eq || r == .iff then return add edges b a r (proof ++ ".symm")
  return edges

private def compose? (a b : Relation) : Option (Relation × String) :=
  if a == b then some (a, ".trans")
  else match a, b with
    | .lt, .le => some (.lt, ".trans_le")
    | .le, .lt => some (.lt, ".trans_lt")
    | _, _ => none

private def receiver (s : String) : String := if s.contains ' ' then "(" ++ s ++ ")" else s

/-- Search the local relation graph for short chains. Vertices are elaborated expressions, so
    different spellings of the same endpoint join without a source rewrite. At each depth a
    shorter path to the same endpoint with the same relation dominates a longer path. Callers
    re-elaborate suggestions to resolve order instances, shadowing and field notation. -/
def candidates (goal : Expr) : MetaM (Array String) := do
  let ctx ← getLCtx
  let mut edges : Graph := {}
  let mut result := #[]
  let target := sides? goal
  for d in ctx do
    if d.isImplementationDetail || d.userName.hasMacroScopes || d.userName.isInternal then continue
    unless (ctx.findFromUserName? d.userName).any (·.fvarId == d.fvarId) do continue
    let name := d.userName.toString
    let facts := if d.type.isAppOfArity ``And 2 then
        #[(d.type, name), (d.type.appFn!.appArg!, name ++ ".1"), (d.type.appArg!, name ++ ".2")]
      else #[(d.type, name)]
    for (ty, p) in facts do
      if ty == goal then result := result.push p
      if target.isSome then edges := insertFact edges ty p
  let some (want, start, stop) := target | return result
  let mut frontier := edges[start]?.getD #[]
  if want == .eq then
    if let some f := frontier.find? (fun e => e.rel == .le && e.dst == stop) then
      if let some b := (edges[stop]?.getD #[]).find? (fun e => e.rel == .le && e.dst == start) then
        result := result.push (f.proof ++ ".antisymm " ++ b.proof)
        result := result.push ("le_antisymm " ++ f.proof ++ " " ++ b.proof)
  let mut best : Std.HashMap (Expr × Relation) Nat := {}
  for depth in [:3] do
    let mut next : Std.HashMap (Expr × Relation) Edge := {}
    for e in frontier do
      let key := (e.dst, e.rel)
      let size := e.proof.utf8ByteSize
      if best[key]?.any (· ≤ size) then continue
      best := best.insert key size
      if e.dst == stop then
        if e.rel == want then result := result.push e.proof
        else if e.rel == .lt && want == .le then result := result.push (receiver e.proof ++ ".le")
      if depth < 2 then
        for step in edges[e.dst]?.getD #[] do
          let some (r, op) := compose? e.rel step.rel | continue
          let proof := receiver e.proof ++ op ++ " " ++ step.proof
          let dest := (step.dst, r)
          if best[dest]?.any (· ≤ proof.utf8ByteSize) then continue
          if next[dest]?.any (fun old => old.proof.utf8ByteSize ≤ proof.utf8ByteSize) then continue
          next := next.insert dest ⟨step.dst, r, proof⟩
    frontier := next.valuesArray
    if frontier.isEmpty then break
  let sorted := result.qsort fun a b =>
    a.utf8ByteSize < b.utf8ByteSize || (a.utf8ByteSize == b.utf8ByteSize && a < b)
  return sorted.toList.eraseDups.toArray.extract 0 4

end LeanPerf.Relations
