import LeanPerf.Combine
import LeanPerf.Prune
import LeanPerf.Signature

/-!
# Rewrites that Claude makes most often

Claude's accepted rewrites of the Riemann modules inline local proofs used once (it removes nearly
half of the `have`s), write terms for `by exact`, turn `intro x; exact e` into `fun x ↦ e` and
write `.1`/`.2` for `.mp`/`.mpr`. These are syntactic, so they need no model: each is an edit to
the command's source that Lean then checks by elaborating the command, as every other edit is.

* `inlineHave`: `have h : T := e` whose `h` the rest of its tactic block names once, with `e` (or
  `(e : T)` when `e` alone does not elaborate) at that place.
* `obtainProjection`: a flat `obtain` or `rcases` of a local, with projections at its uses.
* `termExact`: `by exact e` as `e`, and `by intro x y; exact e` as `fun x y ↦ e`.
* `termCompile`: structural tactic blocks as terms, with short tactic proofs at the leaves.
* `shortProjection`: `h.mp` as `h.1` and `h.mpr` as `h.2`.
* `simpaUsing`: `simp at h` followed by a final `exact h` as `simpa using h`.
* `rwaAt`: `rw [L] at h` followed by a final `exact h` as `rwa [L] at h`.
* `mergeRw`: consecutive `rw` steps at the same location as one `rw`.
-/

open Lean Elab

namespace LeanPerf.Golf

private def saving (e : Edit) : Int :=
  (e.range.stop.byteIdx - e.range.start.byteIdx : Int) - e.newText.utf8ByteSize

private partial def nodes (p : Syntax → Bool) (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if p stx then acc.push stx else acc
  stx.getArgs.foldl (fun acc a => nodes p a acc) acc

private def range? (stx : Syntax) : Option Syntax.Range := stx.getRange? (canonicalOnly := true)

private def text (input : String) (r : Syntax.Range) : String := String.Pos.Raw.extract input r.start r.stop

/-- The column of byte `p` and the length in characters of the line it is on. -/
private def lineAt (input : String) (map : FileMap) (p : String.Pos.Raw) : Nat × Nat :=
  let pos := map.toPosition p
  let start := map.ofPosition { pos with column := 0 }
  let stop := map.ofPosition { line := pos.line + 1, column := 0 }
  let line := (String.Pos.Raw.extract input start stop).trimAsciiEnd.toString
  (pos.column, line.length)

/-- A term written on one line: its source with each line break and the indentation after it as one
    space. Not for terms whose layout matters or that hold comments. -/
private def oneLine? (input : String) (stx : Syntax) : Option String := do
  let r ← range? stx
  let t := text input r
  if !t.contains '\n' then return t
  if t.contains "--" || t.contains "/-" then none
  let layout := nodes (fun s => s.isOfKind ``Parser.Term.byTactic || s.isOfKind ``Parser.Term.match ||
    s.isOfKind ``Parser.Term.fun || s.getKind.toString.startsWith "Lean.calc") stx
  guard layout.isEmpty
  return " ".intercalate ((t.splitOn "\n").map (·.trimAscii.toString))

/-- Whether a term needs no parentheses wherever it goes. -/
private def atomic (stx : Syntax) : Bool :=
  stx.isIdent || stx.isOfKind ``Parser.Term.paren || stx.isOfKind ``Parser.Term.anonymousCtor ||
  stx.isOfKind ``Parser.Term.typeAscription || stx.isOfKind ``Parser.Term.num

/-- The name a `have` binds: its identifier, or `this`. -/
private def boundName? (letId : Syntax) : Option Name :=
  if letId[0].isIdent then some letId[0].getId
  else if letId[0].isOfKind `hygieneInfo then some `this
  else none

private def separatedSteps (items : Syntax) : Array Syntax :=
  (items.getArgs.toList.zipIdx.filterMap fun (a, i) => if i % 2 == 0 then some a else none).toArray

/-- The steps of each tactic sequence written one per line. -/
private def sequences (cmd : Syntax) : Array (Array Syntax) :=
  (nodes (·.isOfKind ``Parser.Tactic.tacticSeq1Indented) cmd).map (fun seq => separatedSteps seq[0])

/-- `have` steps whose name the rest of their block names once, inlined there. Each gives the edit
    from the `have` to the use: without the type, and with it. -/
def inlineHaves (input : String) (map : FileMap) (cmd : Syntax) (width := 100) : Array (Array Edit) := Id.run do
  let mut out := #[]
  for steps in sequences cmd do
    for h : i in [:steps.size] do
      let st := steps[i]
      unless st.isOfKind ``Parser.Tactic.tacticHave__ do continue
      let decl := st[2][0]
      unless decl.isOfKind ``Parser.Term.letIdDecl do continue
      let some n := boundName? decl[0] | continue
      -- Binders would need a `fun`; leave them.
      unless decl[1].getNumArgs == 0 do continue
      let value := decl[decl.getNumArgs - 1]
      let some v := oneLine? input value | continue
      let some haveRange := range? st | continue
      let some lines := Prune.wholeLines? input map haveRange | continue
      let uses := (steps.extract (i + 1) steps.size).foldl (init := #[]) fun acc s =>
        nodes (fun x => x.isIdent && x.getId.getRoot == n) s acc
      let [use] := uses.toList | continue
      let some ur := range? use | continue
      -- `h.trans x` names `h` with a field: the field stays after the inlined term.
      let field := (text input ur).drop n.toString.length |>.toString
      let parent := (nodes (fun x => x.getArgs.any (·.getRange? == use.getRange?)) cmd).back?
      let openPos := field.isEmpty && parent.any fun p =>
        p.isOfKind ``Parser.Tactic.exact || p.isOfKind ``Parser.Tactic.refine ||
        p.isOfKind ``Parser.Tactic.apply || p.getKind.toString.endsWith "rwRule" ||
        p.getKind.toString.endsWith "simpLemma"
      let typed := decl[2].getArgs.findSome? fun ts =>
        if ts.isOfKind ``Parser.Term.typeSpec then range? ts[1] |>.map (text input) else none
      let between := String.Pos.Raw.extract input lines.stop ur.start
      let (col, len) := lineAt input map ur.start
      let mut variants := #[]
      variants := variants.push (if atomic value || openPos then v else s!"({v})")
      if let some t := typed then variants := variants.push s!"({v} : {t})"
      let mut group := #[]
      for repl in variants do
        let repl := repl ++ field
        -- The line of the use, with the term in place of the name.
        if col + repl.length + (len - col - (text input ur).length) > width then continue
        group := group.push { rule := "inlineHave", range := ⟨lines.start, ur.stop⟩
                              newText := between ++ repl
                              message := s!"Use the proof of `{n}` where it is needed" }
      unless group.isEmpty do out := out.push group
  return out

private def singleRCasesPat? (pat : Syntax) : Option Syntax := do
  let med ← if pat.isOfKind ``Parser.Tactic.rcasesPatLo then
      if pat[1].getNumArgs == 0 then some pat[0] else none
    else some pat
  guard (med.isOfKind ``Parser.Tactic.rcasesPatMed && med[0].getNumArgs == 1)
  return med[0][0]

private def projectionPattern? (st : Syntax) : Option (Syntax × Array (Name × String)) := do
  let (hyp, pat) ←
    if st.isOfKind ``Parser.Tactic.obtain && st[2].getNumArgs == 0 && st[3][1].getNumArgs == 1 then
      some (st[3][1][0], st[1][0])
    else if st.isOfKind ``Parser.Tactic.rcases && st[1].getNumArgs == 1 &&
        st[1][0].isOfKind ``Parser.Tactic.elimTarget && st[1][0][0].getNumArgs == 0 then
      some (st[1][0][1], st[2][1])
    else none
  guard (hyp.isIdent && hyp.getId.isAtomic)
  let tuple ← singleRCasesPat? pat
  guard (tuple.isOfKind ``Parser.Tactic.rcasesPat.tuple)
  let parts := separatedSteps tuple[1]
  let fields ← match parts.size with
    | 2 => some #[".1", ".2"]
    | 3 => some #[".1", ".2.1", ".2.2"]
    | _ => none
  let names ← (parts.zip fields).mapM fun (part, field) => do
    let p ← singleRCasesPat? part
    if p.isOfKind ``Parser.Tactic.rcasesPat.ignore then return none
    let n := p[0].getId
    guard (p.isOfKind ``Parser.Tactic.rcasesPat.one && p[0].isIdent && n.isAtomic && n != `rfl)
    return some (n, field)
  let names := names.filterMap id
  guard (!names.isEmpty && (hyp.getId :: (names.toList.map Prod.fst)).Nodup)
  return (hyp, names)

/-- Remove a flat destructuring step and replace each named component with a projection of its
    source local. Use elaboration info to avoid rebinding and ambiguous occurrences. -/
def obtainProjection (input : String) (map : FileMap) (cmd : Syntax) (trees : Array InfoTree) :
    Array Edit := Id.run do
  let mut out := #[]
  let mut binders : Array (String.Pos.Raw × Name) := #[]
  let mut refs : Std.HashSet (String.Pos.Raw × Name) := {}
  for tree in trees do
    let (bs, rs) := tree.foldInfo (init := (binders, refs)) fun _ info (bs, rs) => Id.run do
      let .ofTermInfo ti := info | return (bs, rs)
      let some r := range? ti.stx | return (bs, rs)
      if ti.isBinder then
        let n := if ti.stx.isIdent then ti.stx.getId else
          if let .fvar f := ti.expr then (ti.lctx.find? f).map (·.userName) |>.getD .anonymous
          else .anonymous
        return (bs.push (r.start, n), rs)
      if ti.stx.isIdent then return (bs, rs.insert (r.start, ti.stx.getId.getRoot))
      return (bs, rs)
    binders := bs
    refs := rs
  for steps in sequences cmd do
    let some last := steps.back?.bind range? | continue
    for h : i in [:steps.size] do
      let st := steps[i]
      let some (hyp, fields) := projectionPattern? st | continue
      let some hr := range? hyp | continue
      let some r := range? st | continue
      let some lines := Prune.wholeLines? input map r | continue
      let name := hyp.getId
      let relevant := fun n => n == name || fields.any (fun (part, _) => part == n)
      if binders.any (fun (p, n) => lines.stop ≤ p && p < last.stop && relevant n) then continue
      let uses := (steps.extract (i + 1) steps.size).foldl (init := #[]) fun acc s =>
        nodes (fun x => x.isIdent && relevant x.getId.getRoot) s acc
      -- An identifier the elaborator did not recognize as a reference may be a binder.
      let some uses := uses.mapM (fun x => do
        let r ← range? x
        let n := x.getId.getRoot
        guard (refs.contains (r.start, n))
        return (x, r, n)) | continue
      unless fields.all (fun (n, _) => uses.any (fun (_, _, u) => u == n)) do continue
      let mut cursor := lines.stop
      let mut newText := ""
      let source := text input hr
      for (x, ur, n) in uses.qsort (fun (_, a, _) (_, b, _) => a.start < b.start) do
        let some (_, field) := fields.find? (fun (part, _) => part == n) | continue
        let some head := x.identComponents.head?.bind range? | continue
        if ur.start < cursor then continue
        -- Keep any field suffix verbatim, including escaped names.
        newText := newText ++ text input ⟨cursor, ur.start⟩ ++ source ++ field ++
          text input ⟨head.stop, ur.stop⟩
        cursor := ur.stop
      let e := { rule := "obtainProjection", range := ⟨lines.start, cursor⟩, newText
                 message := s!"Use projections of `{name}` directly" }
      if saving e > 0 then out := out.push e
  return out

/-- `by exact e` as `e`, and `by intro x y` then `exact e` as `fun x y ↦ e`. -/
def termExacts (input : String) (map : FileMap) (cmd : Syntax) (width := 100) : Array Edit := Id.run do
  let mut out := #[]
  for b in nodes (·.isOfKind ``Parser.Term.byTactic) cmd do
    let seq := b[1][0]
    unless seq.isOfKind ``Parser.Tactic.tacticSeq1Indented do continue
    let steps := separatedSteps seq[0]
    let some br := range? b | continue
    -- Only `stripComments` deletes comments, and only when asked to.
    if (text input br).contains "--" || (text input br).contains "/-" then continue
    let some last := steps.back? | continue
    unless last.isOfKind ``Parser.Tactic.exact do continue
    let some er := range? last[1] | continue
    let body := text input er
    let term ← match steps.size with
      | 1 => pure (some body)
      | 2 =>
        let intro := steps[0]!
        let names := intro[1].getArgs
        if intro.isOfKind ``Parser.Tactic.intro && !names.isEmpty &&
            names.all (fun x => x.isIdent || x.isOfKind ``Parser.Term.hole) then
          pure (some s!"fun {" ".intercalate (names.toList.map fun x => (range? x).map (text input) |>.getD "_")} ↦ {body}")
        else pure none
      | _ => pure none
    let some term := term | continue
    let (col, len) := lineAt input map br.start
    -- On the line of the `by` when it fits there, else on a line of its own.
    let firstLine := (term.splitOn "\n").head!
    let before := (String.Pos.Raw.extract input (map.ofPosition { map.toPosition br.start with column := 0 }) br.start)
    let newText := if col + firstLine.length ≤ width || !before.trimAscii.toString.endsWith ":=" then term
      else
        let (ecol, _) := lineAt input map er.start
        "\n" ++ String.ofList (List.replicate ecol ' ') ++ term
    if col + firstLine.length > width && !newText.startsWith "\n" then continue
    if len > width then continue
    let e := { rule := "termExact", range := br, newText
               message := if steps.size == 1 then "Write the term for `by exact`" else "Write `fun` for `intro` and `exact`" }
    if saving e > 0 then out := out.push e
  return out

private structure CompiledTerm where
  source : String
  atomic : Bool := false
  isLeaf : Bool := false

private def CompiledTerm.embed (term : CompiledTerm) (ctorArg := false) : String :=
  if term.atomic || ctorArg then term.source else s!"({term.source})"

/-- Anonymous holes in source order, with their constructor argument context. -/
private partial def refineHoles (stx : Syntax) (ctorArg := false)
    (acc : Array (Syntax × Bool) := #[]) : Array (Syntax × Bool) :=
  if stx.isOfKind ``Parser.Term.syntheticHole && stx[1].getAtomVal == "_" then
    acc.push (stx, ctorArg)
  else if stx.isOfKind ``Parser.Term.anonymousCtor then
    stx[1].getArgs.foldl (fun acc arg => refineHoles arg true acc) acc
  else
    stx.getArgs.foldl (fun acc arg => refineHoles arg false acc) acc

private def tacticLeaf (input : String) (steps : Array Syntax) : Option CompiledTerm := do
  guard (!steps.isEmpty)
  let parts ← steps.mapM fun step => do
    let source := text input (← range? step)
    guard (!source.contains '\n' && !source.contains "·" && !source.contains "<;>")
    guard ((nodes (fun s => s.isAtom && ["case", "case'", "next"].contains s.getAtomVal)
      step).isEmpty)
    return source
  return { source := "by " ++ "; ".intercalate parts.toList, isLeaf := true }

private partial def compileSteps (input : String) (steps : Array Syntax) : Option CompiledTerm :=
  let structural : Option CompiledTerm := do
    let first ← steps[0]?
    let rest := steps.extract 1 steps.size
    let compileBullets (_ : Unit) := rest.mapM fun bullet => do
      guard (bullet.isOfKind ``Lean.cdot)
      let seq := bullet[1][0]
      if seq.isOfKind ``Parser.Tactic.tacticSeq1Indented then
        compileSteps input (separatedSteps seq[0])
      else if seq.isOfKind ``Parser.Tactic.tacticSeqBracketed then
        tacticLeaf input (separatedSteps seq[1])
      else none
    if first.isOfKind ``Parser.Tactic.exact && rest.isEmpty then
      let value := first[1]
      return { source := text input (← range? value), atomic := atomic value }
    if first.isOfKind ``Parser.Tactic.intro then
      let names := first[1].getArgs
      guard (!names.isEmpty && names.all (fun n => n.isIdent || n.isOfKind ``Parser.Term.hole))
      let names ← names.mapM fun n => (range? n).map (text input)
      let body ← compileSteps input rest
      -- A `fun` body extends as far as it can, so it needs no parentheses.
      return { source := s!"fun {" ".intercalate names.toList} ↦ {body.source}" }
    if first.isOfKind ``Parser.Tactic.constructor then
      guard (first[1][0].getNumArgs == 0)
      let args ← compileBullets ()
      return { source := "⟨" ++ ", ".intercalate (args.toList.map (·.embed true)) ++ "⟩", atomic := true }
    if first.isOfKind ``Parser.Tactic.refine then
      let value := first[1]
      let holes := refineHoles value
      guard (!holes.isEmpty)
      let args ← if holes.size == 1 && !(rest.any (·.isOfKind ``Lean.cdot)) then
          (compileSteps input rest).map (#[·])
        else do
          guard (holes.size == rest.size)
          compileBullets ()
      if value.isOfKind ``Parser.Term.syntheticHole then
        return (← args[0]?)
      -- Copy the source between holes so the surrounding term keeps its layout.
      let vr ← range? value
      let mut start := vr.start
      let mut source := ""
      for ((hole, ctorArg), arg) in holes.zip args do
        let hr ← range? hole
        source := source ++ text input ⟨start, hr.start⟩ ++ arg.embed ctorArg
        start := hr.stop
      return { source := source ++ text input ⟨start, vr.stop⟩, atomic := atomic value }
    none
  structural <|> tacticLeaf input steps

/-- Turn structural tactic steps into terms, retaining short tactic proofs for subgoals. -/
def termCompile (input : String) (map : FileMap) (cmd : Syntax) (width := 100) : Array Edit := Id.run do
  let mut out := #[]
  for b in nodes (·.isOfKind ``Parser.Term.byTactic) cmd do
    let seq := b[1][0]
    unless seq.isOfKind ``Parser.Tactic.tacticSeq1Indented do continue
    let some br := range? b | continue
    let source := text input br
    if source.contains "--" || source.contains "/-" then continue
    let steps := separatedSteps seq[0]
    let some term := compileSteps input steps | continue
    if term.isLeaf then continue
    let (col, _) := lineAt input map br.start
    let mut newText := term.source
    if col + (term.source.splitOn "\n").head!.length > width then
      let some first := steps[0]? | continue
      let some r := range? first | continue
      let (indent, _) := lineAt input map r.start
      newText := "\n" ++ String.ofList (List.replicate indent ' ') ++ term.source
    -- The replaced range can share its last line with more of the surrounding term.
    let (endCol, endLen) := lineAt input map br.stop
    let lines := (newText.splitOn "\n").toArray
    let widths := lines.mapIdx fun i line =>
      line.length + (if i == 0 then col else 0) + (if i + 1 == lines.size then endLen - endCol else 0)
    unless widths.all (· ≤ width) do continue
    let e := { rule := "termCompile", range := br, newText
               message := "Write structural tactic steps as a term" }
    if saving e ≥ 8 then out := out.push e
  return out

/-- `have h (x : X) … : T := e` whose explicit binders the theorem's statement binds with the same
    names and types, and whose every use in the rest of its block passes those variables there: the
    binders and those arguments go, so that `h` is a plain local (which `inlineHave` and
    `haveToRefine` can then remove). Folding a helper leaves such `have`s. -/
def sharedHaveBinders (input : String) (cmd : Syntax) : Array Edit := Id.run do
  let some thm := Signature.asTheorem? cmd | return #[]
  let norm (t : String) := " ".intercalate ((t.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty))
  let explicitsOf (binders : Array Syntax) : Array (Syntax × Nat × String × String) := Id.run do
    let mut out := #[]
    let mut i := 0
    for b in binders do
      unless b.isOfKind ``Parser.Term.explicitBinder do continue
      let ty := (range? b[2][1]).map (text input) |>.getD ""
      for x in b[1].getArgs do
        out := out.push (b, i, x.getId.toString, norm ty)
        i := i + 1
    return out
  let theirs := (explicitsOf thm[1][2][0].getArgs).map fun (_, _, n, t) => (n, t)
  let bytes := input.toUTF8
  let back (p : String.Pos.Raw) : String.Pos.Raw := Id.run do
    let mut s := p.byteIdx
    while s > 0 && bytes[s-1]! == ' '.toUInt8 do s := s - 1
    return ⟨s⟩
  let mut out := #[]
  for steps in sequences cmd do
    for i in [:steps.size] do
      let st := steps[i]!
      unless st.isOfKind ``Parser.Tactic.tacticHave__ do continue
      let decl := st[2][0]
      unless decl.isOfKind ``Parser.Term.letIdDecl do continue
      let some n := boundName? decl[0] | continue
      let binders := decl[1].getArgs
      -- Only explicit binders, all of them shared: then the `have` takes no arguments at all.
      unless !binders.isEmpty && binders.all (·.isOfKind ``Parser.Term.explicitBinder) do continue
      let mine := explicitsOf binders
      unless mine.all fun (_, _, m, t) => theirs.contains (m, t) do continue
      let uses := (steps.extract (i + 1) steps.size).foldl (init := #[]) fun acc s =>
        nodes (fun x => x.isIdent && x.getId == n) s acc
      if uses.isEmpty then continue
      let mut edits : Array (Syntax.Range × String) := #[]
      let mut ok := true
      for x in uses do
        let some ap := (nodes (fun s => s.isOfKind ``Parser.Term.app && s[0].getRange? == x.getRange?) cmd)[0]?
          | ok := false; break
        let args := ap[1].getArgs
        unless args.size == mine.size && (args.zip mine).all (fun (a, (_, _, m, _)) => a.isIdent && a.getId.toString == m) do
          ok := false; break
        -- `h x y` is `h`; the application's parentheses, if any, stay.
        let (some first, some lastArg) := (args[0]?.bind range?, args.back?.bind range?) | ok := false; break
        edits := edits.push (⟨back first.start, lastArg.stop⟩, "")
      unless ok do continue
      let (some b0, some b1) := (binders[0]?.bind range?, binders.back?.bind range?) | continue
      edits := edits.push (⟨back b0.start, b1.stop⟩, "")
      let sorted := edits.qsort (·.1.start < ·.1.start)
      let some start := sorted[0]?.map (·.1.start) | continue
      let some stop := sorted.back?.map (·.1.stop) | continue
      let mut newText := ""
      let mut p := start
      for (r, t) in sorted do
        newText := newText ++ String.Pos.Raw.extract input p r.start ++ t
        p := r.stop
      if newText.contains "--" || newText.contains "/-" then continue
      out := out.push { rule := "sharedHaveBinders", range := ⟨start, stop⟩, newText
                        message := s!"`{n}` can use the theorem's variables" }
  return out

/-- `have h : T := by tacs` whose `h` only the last step `exact e` names, once: the `have` goes, the
    last step becomes `refine e` with `?_` for `h`, and `tacs` follow it, dedented, to prove the hole.
    The type `T` is no longer written; when the hole needs it, `(?_ : T)` is the second candidate. -/
def haveToRefine (input : String) (map : FileMap) (cmd : Syntax) : Array (Array Edit) := Id.run do
  let mut out := #[]
  for steps in sequences cmd do
    let some last := steps.back? | continue
    unless last.isOfKind ``Parser.Tactic.exact do continue
    let some lr := range? last | continue
    for i in [:steps.size - 1] do
      let st := steps[i]!
      unless st.isOfKind ``Parser.Tactic.tacticHave__ do continue
      let decl := st[2][0]
      unless decl.isOfKind ``Parser.Term.letIdDecl && decl[1].getNumArgs == 0 do continue
      let some n := boundName? decl[0] | continue
      let value := decl[decl.getNumArgs - 1]
      unless value.isOfKind ``Parser.Term.byTactic do continue
      let some hr := range? st | continue
      let some lines := Prune.wholeLines? input map hr | continue
      -- Named once in all, by the last step, without fields.
      let uses := (steps.extract (i + 1) steps.size).foldl (init := #[]) fun acc s =>
        nodes (fun x => x.isIdent && x.getId.getRoot == n) s acc
      let [use] := uses.toList | continue
      unless use.getId == n do continue
      let some ur := range? use | continue
      unless lr.start ≤ ur.start && ur.stop ≤ lr.stop do continue
      let block := text input ⟨hr.start, lr.stop⟩
      if block.contains "--" || block.contains "/-" then continue
      -- The `have`'s tactics, at the column of the sequence's steps.
      let seq := value[1][0]
      unless seq.isOfKind ``Parser.Tactic.tacticSeq1Indented do continue
      let some sr := range? seq | continue
      let stepCol := (map.toPosition hr.start).column
      let tacCol := (map.toPosition sr.start).column
      let tacText := text input sr
      let tacLines := tacText.splitOn "\n"
      let pad := String.ofList (List.replicate stepCol ' ')
      -- Lines after the first keep their place relative to the first, which moves to `stepCol`.
      let some body := (tacLines.drop 1).foldlM (init := pad ++ tacLines.head!) (fun acc l =>
        if l.trimAscii.isEmpty then some (acc ++ "\n") else
        let lead := l.length - l.trimAsciiStart.toString.length
        if lead < tacCol then none else some (acc ++ "\n" ++ pad ++ (l.drop tacCol).toString)) | continue
      let typed := decl[2].getArgs.findSome? fun ts =>
        if ts.isOfKind ``Parser.Term.typeSpec then range? ts[1] |>.map (text input) else none
      let between := String.Pos.Raw.extract input lines.stop lr.start
      let exactKw := (range? last[0]).map (text input) |>.getD "exact"
      let mut group := #[]
      for hole in #["?_"] ++ (typed.map (fun t => #[s!"(?_ : {t})"])).getD #[] do
        let lastText := "refine" ++ String.Pos.Raw.extract input ⟨lr.start.byteIdx + exactKw.utf8ByteSize⟩ ur.start ++
          hole ++ String.Pos.Raw.extract input ur.stop lr.stop
        if lastText.contains '\n' then continue
        if stepCol + lastText.length > 100 then continue
        group := group.push { rule := "haveToRefine", range := ⟨lines.start, lr.stop⟩
                              newText := between ++ lastText ++ "\n" ++ body
                              message := s!"Prove `{n}` where the last step needs it" }
      unless group.isEmpty do out := out.push group
  return out

/-- The identifier in an `at h` location. -/
private def atHyp? (loc : Syntax) : Option Syntax := do
  let target := loc[0][1]
  guard (target.isOfKind ``Parser.Tactic.locationHyp)
  let #[h] := target[0].getArgs | none
  guard h.isIdent
  return h

/-- The range of two adjacent steps, when replacing it would preserve comments. -/
private def pairRange? (input : String) (first last : Syntax.Range) : Option Syntax.Range := do
  let r : Syntax.Range := ⟨first.start, last.stop⟩
  let source := text input r
  guard (!source.contains "--" && !source.contains "/-")
  return r

/-- The final two steps when a tactic at one hypothesis is followed by `exact` of that hypothesis. -/
private def finalHypPair? (input : String) (steps : Array Syntax) (kind : SyntaxNodeKind)
    (locationIdx : Nat) : Option (Syntax × Syntax × Syntax.Range) := do
  guard (steps.size ≥ 2)
  let tactic ← steps[steps.size - 2]?
  let last ← steps.back?
  guard (tactic.isOfKind kind && last.isOfKind ``Parser.Tactic.exact)
  let hyp ← atHyp? tactic[locationIdx]
  guard (last[1].isIdent && last[1].getId == hyp.getId)
  let r ← pairRange? input (← range? tactic) (← range? last)
  return (tactic, hyp, r)

/-- `simp at h` then a final `exact h` as `simpa using h`, retaining the simp arguments. -/
def simpaUsing (input : String) (cmd : Syntax) : Array Edit :=
  (sequences cmd).filterMap fun steps => do
    let (simp, hyp, r) ← finalHypPair? input steps ``Parser.Tactic.simp 5
    let keyword ← range? simp[0]
    let loc ← range? simp[5][0]
    let args := (text input ⟨keyword.stop, loc.start⟩).trimAsciiEnd.toString
    let h := text input (← range? hyp)
    return { rule := "simpaUsing", range := r, newText := s!"simpa{args} using {h}"
             message := "Use `simpa using` to simplify and close the goal" }

/-- `rw [L] at h` then a final `exact h` as `rwa [L] at h`. -/
def rwaAt (input : String) (cmd : Syntax) : Array Edit :=
  (sequences cmd).filterMap fun steps => do
    let (rw, _, r) ← finalHypPair? input steps ``Parser.Tactic.rwSeq 3
    -- `rwa` has no rewrite configuration.
    guard (rw[1][0].getNumArgs == 0)
    let keyword ← range? rw[0]
    let rwRange ← range? rw
    return { rule := "rwaAt", range := r, newText := "rwa" ++ text input ⟨keyword.stop, rwRange.stop⟩
             message := "Use `rwa` to rewrite the hypothesis and close the goal" }

/-- The rules inside an `rw` list, dropping any trailing comma so another list can follow. -/
private def rwRulesText? (input : String) (rw : Syntax) : Option String := do
  let rules := rw[2][1].getArgs.filter (·.isOfKind ``Parser.Tactic.rwRule)
  if rules.isEmpty then return ""
  let first ← range? rules[0]!
  let last ← range? rules.back!
  return text input ⟨first.start, last.stop⟩

/-- Consecutive `rw` steps at the same location as one, if each stands alone and the result fits. -/
def mergeRw (input : String) (map : FileMap) (cmd : Syntax) (width := 100) : Array Edit := Id.run do
  let mut out := #[]
  for steps in sequences cmd do
    for (first, last) in steps.toList.zip (steps.toList.drop 1) do
      unless first.isOfKind ``Parser.Tactic.rwSeq && last.isOfKind ``Parser.Tactic.rwSeq do continue
      unless first[1][0].getNumArgs == 0 && last[1][0].getNumArgs == 0 do continue
      let suffix ← if first[3].getNumArgs == 0 && last[3].getNumArgs == 0 then pure "" else do
        let some h := atHyp? first[3] | continue
        let some k := atHyp? last[3] | continue
        unless h.getId == k.getId do continue
        let some loc := range? first[3][0] | continue
        pure (" " ++ text input loc)
      let some fr := range? first | continue
      let some lr := range? last | continue
      let fp := map.toPosition fr.start
      let lp := map.toPosition lr.start
      unless fp.line == (map.toPosition fr.stop).line && lp.line == (map.toPosition lr.stop).line &&
          fp.line < lp.line do continue
      unless (Prune.wholeLines? input map fr).isSome && (Prune.wholeLines? input map lr).isSome do continue
      let some r := pairRange? input fr lr | continue
      let some a := rwRulesText? input first | continue
      let some b := rwRulesText? input last | continue
      let rules := ", ".intercalate ([a, b].filter (!·.isEmpty))
      let newText := s!"rw [{rules}]{suffix}"
      if fp.column + newText.length ≤ width then
        out := out.push { rule := "mergeRw", range := r, newText
                          message := "Merge consecutive `rw` steps at the same location" }
  return out

/-- `.mp` and `.mpr` of a proof of `↔` as `.1` and `.2`. -/
def shortProjections (input : String) (cmd : Syntax) : Array Edit := Id.run do
  let mut out := #[]
  for x in nodes (fun s => s.isIdent) cmd do
    let some r := range? x | continue
    let t := text input r
    let n := x.getId
    let some head := n.components.head? | continue
    -- `Iff.mp` and the like name the projection itself.
    if n.components.length < 2 || (n.components.length == 2 && (head.toString.toList.headD 'a').isUpper) then
      continue
    for (f, k) in [(".mpr", ".2"), (".mp", ".1")] do
      if t.endsWith f then
        out := out.push { rule := "shortProjection", range := ⟨⟨r.stop.byteIdx - f.utf8ByteSize⟩, r.stop⟩, newText := k
                          message := s!"Write `{k}` for `{f}`" }
        break
  for p in nodes (·.isOfKind ``Parser.Term.proj) cmd do
    let fld := p[2]
    unless fld.isIdent do continue
    let some r := range? fld | continue
    match fld.getId with
    | `mp => out := out.push { rule := "shortProjection", range := r, newText := "1", message := "Write `.1` for `.mp`" }
    | `mpr => out := out.push { rule := "shortProjection", range := r, newText := "2", message := "Write `.2` for `.mpr`" }
    | _ => pure ()
  return out

/-- Words that cannot name a local. -/
private def reserved : List String :=
  ["at", "by", "do", "fun", "if", "in", "λ", "let", "have", "show", "from", "with", "then", "else",
   "match", "end", "open", "this", "for", "use", "calc", "case", "next", "only", "using", "deriving",
   "where", "extends", "instance", "theorem", "lemma", "def", "example", "variable", "mut", "return"]

/-- Shorter names in the order they are tried for a local first named `old`: its first letter,
    then that letter with a prime or a digit, then its first two letters, then any letter. -/
private def namesFor (old : String) : List String :=
  let cs := old.toList
  let first := cs.headD 'x'
  let firstTwo := String.ofList (cs.take 2)
  let base := if first.isAlpha then [first.toString, s!"{first}'"] ++
      ((List.range 9).map fun i => s!"{first}{i + 1}") ++ [firstTwo] else []
  base ++ ("abcdefghijklmnopqrstuvwxyz".toList.map (·.toString))

/-- The locals that the proof of `cmd` binds by name, with every identifier in the proof whose
    first component names them: renamed to the shortest names that no identifier of the command
    uses. One group of edits per name, the names that save most first. -/
def shortNames (input : String) (cmd : Syntax) (trees : Array InfoTree) : Array (String × Array Edit) := Id.run do
  let some sig := (nodes (·.isOfKind ``Parser.Command.declSig) cmd)[0]? | return #[]
  let some sr := range? sig | return #[]
  let some cr := range? cmd | return #[]
  -- Locals bound in the proof, by the name written at the binder.
  let mut bound : Std.HashSet String := {}
  for t in trees do
    bound := t.foldInfo (init := bound) fun _ info acc => Id.run do
      let .ofTermInfo ti := info | return acc
      unless ti.isBinder && ti.expr.isFVar && ti.stx.isIdent do return acc
      let some r := range? ti.stx | return acc
      unless sr.stop ≤ r.start && r.stop ≤ cr.stop do return acc
      let n := ti.stx.getId
      unless n.isAtomic && !n.hasMacroScopes do return acc
      return acc.insert n.toString
  -- Every identifier's first component in the command, the statement included, is taken.
  let idents := nodes (·.isIdent) cmd
  let mut taken : Std.HashSet String := {}
  for x in idents do
    for c in x.getId.components do taken := taken.insert c.toString
  let sigNames := (nodes (·.isIdent) sig).foldl (fun s x => s.insert x.getId.toString) ({} : Std.HashSet String)
  -- Identifiers that name a parameter of another declaration, as in `(h := e)`, stay.
  let named := nodes (fun s => s.isOfKind ``Parser.Term.namedArgument) cmd |>.filterMap (fun s => range? s[1])
  let uses (old : String) : Array Syntax.Range := Id.run do
    let mut out := #[]
    for x in idents do
      let some r := range? x | continue
      unless sr.stop ≤ r.start do continue
      if named.any (· == r) then continue
      let some head := x.getId.components.head? | continue
      unless head.toString == old do continue
      unless (text input r).startsWith old do continue
      out := out.push ⟨r.start, ⟨r.start.byteIdx + old.utf8ByteSize⟩⟩
    return out
  let mut plans : Array (Nat × String × Array Syntax.Range) := #[]
  for old in bound.toList do
    if old.utf8ByteSize ≤ 1 || sigNames.contains old then continue
    let us := uses old
    if us.isEmpty then continue
    plans := plans.push (us.size * old.utf8ByteSize, old, us)
  plans := plans.qsort (·.1 > ·.1)
  let mut out := #[]
  for (_, old, us) in plans do
    let some new := (namesFor old).find? fun n => !taken.contains n && !reserved.contains n &&
      n.utf8ByteSize < old.utf8ByteSize | continue
    taken := taken.insert new
    out := out.push (old, us.map fun r => { rule := "shortNames", range := r, newText := new
                                            message := s!"Name `{old}` `{new}`" })
  return out

/-- The renamings that Lean accepts together: all at once, else halves of them in turn. -/
def checkedNames (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (ctx : Command.Context) (before after : Command.State) (trees : Array InfoTree) (trials := 8) :
    IO (Array Edit) := do
  let groups := shortNames input cmd trees
  if groups.isEmpty then return #[]
  let works (gs : Array (String × Array Edit)) : IO Bool := do
    let es := gs.foldl (fun acc (_, es) => acc ++ es) #[]
    let kept ← Combine.check input map cmd pctx ctx before after es (shorter := true) (trials := 1)
    return kept.size == es.size
  let mut accepted := #[]
  let mut todo := #[groups]
  for _ in [:trials] do
    let some g := todo.back? | break
    todo := todo.pop
    if ← works (accepted ++ g) then
      accepted := accepted ++ g
    else if g.size > 1 then
      todo := (todo.push (g.extract (g.size / 2) g.size)).push (g.extract 0 (g.size / 2))
  return accepted.foldl (fun acc (_, es) => acc ++ es) #[]

def rules : List String :=
  ["inlineHave", "obtainProjection", "sharedHaveBinders", "haveToRefine", "termExact", "termCompile", "simpaUsing", "rwaAt",
    "mergeRw", "shortProjection", "shortNames"]

/-- The edits that Lean accepts for `cmd`, which took `before` to `after`. Check each candidate
    alone up to `maxChecks` elaborations, then check the `shortProjection` edits together. -/
def edits (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (ctx : Command.Context) (before after : Command.State) (rules : List String) (maxChecks := 12) :
    IO (Array Edit) := do
  let works (e : Edit) : IO Bool := do
    let gain := (Steps.removed input cmd pctx e.range e.newText).toNat
    let kept ← Combine.check input map cmd pctx ctx before after #[{ e with gain }]
      (shorter := true) (trials := 1)
    return kept.size == 1
  let mut out := #[]
  let mut checks := 0
  let rules := rules.filter (· != "shortNames")
  let mut groups := (if rules.contains "inlineHave" then (inlineHaves input map cmd).map (·.toList) else #[]) ++
    (if rules.contains "obtainProjection" then
      (obtainProjection input map cmd after.infoState.trees.toArray).map ([·]) else #[]) ++
    (if rules.contains "termExact" then (termExacts input map cmd).map ([·]) else #[]) ++
    (if rules.contains "termCompile" then (termCompile input map cmd).map ([·]) else #[]) ++
    (if rules.contains "simpaUsing" then (simpaUsing input cmd).map ([·]) else #[]) ++
    (if rules.contains "rwaAt" then (rwaAt input cmd).map ([·]) else #[]) ++
    (if rules.contains "mergeRw" then (mergeRw input map cmd).map ([·]) else #[]) ++
    (if rules.contains "haveToRefine" then (haveToRefine input map cmd).map (·.toList) else #[]) ++
    (if rules.contains "sharedHaveBinders" then (sharedHaveBinders input cmd).map ([·]) else #[])
  groups := groups.qsort fun a b => (a.head?.map saving |>.getD 0) > (b.head?.map saving |>.getD 0)
  let debug ← debugging "golf"
  for g in groups do
    for e in g do
      if checks ≥ maxChecks then break
      if out.any fun o => o.range.start < e.range.stop && e.range.start < o.range.stop then break
      checks := checks + 1
      let ok ← works e
      if debug then
        IO.eprintln s!"golf {e.rule} {map.toPosition e.range.start} {if ok then "accepted" else "rejected"}: {String.ofList (e.newText.trimAscii.toString.toList.reverse.take 120).reverse}"
      if ok then
        out := out.push e
        break
  let projs := (if rules.contains "shortProjection" then shortProjections input cmd else #[]).filter fun e =>
    !out.any fun o => o.range.start < e.range.stop && e.range.start < o.range.stop
  unless projs.isEmpty do
    let kept ← Combine.check input map cmd pctx ctx before after projs (shorter := true) (trials := 5)
    out := out ++ kept.map (projs[·]!)
  return out

end LeanPerf.Golf
