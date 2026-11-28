import LeanPerf.Propose

/-!
# Folding helper lemmas into the theorem that uses them

Most of the difference between the readable and the compact edition of the Riemann development is
declarations, not proof length: 57% of the readable edition's theorem lines are in lemmas used only
in their own file, and the lemmas the compact edition lacks mostly had one caller. A lemma that only
one theorem of its module uses, and that no other module mentions, is not part of the module's
interface. Folding it into its user as a local `have` keeps the user's statement and drops the
lemma's name, docstring and declaration.

`foldHelper` does this for the groups of `Propose.groups`: a theorem with the helpers right above
it. Each helper's binders, statement and proof are copied verbatim into a `have` at the start of
its user's proof, re-indented, and the user's references to it name the `have`. Lean then checks
the whole group as it checks a proposer's rewrite: the kept theorems have their statements and
docstrings, nothing new is declared, and the proof is not slower than twice the original.
-/

open Lean Elab

namespace LeanPerf.Fold

private partial def nodes (p : Syntax → Bool) (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if p stx then acc.push stx else acc
  stx.getArgs.foldl (fun acc a => nodes p a acc) acc

private def range? (stx : Syntax) : Option Syntax.Range := stx.getRange? (canonicalOnly := true)

private def text (input : String) (r : Syntax.Range) : String := String.Pos.Raw.extract input r.start r.stop

/-- `t` with `n` more spaces at the start of every line but the first. -/
private def shift (t : String) (n : Nat) : String :=
  let pad := String.ofList (List.replicate n ' ')
  match t.splitOn "\n" with
  | [] => t
  | first :: rest => "\n".intercalate (first :: rest.map fun l => if l.trimAscii.isEmpty then l else pad ++ l)

/-- The column of byte `p`. -/
private def column (map : FileMap) (p : String.Pos.Raw) : Nat := (map.toPosition p).column

/-- Whether a helper can be a `have`: no attributes, universe parameters, `where` or
    `termination_by`, and no comments after its name. The byte where its name ends. -/
private def foldable? (input : String) (cmd : Syntax) : Option String.Pos.Raw := do
  let thm ← Signature.asTheorem? cmd
  let d := thm[1]
  guard (cmd[0][1].getNumArgs == 0)
  let declId := d[1]
  guard (declId[1].getNumArgs == 0)
  let val := d[3]
  guard (val.isOfKind ``Parser.Command.declValSimple)
  guard (val[2].getNumArgs == 0 || (range? val[2]).isNone)
  guard (val.getNumArgs < 4 || val[3].getNumArgs == 0)
  let idr ← range? declId
  let cr ← range? cmd
  let rest := String.Pos.Raw.extract input idr.stop cr.stop
  guard (!rest.contains "--" && !rest.contains "/-")
  return idr.stop

/-- Whether identifier `x` names `full`: by a suffix of its components that ends at its last one,
    followed only by field names. The number of components that name it. -/
private def refersTo (x : Syntax) (full : Name) : Option Nat := do
  let cs := x.getId.components
  let fs := full.components
  let some last := fs.getLast? | none
  let some k := cs.findIdx? (· == last) | none
  let pre := cs.take (k + 1)
  guard (pre.length ≤ fs.length && fs.drop (fs.length - pre.length) == pre)
  return k + 1

/-- The index, among the explicit arguments of a helper, of the first whose type is named by the
    helper's namespace: the argument that `x.helper` passes `x` as. -/
private def receiverIndex? (cmd : Syntax) (full : Name) : Option Nat := do
  let thm ← Signature.asTheorem? cmd
  let ns ← (full.components.dropLast.filter fun c => !c.isNum && !c.toString.startsWith "_").getLast?
  let mut k := 0
  for b in thm[1][2][0].getArgs do
    unless b.isOfKind ``Parser.Term.explicitBinder do continue
    let names := b[1].getArgs.size
    -- `(x y : T)`: the type follows the colon.
    let ty := b[2][1]
    let head := if ty.isOfKind ``Parser.Term.app then ty[0] else ty
    if head.isIdent && head.getId.components.getLast? == some ns then return k
    k := k + names
  none

/-- How identifier `x` names a helper `full`: plainly, by a suffix of the full name (`some none`),
    or by dot notation on a receiver, the text before the last dot (`some (some receiver)`). -/
private def reference? (input : String) (x : Syntax) (full : Name) : Option (Option String) := do
  let some last := full.components.getLast? | none
  let cs := x.getId.components
  guard (cs.getLast? == some last)
  if (refersTo x full).isSome then return none
  let r ← range? x
  let t := text input r
  let cut := t.utf8ByteSize - last.toString.utf8ByteSize - 1
  guard (cut > 0)
  return some (String.Pos.Raw.extract t 0 ⟨cut⟩)

/-- The implicit and instance binders of a signature, one entry per name: the binder's kind, the
    name (empty for an anonymous instance) and the type with its whitespace collapsed. -/
private def implicits (input : String) (sig : Syntax) : Array (Syntax × String × String × String) := Id.run do
  let norm (t : String) := " ".intercalate ((t.splitOn " ").filter (!·.isEmpty) |>.map (·.trimAscii.toString))
  let mut out := #[]
  for b in sig[0].getArgs do
    let kind := b.getKind.toString
    if b.isOfKind ``Parser.Term.instBinder then
      let some tr := range? b[2] | continue
      let name := if b[1].getNumArgs > 0 then b[1][0].getId.toString else ""
      out := out.push (b, kind, name, norm ((text input tr).replace "\n" " "))
    else if b.isOfKind ``Parser.Term.implicitBinder || b.isOfKind ``Parser.Term.strictImplicitBinder then
      let some tr := range? b[2][1] | continue
      for x in b[1].getArgs do
        out := out.push (b, kind, x.getId.toString, norm ((text input tr).replace "\n" " "))
  return out

/-- Edits to a helper's signature that drop the implicit and instance binders the theorem binds
    the same way, so that the `have` uses the theorem's variables. Explicit binders stay, so that
    every use passes the same arguments. -/
private def sharedBinders (input : String) (helper anchor : Syntax) : Array (Syntax.Range × String) := Id.run do
  let some ht := Signature.asTheorem? helper | return #[]
  let some at_ := Signature.asTheorem? anchor | return #[]
  let theirs := (implicits input at_[1][2]).map fun (_, k, n, t) => (k, n, t)
  let mine := implicits input ht[1][2]
  let mut out := #[]
  -- The names the helper itself still binds: a binder whose type mentions one of them stays,
  -- since its type is about the helper's variable, not the theorem's.
  let mut own : Std.HashSet String := {}
  for b in ht[1][2][0].getArgs do
    let entries := mine.filter fun (x, _, _, _) => x.getRange? == b.getRange?
    let typeNames := (nodes (·.isIdent) (if b.isOfKind ``Parser.Term.instBinder then b[2] else b[2]))
      |>.filterMap (·.getId.components.head?.map (·.toString))
    let mentionsOwn := typeNames.any own.contains
    if entries.isEmpty then
      -- An explicit binder: its names are the helper's own.
      for x in nodes (·.isIdent) b[1] do own := own.insert x.getId.toString
      continue
    let kept := entries.filter fun (_, k, n, t) => mentionsOwn || !theirs.contains (k, n, t)
    for (_, _, n, _) in kept do
      unless n.isEmpty do own := own.insert n
    if kept.size == entries.size then continue
    let some br := range? b | continue
    -- The binder goes with the space before it.
    let mut s := br.start.byteIdx
    let bytes := input.toUTF8
    while s > 0 && (bytes[s-1]! == ' '.toUInt8) do s := s - 1
    if kept.isEmpty then
      out := out.push (⟨⟨s⟩, br.stop⟩, "")
    else
      let some tr := range? b[2][1] | continue
      let (l, r) := if b.isOfKind ``Parser.Term.implicitBinder then ("{", "}") else ("⦃", "⦄")
      out := out.push (⟨⟨s⟩, br.stop⟩, s!" {l}{" ".intercalate (kept.toList.map (·.2.2.1))} : {text input tr}{r}")
  return out

/-- The explicit binders of a theorem, one entry per name: the binder, its index among the
    explicit arguments, the name and the type with its whitespace collapsed. -/
private def explicits (input : String) (thm : Syntax) : Array (Syntax × Nat × String × String) := Id.run do
  let norm (t : String) := " ".intercalate ((t.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty))
  let mut out := #[]
  let mut i := 0
  for b in thm[1][2][0].getArgs do
    unless b.isOfKind ``Parser.Term.explicitBinder do continue
    let ty := (range? b[2][1]).map (text input) |>.getD ""
    for x in b[1].getArgs do
      out := out.push (b, i, x.getId.toString, norm ty)
      i := i + 1
  return out

/-- Explicit binders of helper `k` that the theorem `b` binds the same way and that every use of the
    helper, all in `b`, passes the variable of that name: they can go from the `have` and from each
    use. The edits to the helper's signature and to the uses, or none. -/
private def sharedExplicits (input : String) (helper anchor : Syntax) (full : Name) :
    Array (Syntax.Range × String) := Id.run do
  let some ht := Signature.asTheorem? helper | return #[]
  let some at_ := Signature.asTheorem? anchor | return #[]
  let theirs := (explicits input at_).map fun (_, _, n, t) => (n, t)
  let mine := (explicits input ht).filter fun (_, _, n, t) => theirs.contains (n, t)
  if mine.isEmpty then return #[]
  -- Every use: a plain application of the helper with the variable at each dropped position.
  let uses := nodes (fun x => x.isIdent && (reference? input x full).isSome) anchor
  let mut drop := mine
  let mut argEdits : Array (Syntax.Range × String) := #[]
  for x in uses do
    unless (reference? input x full) == some none do return #[]
    let some ap := (nodes (fun s => s.isOfKind ``Parser.Term.app && s[0].getRange? == x.getRange?) anchor)[0]?
      | return #[]
    let args := ap[1].getArgs
    if args.any (·.isOfKind ``Parser.Term.namedArgument) then return #[]
    drop := drop.filter fun (_, i, n, _) => (args[i]?).any fun a => a.isIdent && a.getId.toString == n
  if drop.isEmpty then return #[]
  let bytes := input.toUTF8
  let back (p : String.Pos.Raw) : String.Pos.Raw := Id.run do
    let mut s := p.byteIdx
    while s > 0 && bytes[s-1]! == ' '.toUInt8 do s := s - 1
    return ⟨s⟩
  for x in uses do
    let some ap := (nodes (fun s => s.isOfKind ``Parser.Term.app && s[0].getRange? == x.getRange?) anchor)[0]?
      | return #[]
    let args := ap[1].getArgs
    -- An application left with no arguments is the bare name.
    for (_, i, _, _) in drop do
      let some a := args[i]? | return #[]
      let some r := range? a | return #[]
      argEdits := argEdits.push (⟨back r.start, r.stop⟩, "")
  -- The binders: a group whose names all go is deleted, else written with the names that stay.
  let mut sigEdits := #[]
  for b in ht[1][2][0].getArgs do
    unless b.isOfKind ``Parser.Term.explicitBinder do continue
    let names := b[1].getArgs.map (·.getId.toString)
    let gone := names.filter fun n => drop.any fun (x, _, m, _) => x.getRange? == b.getRange? && m == n
    if gone.isEmpty then continue
    let some br := range? b | continue
    if gone.size == names.size then sigEdits := sigEdits.push (⟨back br.start, br.stop⟩, "")
    else
      let some tr := range? b[2][1] | continue
      let kept := names.filter (!gone.contains ·)
      sigEdits := sigEdits.push (⟨back br.start, br.stop⟩, s!" ({" ".intercalate kept.toList} : {text input tr})")
  return sigEdits ++ argEdits

/-- The text that replaces commands `a` to `b` (see `Propose.span`), helpers that only later
    commands of the group use followed by the theorem `b`, with every helper a `have` at the start
    of the theorem's proof, in order. References to a helper, plain or by dot notation, name its
    `have`. An error says why a group cannot be folded. -/
def fold (input : String) (map : FileMap) (records : Array Propose.Record) (a b : Nat) (free : Array Name)
    : Except String String := do
  let cmdAt (k : Nat) : Syntax := (records[k]?.map (·.cmd)).getD .missing
  let nameOf (k : Nat) : Option Name := do
    let r ← records[k]?
    let thm ← Signature.asTheorem? r.cmd
    Signature.theoremName? thm[1] r.before r.after
  -- The helpers among commands `a` to `b - 1`; the others stay as they are.
  let mut helpers : Array (Nat × Name × String.Pos.Raw × String) := #[]
  let mut taken : Std.HashSet String := {}
  for k in [a:b+1] do
    for x in nodes (·.isIdent) (cmdAt k) do
      for c in x.getId.components do taken := taken.insert c.toString
  for k in [a:b] do
    let some n := nameOf k | continue
    unless free.contains n do continue
    let some nameEnd := foldable? input (cmdAt k) | throw s!"{n} cannot be a have"
    let some nm := ([s!"h{k - a}", s!"h{k - a}'"] ++ ("abcdefghijklmnopqrstuvwxyz".toList.map (·.toString))).find?
      (!taken.contains ·) | throw "no free name"
    taken := taken.insert nm
    helpers := helpers.push (k, n, nameEnd, nm)
  if helpers.isEmpty then throw "no helper"
  -- The source of command `j` with references to helpers renamed.
  let renamed (j : Nat) (start : String.Pos.Raw) : Except String String := do
    let cmd := cmdAt j
    let some cr := range? cmd | throw "no range"
    let mut repl : Array (Syntax.Range × String) := if j < b then sharedBinders input cmd (cmdAt b) else #[]
    -- Explicit binders the theorem shares: from the helper's signature and from its uses there.
    for (k, n, _, _) in helpers do
      let edits := sharedExplicits input (cmdAt k) (cmdAt b) n
      let some kr := range? (cmdAt k) | continue
      let some br := range? (cmdAt b) | continue
      for (r, t) in edits do
        if (j == k && kr.start ≤ r.start && r.stop ≤ kr.stop) || (j == b && br.start ≤ r.start && r.stop ≤ br.stop) then
          repl := repl.push (r, t)
    for (k, n, _, nm) in helpers do
      if k ≥ j then continue
      for x in nodes (·.isIdent) cmd do
        let some how := reference? input x n | continue
        let some r := range? x | continue
        match how with
        | none => repl := repl.push (r, nm)
        | some recv =>
          -- A receiver that is not an argument of the helper is a section variable, which the
          -- `have` takes from the theorem's context.
          let some i := receiverIndex? (cmdAt k) n
            | repl := repl.push (r, nm); continue
          -- `recv.helper args` is `nm args` with `recv` among them, at the receiver's place.
          let app := (nodes (fun s => s.isOfKind ``Parser.Term.app && s[0].getRange? == x.getRange?) cmd)[0]?
          match app with
          | none =>
            if i != 0 then throw s!"{n} by dot notation, unapplied"
            repl := repl.push (r, s!"({nm} {recv})")
          | some ap =>
            let args := ap[1].getArgs
            if i == 0 then repl := repl.push (r, s!"{nm} {recv}")
            else
              let some prev := args[i - 1]? | throw s!"{n} by dot notation with too few arguments"
              let some pr := range? prev | throw "no range"
              repl := repl.push (r, nm)
              repl := repl.push (⟨pr.stop, pr.stop⟩, s!" {recv}")
    let mut out := ""
    let mut p := start
    for (r, t) in repl.qsort (fun x y => x.1.start < y.1.start || (x.1.start == y.1.start && x.1.stop < y.1.stop)) do
      if r.start < p then throw "overlapping references"
      out := out ++ String.Pos.Raw.extract input p r.start ++ t
      p := r.stop
    return out ++ String.Pos.Raw.extract input p cr.stop
  -- The theorem's proof: a tactic block takes the `have`s as its first steps; a term becomes one.
  let anchor := cmdAt b
  let some cr := range? anchor | throw "no range"
  let some thm := Signature.asTheorem? anchor | throw "the last command is not a theorem"
  let val := thm[1][3]
  unless val.isOfKind ``Parser.Command.declValSimple do throw "the theorem has no simple value"
  let term := val[1]
  let some tr := range? term | throw "no range"
  let isBy := term.isOfKind ``Parser.Term.byTactic
  let seq := if isBy then (nodes (·.isOfKind ``Parser.Tactic.tacticSeq1Indented) term)[0]? else none
  let (insertAt, indent) := match seq.bind range? with
    | some r => (r.start, column map r.start)
    | none => (tr.start, 2)
  let pad := String.ofList (List.replicate indent ' ')
  let mut haves := ""
  for (k, _, nameEnd, nm) in helpers do
    let some hr := range? (cmdAt k) | throw "no range"
    let src ← renamed k hr.start
    -- The helper after its name: binders, statement and proof.
    let body := (src.drop (String.Pos.Raw.extract input hr.start nameEnd).length).toString
    -- Lines that dropped binders leave empty go.
    let body := "\n".intercalate ((body.splitOn "\n").filter (!·.trimAscii.isEmpty))
    -- `Type*` makes a lemma universe polymorphic but gives a `have` a fixed new universe, which
    -- its use cannot match; `Type _` leaves the universe to the use.
    let body := (body.replace "Type*" "Type _").replace "Sort*" "Sort _"
    haves := haves ++ s!"have {nm}" ++ shift body indent ++ "\n" ++ pad
  let lead := if isBy then haves else "by\n" ++ pad ++ haves ++ "exact "
  let whole ← renamed b cr.start
  -- `insertAt` in the renamed text: renaming happens only after it in a proof, or before it in the
  -- statement, which never names a helper.
  let offset := (String.Pos.Raw.extract input cr.start insertAt).length
  let anchorText := (whole.take offset).toString ++ lead ++ (whole.drop offset).toString
  -- The span without the helpers, each with the text after it; the other commands as they are.
  let mut out := ""
  for j in [a:b+1] do
    let some jr := range? (cmdAt j) | throw "no range"
    let isHelper := helpers.any (·.1 == j)
    if j == b then out := out ++ anchorText
    else if !isHelper then
      let some nr := range? (cmdAt (j + 1)) | throw "no range"
      out := out ++ String.Pos.Raw.extract input jr.start nr.start
  return out

/-- Groups to fold: a theorem with the theorems of its module that only it uses, directly or
    through one another, and that no other module mentions (`external` holds the last name
    components other modules mention). A use is an identifier in a command, so a docstring that
    names a helper does not keep it. Each group is `(a, b, keep, free)`: commands `a` to `b`, the
    theorems among them that stay, and the helpers. At most `maxSpan` commands. -/
def groups (records : Array Propose.Record) (external : Std.HashSet String) (maxSpan := 16) :
    Array (Nat × Nat × Array Name × Array Name) := Id.run do
  let n := records.size
  let info := records.map fun r =>
    let name := (Signature.asTheorem? r.cmd).bind fun t => Signature.theoremName? t[1] r.before r.after
    let attributed : Bool := r.cmd[0][1].getNumArgs > 0
    let comps := (nodes (·.isIdent) r.cmd).foldl (init := ({} : Std.HashSet String)) fun acc x =>
      x.getId.components.foldl (fun acc c => acc.insert c.toString) acc
    (name, attributed, comps)
  let last (k : Nat) : Option String := info[k]!.1.bind (·.componentsRev.head?.map (·.toString))
  -- The commands that use each theorem.
  let users (k : Nat) : Array Nat := Id.run do
    let some l := last k | return #[]
    return (Array.range n).filter fun j => j != k && info[j]!.2.2.contains l
  let mut out := #[]
  let mut claimed : Std.HashSet Nat := {}
  let mut u := n
  while u > 0 do
    u := u - 1
    if claimed.contains u then continue
    let some anchor := info[u]!.1 | continue
    -- Helpers of `u`: theorems used only by `u` and by other helpers of `u`, found from `u` back.
    let mut helps : Array Nat := #[]
    let mut changed := true
    while changed do
      changed := false
      for k in (List.range u).reverse do
        if helps.contains k || claimed.contains k || u - k + 1 > maxSpan then continue
        let some l := last k | continue
        if info[k]!.2.1 || external.contains l then continue
        let us := users k
        if !us.isEmpty && us.all (fun j => j == u || helps.contains j) then
          helps := helps.push k
          changed := true
    if helps.isEmpty then continue
    let a := helps.foldl min u
    let free := helps.filterMap (info[·]!.1)
    let keep := ((List.range (u - a + 1)).map (a + ·)).toArray.filter (!helps.contains ·) |>.filterMap (info[·]!.1)
    out := out.push (a, u, keep.push anchor |>.toList.eraseDups.toArray, free)
    for k in [a:u+1] do claimed := claimed.insert k
  return out.reverse

/-- The theorem that command `k` declares. -/
def nameAt (records : Array Propose.Record) (k : Nat) : Option Name := do
  let r ← records[k]?
  let thm ← Signature.asTheorem? r.cmd
  Signature.theoremName? thm[1] r.before r.after

/-- Wrappers to merge: a theorem `w` whose proof only applies another theorem `t` of its module,
    in the same namespace, that no other module mentions. `t`'s proof can move to `w`, which then
    takes `t`'s place everywhere in the module. Each is `(t, w, last, keep)`: the span from `t` to
    `last`, the last command that names `t` or `w`, and the theorems in it that stay. At most
    `maxSpan` commands. -/
def wrappers (input : String) (records : Array Propose.Record) (external : Std.HashSet String) (maxSpan := 24) :
    Array (Nat × Nat × Nat × Array Name) := Id.run do
  let n := records.size
  let nameOf (k : Nat) : Option Name := do
    let r ← records[k]?
    let thm ← Signature.asTheorem? r.cmd
    Signature.theoremName? thm[1] r.before r.after
  let cmdAt (k : Nat) : Syntax := (records[k]?.map (·.cmd)).getD .missing
  let mut out := #[]
  for w in [:n] do
    let some wn := nameOf w | continue
    let some thm := Signature.asTheorem? (cmdAt w) | continue
    let val := thm[1][3]
    unless val.isOfKind ``Parser.Command.declValSimple do continue
    let some vr := range? val[1] | continue
    if (text input vr).utf8ByteSize > 160 then continue
    -- The head of the proof term: `t args` or `x.t args`.
    let head := if val[1].isOfKind ``Parser.Term.app then val[1][0] else val[1]
    unless head.isIdent do continue
    let some t := (List.range w).find? fun k => (nameOf k).any fun tn =>
      tn.componentsRev.head? == head.getId.componentsRev.head? && tn.getPrefix == wn.getPrefix
      | continue
    let some tn := nameOf t | continue
    let some tl := tn.componentsRev.head? | continue
    if external.contains tl.toString then continue
    if (cmdAt t)[0][1].getNumArgs > 0 then continue
    -- `w` must bind the names `t`'s proof uses: the same explicit binder names, in order.
    let explicitNames (k : Nat) : Array String := match Signature.asTheorem? (cmdAt k) with
      | some th => th[1][2][0].getArgs.foldl (init := #[]) fun acc b =>
        if b.isOfKind ``Parser.Term.explicitBinder then acc ++ b[1].getArgs.map (·.getId.toString) else acc
      | none => #[]
    unless explicitNames t == explicitNames w do continue
    -- The commands that name `t`, also with fields after it, as in `t.mp`.
    let users := (List.range n).filter fun j => j != t &&
      (nodes (fun x => x.isIdent && x.getId.components.contains tl) (cmdAt j)).size > 0
    let last := users.foldl max w
    if last - t + 1 > maxSpan then continue
    let keep := ((List.range (last - t + 1)).map (t + ·)).filter (· != t) |>.filterMap nameOf
    out := out.push (t, w, last, keep.toArray)
  return out

/-- The text from command `t` to `last` with `t`'s proof as the proof of `w`, `t` deleted, and every
    reference to `t` naming `w`, as `t`'s last name component replaced by `w`'s. -/
def mergeWrapper (input : String) (records : Array Propose.Record) (t w last : Nat) : Except String String := do
  let cmdAt (k : Nat) : Syntax := (records[k]?.map (·.cmd)).getD .missing
  let nameOf (k : Nat) : Option Name := do
    let r ← records[k]?
    let thm ← Signature.asTheorem? r.cmd
    Signature.theoremName? thm[1] r.before r.after
  let some tn := nameOf t | throw "no theorem"
  let some wn := nameOf w | throw "no wrapper"
  let some tl := tn.componentsRev.head? | throw "no name"
  let some wl := wn.componentsRev.head? | throw "no name"
  let some tthm := Signature.asTheorem? (cmdAt t) | throw "no theorem"
  let some wthm := Signature.asTheorem? (cmdAt w) | throw "no wrapper"
  let some tv := range? tthm[1][3][1] | throw "no proof"
  let some wv := range? wthm[1][3][1] | throw "no proof"
  let some tr := range? (cmdAt t) | throw "no range"
  let tproof := String.Pos.Raw.extract input tv.start tr.stop
  if tproof.contains "--" || tproof.contains "/-" then throw "the proof has comments"
  let mut out := ""
  for j in [t:last+1] do
    if j == t then continue
    let some jr := range? (cmdAt j) | throw "no range"
    -- The text before command `j`: after the command above it, kept or deleted.
    if j > t + 1 then
      let some pr := range? (cmdAt (j - 1)) | throw "no range"
      out := out ++ String.Pos.Raw.extract input pr.stop jr.start
    let mut repl : Array (Syntax.Range × String) :=
      if j == w then #[(wv, tproof)] else #[]
    for x in nodes (fun x => x.isIdent && x.getId.components.contains tl) (cmdAt j) do
      let some r := range? x | continue
      if j == w && wv.start ≤ r.start && r.stop ≤ wv.stop then continue
      let tx := text input r
      if tx.contains '«' then throw "an escaped reference"
      -- The component that names `t` becomes `w`'s; a namespace before it and fields after it stay.
      let parts := tx.splitOn "."
      let some k := x.getId.components.findIdx? (· == tl) | throw "no component"
      unless parts.length == x.getId.components.length && parts[k]? == some tl.toString do
        throw "a reference is not plain"
      repl := repl.push (r, ".".intercalate (parts.set k wl.toString))
    let mut p := jr.start
    for (r, s) in repl.qsort (·.1.start < ·.1.start) do
      if r.start < p then throw "overlapping edits"
      out := out ++ String.Pos.Raw.extract input p r.start ++ s
      p := r.stop
    out := out ++ String.Pos.Raw.extract input p jr.stop
  return out

end LeanPerf.Fold
