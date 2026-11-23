import Lean

open Lean Elab Meta

namespace LeanPerf.Signature

/-- Remove only parsed universe suffixes, retaining all intervening user text. -/
private partial def universeRanges (stx : Syntax) : Array Syntax.Range := Id.run do
  if stx.isOfKind ``Parser.Term.explicitUniv then
    if let (some a, some b) := (stx[0].getTailPos?, stx.getTailPos?) then return #[⟨a, b⟩]
  let mut spans := #[]
  for child in stx.getArgs do spans := spans ++ universeRanges child
  return spans

private def dropUniverses (input : String) (range : Syntax.Range) (type : Syntax) : String := Id.run do
  let mut cursor := range.start
  let mut text := ""
  for r in universeRanges type do
    text := text ++ String.Pos.Raw.extract input cursor r.start
    cursor := r.stop
  return text ++ String.Pos.Raw.extract input cursor range.stop

/-- Print the result type in the context of the written declaration binders. -/
private def renderTypes (trees : PersistentArray InfoTree) (range : Syntax.Range) : IO (Array String) := do
  let mut texts := #[]
  for tree in trees do
    let hits := tree.foldInfo (init := #[]) fun ci info acc => Id.run do
      let .ofTermInfo ti := info | return acc
      unless ti.stx.getRange? (canonicalOnly := true) == some range do return acc
      return acc.push (ci, ti)
    for (ci, ti) in hits do
      let printed ← ci.runMetaM ti.lctx do
        let ty ← instantiateMVars ti.expr
        if ty.hasMVar then return #[]
        let mut variants := #[]
        for (hideCoercions, showTypes) in [(true, false), (true, true), (false, true)] do
          let options (o : Options) := o.setBool `pp.universes false |>.setBool `pp.piBinderNames true
            |>.setBool `pp.piBinderTypes true |>.setBool `pp.funBinderTypes showTypes
            |>.setBool `pp.coercions hideCoercions |>.setBool `pp.coercions.types showTypes
          try variants := variants.push ((← withOptions options (ppExpr ty)).pretty 100)
          catch _ => pure ()
        return variants
      for t in printed do
        unless texts.contains t do texts := texts.push t
  return texts

/-- Re-elaborate the proposed declaration in its original scope and require structural equality
    of the exported theorem type, including binder names, plicity and the order of universes. -/
def compress (input : String) (map : FileMap) (cmd : Syntax) (ctx : Command.Context)
    (before after : Command.State) : IO (Option Lsp.TextEdit) := do
  unless cmd.isOfKind ``Parser.Command.declaration do return none
  let d := cmd[1]
  unless d.isOfKind ``Parser.Command.theorem do return none
  let sig := d[2]
  let spec := sig[1]
  let ty := spec[1]
  let some r := ty.getRange? | return none
  let original := String.Pos.Raw.extract input r.start r.stop
  unless original.contains ".{" || original.contains "DFunLike.coe" || original.contains "Membership.mem" ||
      original.contains "@" do return none
  if original.contains "/-" || original.contains "--" then return none
  let id := d[1][0].getId
  let full := if id.getRoot == `_root_ then id.replacePrefix `_root_ .anonymous
    else before.scopes.head!.currNamespace ++ id
  let some name := [full, mkPrivateName after.env full].find? (fun n => !before.env.contains n && after.env.contains n)
    | return none
  let some (.thmInfo old) := after.env.find? name | return none
  let texts ← renderTypes after.infoState.trees r
  let pos := map.toPosition r.start
  let line := String.Pos.Raw.extract input (map.ofPosition { pos with column := 0 }) r.start
  let indent := (line.takeWhile (· == ' ')).toString ++ (if line.trimAscii.isEmpty then "" else "  ")
  let variants := texts.map fun t => ("\n" ++ indent).intercalate (t.splitOn "\n")
  let variants := (variants.push (dropUniverses input r ty)).qsort (·.utf8ByteSize < ·.utf8ByteSize)
  for text in variants do
    if text.utf8ByteSize ≥ original.utf8ByteSize then continue
    let .ok parsed := Parser.runParserCategory before.env `term text | continue
    let d' := d.setArg 2 (sig.setArg 1 (spec.setArg 1 parsed))
    let probe := { before with messages := {}, infoState := { enabled := false } }
    let .ok ((), checked) ← ((Command.elabCommandTopLevel (cmd.setArg 1 d')).run ctx |>.run probe).toIO' | continue
    if checked.messages.hasErrors then continue
    let some (.thmInfo new) := checked.env.find? name | continue
    if old.levelParams == new.levelParams && old.type.equal new.type then
      return some { range := map.utf8RangeToLspRange r, newText := text }
  return none

end LeanPerf.Signature
