import LeanPerf.Edit
import LeanPerf.Instances
import LeanPerf.Steps

/-!
# Edits to one command, checked together

Each lint checks its own edit against the original command: a replayed step leaves the same goals,
or the command elaborates to the same type with that edit alone. Two edits that are each correct
can still conflict. A `restatedType` deletion can change a hypothesis by an instance path that a
faster tactic later in the proof then fails to match. So when a command has more than one edit that
the source rewrite would select, the command is elaborated with all of them. On failure the group
is split and each half rechecked with the edits accepted so far, as for `unusedHave`. A failing
whole-module check would otherwise discard every edit in the file.
-/

open Lean Elab

namespace LeanPerf.Combine

/-- The edit deletes instance binders, which changes the exported type by design. -/
private def dropsInstances (e : Edit) : Bool := e.rule == "unusedInstance"

/-- What the edit is worth: steps and declarations first, then bytes. -/
private def saving (e : Edit) : Int :=
  Steps.worth e.gain ((e.range.stop.byteIdx - e.range.start.byteIdx : Int) - e.newText.utf8ByteSize)

/-- The edits the source rewrite applies: with `shorter`, a set of disjoint edits worth the most (steps
    and declarations taken out, then bytes); otherwise an edit unless an earlier one contains it.
    Returns indices in source order. -/
def select (edits : Array Edit) (shorter : Bool) : Array Nat := Id.run do
  let idx := (Array.range edits.size).qsort fun i j =>
    let a := edits[i]!.range
    let b := edits[j]!.range
    a.start < b.start || (a.start == b.start && b.stop < a.stop)
  if !shorter then
    let mut out := #[]
    let mut stop : String.Pos.Raw := 0
    for i in idx do
      if out.isEmpty || stop ≤ edits[i]!.range.start then
        out := out.push i
        stop := edits[i]!.range.stop
    return out
  let byStop := (idx.filter (saving edits[·]! > 0)).qsort fun i j => edits[i]!.range.stop < edits[j]!.range.stop
  return bestDisjoint byStop (edits[·]!.range.start.byteIdx) (edits[·]!.range.stop.byteIdx) (saving edits[·]!)

private def applyTo (input : String) (r : Syntax.Range) (edits : Array Edit) : String := Id.run do
  let mut out := ""
  let mut cursor := r.start
  for e in edits.qsort (·.range.start < ·.range.start) do
    if e.range.start < cursor then continue
    out := out ++ String.Pos.Raw.extract input cursor e.range.start ++ e.newText
    cursor := e.range.stop
  return out ++ String.Pos.Raw.extract input cursor r.stop

/-- Whether the rewritten command declares what the original did. A theorem whose instance
    binders an edit deletes may lose exactly those binders. -/
private def sameDecls (before after new : Environment) (dropping : Bool) : IO Bool := do
  for (n, c) in after.constants.map₂.toList do
    if before.contains n || Replay.generated n then continue
    let some c' := new.find? n | return false
    if c'.levelParams != c.levelParams then return false
    if let .thmInfo t := c' then if t.value.hasSorry then return false
    if c.type.equal c'.type then continue
    unless dropping do return false
    let check := (Instances.dropsInstances c.type c'.type).run' {} {}
    unless ← (try check.toIO' { fileName := "<leanperf>", fileMap := default, maxHeartbeats := 0 } { env := new }
        catch _ => pure false) do return false
  return true

/-- The indices of `edits` to keep for `cmd`: the selected edits, or the largest group found by
    splitting them when they fail together. -/
def check (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (ctx : Command.Context) (before after : Command.State) (edits : Array Edit) (shorter : Bool)
    (trials := 7) : IO (Array Nat) := do
  let chosen := select edits shorter
  if chosen.isEmpty then return chosen
  let some cr := cmd.getRange? | return #[]
  let first := chosen.foldl (fun p i => if edits[i]!.range.start < p then edits[i]!.range.start else p) cr.start
  let r : Syntax.Range := ⟨map.ofPosition { map.toPosition first with column := 0 }, cr.stop⟩
  let probe := { before with messages := {}, infoState := { enabled := false } }
  let works (group : Array Nat) : IO Bool := do
    let ictx := Parser.mkInputContext (applyTo input r (group.map (edits[·]!))) ctx.fileName
    let (next, ps, msgs) := Parser.parseCommand ictx pctx {} {}
    let (eof, _, msgs) := Parser.parseCommand ictx pctx ps msgs
    unless !msgs.hasErrors && Parser.isTerminalCommand eof do return false
    let c := { ctx with fileMap := ictx.fileMap, cmdPos := 0 }
    let .ok ((), s) ← ((Command.elabCommandTopLevel next).run c |>.run probe).toIO' | return false
    if s.messages.hasErrors then return false
    sameDecls before.env after.env s.env (group.any (dropsInstances edits[·]!))
  if ← works chosen then return chosen
  let mut accepted := #[]
  let mut todo := #[chosen]
  for _ in [:trials] do
    let some group := todo.back? | break
    todo := todo.pop
    if ← works (accepted ++ group) then
      accepted := accepted ++ group
      continue
    if group.size > 1 then
      let mid := group.size / 2
      todo := (todo.push (group.extract mid group.size)).push (group.extract 0 mid)
  return accepted

end LeanPerf.Combine
