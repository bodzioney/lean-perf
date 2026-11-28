import LeanPerf.Signature

open Lean Elab

namespace LeanPerf.Prune

private structure Uses where
  names : Std.HashMap Name Nat := {}
  haves : Array (Name × Syntax.Range) := #[]

/-- A single written occurrence nominates a named `have` for removal. Tactics can use a fact
    without naming it, so only elaborating the remaining proof can confirm a deletion. -/
private partial def collect (stx : Syntax) (s : Uses) : Uses := Id.run do
  if stx.isIdent then
    return { s with names := s.names.alter stx.getId.getRoot fun n => some (n.getD 0 + 1) }
  let id? := match stx with
    | `(tactic| have $id:ident : $_:term := $_:term) => some id
    | `(tactic| have $id:ident := $_:term) => some id
    | _ => none
  let mut s := s
  if let (some id, some r) := (id?, stx.getRange? (canonicalOnly := true)) then
    s := { s with haves := s.haves.push (id.getId, r) }
  for child in stx.getArgs do s := collect child s
  return s

/-- The lines that `r` occupies, when nothing else shares them and no comment is involved. -/
def wholeLines? (input : String) (map : FileMap) (r : Syntax.Range) : Option Syntax.Range := do
  let start := map.ofPosition { map.toPosition r.start with column := 0 }
  let stop := map.ofPosition { line := (map.toPosition r.stop).line + 1, column := 0 }
  guard (String.Pos.Raw.extract input start r.start).trimAscii.isEmpty
  guard (String.Pos.Raw.extract input r.stop stop).trimAscii.isEmpty
  let block := String.Pos.Raw.extract input start stop
  guard (!block.contains "--" && !block.contains "/-")
  return ⟨start, stop⟩

private def removeRanges (input : String) (r : Syntax.Range) (drops : Array Syntax.Range) : String := Id.run do
  let mut out := ""
  let mut cursor := r.start
  for d in drops.qsort (·.start < ·.start) do
    if d.start < cursor then continue
    out := out ++ String.Pos.Raw.extract input cursor d.start
    cursor := d.stop
  return out ++ String.Pos.Raw.extract input cursor r.stop

/-- Whether a rewritten theorem still states the same thing: by default the same exported type,
    including binder names, and the same universe parameters. -/
abbrev Accept := Environment → TheoremVal → TheoremVal → IO Bool

def sameType : Accept := fun _ old new =>
  pure (old.type.equal new.type && old.levelParams == new.levelParams)

/-- The deletions from `candidates` that a theorem survives together with `fixed`. Try the whole
    group; on failure, bisect it and recheck each half with everything accepted so far. The
    rewritten theorem must satisfy `accept`, and its proof must contain no `sorry`. -/
def deletions (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (ctx : Command.Context) (before after : Command.State) (candidates : Array Syntax.Range)
    (fixed : Array Syntax.Range := #[]) (trials := 7) (accept : Accept := sameType) :
    IO (Array Syntax.Range) := do
  if candidates.isEmpty then return #[]
  let some cmd := Signature.asTheorem? cmd | return #[]
  let some name := Signature.theoremName? cmd[1] before after | return #[]
  let some (.thmInfo old) := after.env.find? name | return #[]
  let some r := cmd.getRange? | return #[]
  let r := { r with start := map.ofPosition { map.toPosition r.start with column := 0 } }
  let probe := { before with messages := {}, infoState := { enabled := false } }
  let mut accepted := #[]
  let mut todo := #[candidates]
  for _ in [:trials] do
    let some group := todo.back? | break
    todo := todo.pop
    let ictx := Parser.mkInputContext (removeRanges input r (fixed ++ accepted ++ group)) ctx.fileName
    let (next, ps, msgs) := Parser.parseCommand ictx pctx {} {}
    let (eof, _, msgs) := Parser.parseCommand ictx pctx ps msgs
    if !msgs.hasErrors && Parser.isTerminalCommand eof then
      let c := { ctx with fileMap := ictx.fileMap, cmdPos := 0 }
      if let .ok ((), s) ← ((Command.elabCommandTopLevel next).run c |>.run probe).toIO' then
        if let some (.thmInfo new) := s.env.find? name then
          if !s.messages.hasErrors && !new.value.hasSorry && (← accept s.env old new) then
            accepted := accepted ++ group
            continue
    if group.size > 1 then
      let mid := group.size / 2
      todo := (todo.push (group.extract mid group.size)).push (group.extract 0 mid)
  return accepted

/-- Remove named local proofs that nothing names. The returned proof is a single edit so
    competing suggestions cannot introduce references to locals it removes. -/
def proof? (input : String) (map : FileMap) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (ctx : Command.Context) (before after : Command.State) : IO (Option Lsp.TextEdit) := do
  let some thm := Signature.asTheorem? cmd | return none
  let d := thm[1]
  unless d[3].isOfKind ``Parser.Command.declValSimple do return none
  let proof := d[3][1]
  unless proof.isOfKind ``Parser.Term.byTactic do return none
  let some pr := proof.getRange? | return none
  let used := collect proof {}
  let candidates := used.haves.filterMap fun (n, r) => do
    guard (used.names[n]? == some 1)
    let span ← wholeLines? input map r
    guard (pr.start ≤ span.start && span.stop ≤ pr.stop)
    return span
  let accepted ← deletions input map cmd pctx ctx before after candidates
  if accepted.isEmpty then return none
  return some { range := map.utf8RangeToLspRange pr, newText := removeRanges input pr accepted }

end LeanPerf.Prune
