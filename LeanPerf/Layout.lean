import Lean

/-!
# Joining lines

The compact edition of the Riemann development has half as many lines per lemma as the readable
one, and most of the difference is layout. A statement fills each line up to the width limit, a
term continues on the line where it starts, and a block of one tactic sits on the line of its `by`.
This pass joins a line to the one before it when the joined line fits the width and the command
parses to the same syntax tree. The tree is all that Lean elaborates, so the command means the same.

A line with a comment is never joined, nor a blank line. Steps of a tactic block are never put on
one line: that needs a `;`, which changes the tree.
-/

open Lean

namespace LeanPerf.Layout

/-- A source line of a command: where it starts, where its indentation ends and where its text
    ends before trailing spaces, as byte offsets into the file. -/
private structure Line where
  start : Nat
  content : Nat
  stop : Nat
  text : String
  deriving Inhabited

private def lines (input : String) (r : Syntax.Range) : Array Line := Id.run do
  let text := String.Pos.Raw.extract input r.start r.stop
  let mut out := #[]
  let mut offset := r.start.byteIdx
  for l in text.splitOn "\n" do
    let body := l.trimAsciiEnd.toString
    let indent := l.utf8ByteSize - l.trimAsciiStart.toString.utf8ByteSize
    out := out.push { start := offset, content := offset + indent, stop := offset + body.utf8ByteSize, text := body }
    offset := offset + l.utf8ByteSize + 1
  return out

private def indent (l : Line) : Nat := l.content - l.start

private def joinable (l : Line) : Bool :=
  !l.text.trimAscii.isEmpty && !l.text.contains "--" && !l.text.contains "/-" && !l.text.contains "-/"

/-- The text of physical lines, each a run of source lines joined by spaces. -/
private def render (ls : Array Line) (phys : Array (Array Nat)) : String :=
  "\n".intercalate <| phys.toList.map fun group =>
    " ".intercalate <| group.toList.zipIdx.map fun (i, k) =>
      if k == 0 then ls[i]!.text else ls[i]!.text.trimAsciiStart.toString

/-- Whether `text` parses as exactly one command with the syntax tree of `cmd`. -/
def sameTree (text : String) (cmd : Syntax) (pctx : Parser.ParserModuleContext) (fileName : String) : Bool :=
  let ictx := Parser.mkInputContext text fileName
  let (stx, ps, msgs) := Parser.parseCommand ictx pctx {} {}
  let (eof, _, msgs) := Parser.parseCommand ictx pctx ps msgs
  !msgs.hasErrors && Parser.isTerminalCommand eof && stx == cmd

/-- The line breaks of `cmd` to replace by a space: from the end of a line's text to the start of
    the next line's text. -/
def joins (input : String) (cmd : Syntax) (pctx : Parser.ParserModuleContext) (fileName : String)
    (width : Nat := 100) : Array Syntax.Range := Id.run do
  let some r := cmd.getRange? (canonicalOnly := true) | return #[]
  -- Parsing the command alone measures columns from its start, which must start a line.
  if r.start.byteIdx > 0 && (r.start.prev input).get input != '\n' then return #[]
  let ls := lines input r
  if ls.size < 2 then return #[]
  let mut phys : Array (Array Nat) := (Array.range ls.size).map (#[·])
  let mut k := 0
  while k + 1 < phys.size do
    let a := phys[k]!
    let b := phys[k+1]!
    let fits := (render ls #[a]).length + 1 + (render ls #[b]).trimAsciiStart.toString.length ≤ width
    -- A line that opens an indented continuation stays at the head of it.
    let opens := match phys[k+2]? with
      | some c => joinable ls[c[0]!]! && indent ls[c[0]!]! > indent ls[b[0]!]!
      | none => false
    if !(a ++ b).all (joinable ls[·]!) || !fits || opens then
      k := k + 1
      continue
    let cand := (phys.extract 0 k).push (a ++ b) ++ phys.extract (k + 2) phys.size
    if sameTree (render ls cand) cmd pctx fileName then
      phys := cand
      -- The line above may now take this one, which no longer opens a continuation.
      if k > 0 then k := k - 1
    else k := k + 1
  let mut out := #[]
  for group in phys do
    for h : j in [1:group.size] do
      out := out.push ⟨⟨ls[group[j-1]!]!.stop⟩, ⟨ls[group[j]!]!.content⟩⟩
  return out

/-- The comments in `bytes[a:b]`, as byte ranges: line comments up to their newline and block
    comments with their nesting. Doc comments and module docs are syntax and are skipped, and so is
    the text of string literals. -/
private def commentRanges (bytes : ByteArray) (a b : Nat) : Array (Nat × Nat) := Id.run do
  let at? (i : Nat) (c : Char) : Bool := i < b && bytes[i]! == c.toUInt8
  let mut out := #[]
  let mut i := a
  while i < b do
    if at? i '"' then
      i := i + 1
      while i < b && !at? i '"' do
        i := i + (if at? i '\\' then 2 else 1)
      i := i + 1
    else if at? i '-' && at? (i+1) '-' then
      let s := i
      while i < b && !at? i '\n' do i := i + 1
      out := out.push (s, i)
    else if at? i '/' && at? (i+1) '-' then
      let doc := at? (i+2) '-' || at? (i+2) '!'
      let s := i
      let mut depth := 1
      i := i + 2
      while i < b && depth > 0 do
        if at? i '/' && at? (i+1) '-' then depth := depth + 1; i := i + 2
        else if at? i '-' && at? (i+1) '/' then depth := depth - 1; i := i + 2
        else i := i + 1
      unless doc do out := out.push (s, i)
    else i := i + 1
  return out

/-- The edits that delete the comments inside `cmd`, its leading doc comment aside: a comment on a
    line of its own goes with its line, one after code goes with the spaces before it, and one
    between tokens becomes a space. All are kept only if the command still parses to the same
    syntax tree; comments are not part of it. -/
def stripComments (input : String) (cmd : Syntax) (pctx : Parser.ParserModuleContext)
    (fileName : String) : Array (Syntax.Range × String) := Id.run do
  let some r := cmd.getRange? (canonicalOnly := true) | return #[]
  if r.start.byteIdx > 0 && (r.start.prev input).get input != '\n' then return #[]
  let bytes := input.toUTF8
  let isSpace (i : Nat) : Bool := bytes[i]! == ' '.toUInt8 || bytes[i]! == '\t'.toUInt8
  -- A comment after the last token, on its line, belongs to the command too.
  let mut stop := r.stop.byteIdx
  while stop < bytes.size && bytes[stop]! != '\n'.toUInt8 do stop := stop + 1
  let mut edits : Array (Nat × Nat × String) := #[]
  for (s, e) in commentRanges bytes r.start.byteIdx stop do
    if e > stop then continue
    -- The start of the comment's line, and whether only spaces come before it there.
    let mut ls := s
    while ls > 0 && bytes[ls-1]! != '\n'.toUInt8 do ls := ls - 1
    let mut alone := true
    for k in [ls:s] do
      if !isSpace k then alone := false
    -- What follows the comment on its line.
    let mut le := e
    while le < bytes.size && isSpace le do le := le + 1
    let lineEnds := le ≥ bytes.size || bytes[le]! == '\n'.toUInt8
    if alone && lineEnds then
      -- The whole line, with its newline.
      edits := edits.push (ls, min (le + 1) bytes.size, "")
    else if lineEnds then
      let mut cs := s
      while cs > ls && isSpace (cs - 1) do cs := cs - 1
      -- After a bullet alone on its line, the next line moves up when it starts two columns
      -- right of the bullet: its first tactic keeps its column, so its block keeps its layout.
      let mut bs := ls
      while bs < cs && isSpace bs do bs := bs + 1
      let bullet := cs == bs + 2 && bytes[bs]! == 0xC2 && bytes[bs+1]! == 0xB7
      let mut ns := le + 1
      while ns < bytes.size && isSpace ns do ns := ns + 1
      let nextOpens := ns + 1 < bytes.size && bytes[ns]! != '\n'.toUInt8 &&
        !((bytes[ns]! == '-'.toUInt8 || bytes[ns]! == '/'.toUInt8) && bytes[ns+1]! == '-'.toUInt8)
      if bullet && nextOpens && ns - (le + 1) == (bs - ls) + 2 && ns < r.stop.byteIdx then
        edits := edits.push (cs, ns, " ")
      else
        edits := edits.push (cs, le, "")
    else
      edits := edits.push (s, e, if alone then "" else " ")
  if edits.isEmpty then return #[]
  -- The command's text with every comment gone must parse to the same tree.
  let mut text := ""
  let mut p := r.start.byteIdx
  for (s, e, t) in edits do
    if s < p then return #[]
    text := text ++ String.Pos.Raw.extract input ⟨p⟩ ⟨s⟩ ++ t
    p := e
  text := text ++ String.Pos.Raw.extract input ⟨p⟩ ⟨stop⟩
  unless sameTree text cmd pctx fileName do return #[]
  return edits.map fun (s, e, t) => (⟨⟨s⟩, ⟨e⟩⟩, t)

end LeanPerf.Layout
