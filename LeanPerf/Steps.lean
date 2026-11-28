import Lean

/-!
# Proof steps

What `--compress` shortens: the tactic steps of a proof, the work a reader follows, rather than its
bytes. A step is a node of the tactic category, wherever it is, including the tactic blocks inside
terms. Nodes that only arrange other tactics are not steps: sequences, bullets, parentheses, `<;>`,
`focus`, `case` and `next`. So `rw [a, b]` is one step, `constructor <;> simp` two, and
`exact f (by simp)` two.
-/

open Lean

namespace LeanPerf.Steps

/-- The leading identifier-like token of a tactic's text, e.g. `simp_all` or `nlinarith`. -/
def head (text : String) : String :=
  (text.takeWhile fun c => c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!').toString

/-- Whether `text` has no comment, which an edit of it could lose. -/
def uncommented (text : String) : Bool := !text.contains "--" && !text.contains "/-"

/-- Tactic syntax kinds that arrange other tactics rather than act on a goal. -/
def structural : List SyntaxNodeKind :=
  [``Parser.Tactic.tacticSeq, ``Parser.Tactic.tacticSeq1Indented, ``Parser.Tactic.tacticSeqBracketed,
   ``Lean.cdot, ``Lean.Parser.Tactic.paren, ``Lean.Parser.Tactic.«tactic_<;>_», ``Lean.Parser.Tactic.focus,
   ``Lean.Parser.Tactic.case, ``Lean.Parser.Tactic.«tacticNext_=>_»]

/-- The syntax kinds of the tactic category in `env`. -/
def tacticKinds (env : Environment) : Parser.SyntaxNodeKindSet :=
  match (Parser.parserExtension.getState env).categories.find? `tactic with
  | some c => c.kinds
  | none => {}

/-- The tactic steps in `stx`. -/
partial def count (kinds : Parser.SyntaxNodeKindSet) (stx : Syntax) : Nat :=
  match stx with
  | .node _ k args =>
    let own := if kinds.contains k && !structural.contains k then 1 else 0
    args.foldl (fun n a => n + count kinds a) own
  | _ => 0

/-- Whether `cmd` declares something: `theorem`, `def`, `instance`, `structure`, Mathlib's `lemma`… -/
partial def isDeclaration (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Parser.Command.declaration || cmd.getKind == `lemma ||
    (cmd.getKind == ``Parser.Command.in && isDeclaration cmd[2])

/-- The steps of the command that `text` holds, parsed alone; none when it does not parse. -/
def ofCommand (kinds : Parser.SyntaxNodeKindSet) (text : String) (pctx : Parser.ParserModuleContext)
    (fileName : String) : Option Nat :=
  let ictx := Parser.mkInputContext text fileName
  let (stx, ps, msgs) := Parser.parseCommand ictx pctx {} {}
  let (eof, _, msgs) := Parser.parseCommand ictx pctx ps msgs
  if msgs.hasErrors || !Parser.isTerminalCommand eof then none else some (count kinds stx)

/-- How many steps the command `cmd` loses when `newText` replaces `range` of `input`; 0 when the
    edit reaches outside the command or the result does not parse alone, and negative when it
    gains steps. -/
def removed (input : String) (cmd : Syntax) (pctx : Parser.ParserModuleContext) (range : Syntax.Range)
    (newText : String) : Int :=
  match cmd.getRange? (canonicalOnly := true) with
  | none => 0
  | some r =>
    if range.start < r.start || r.stop < range.stop then 0 else
      let kinds := tacticKinds pctx.env
      let text := String.Pos.Raw.extract input r.start range.start ++ newText ++
        String.Pos.Raw.extract input range.stop r.stop
      match ofCommand kinds text pctx "<leanperf>" with
      | some n => (count kinds cmd : Int) - n
      | none => 0

/-- What an edit is worth: each declaration it removes outranks any number of steps, each step any
    number of bytes. An edit is worth making when this is positive. -/
def worth (gain : Nat) (bytesSaved : Int) : Int := (gain : Int) * 1000000 + bytesSaved

end LeanPerf.Steps
