import LeanPerf.Grammar

open Lean Parser

namespace LeanPerf

structure Finding where
  rule : String
  edit : Lsp.TextEdit
  deriving ToJson

structure Report where
  findings : Array Finding := #[]
  skippedCommands : Nat := 0
  deriving ToJson

private def slice (file : FileMap) (a b : String.Pos.Raw) : String :=
  String.Pos.Raw.extract file.source a b

private def finding (file : FileMap) (stx : Syntax) (rule text : String) : Option Finding := do
  let range ← stx.getRange?
  return {rule, edit := {range := file.utf8RangeToLspRange range, newText := text}}

private def splitObtain (file : FileMap) (name : String) (stx : Syntax) : Option Finding := do
  let `(tactic| obtain $pat:rcasesPatMed := $rhs:term) := stx | none
  guard (rhs.raw.isOfKind ``Term.app)
  let pr ← pat.raw.getRange?
  guard ((slice file pr.start pr.stop).startsWith "⟨")
  let r ← stx.getRange?
  let pos := file.toPosition r.start
  let indent := slice file (file.ofPosition { pos with column := 0 }) r.start
  guard (indent.all (· == ' '))
  let replacement := "have " ++ name ++ slice file pr.stop r.stop ++ "\n" ++ indent ++
    slice file r.start pr.stop ++ " := " ++ name
  finding file stx "splitObtain" replacement

/-- Only inspect the declared goal when the *whole* proof is one tactic. -/
private def directProof (file : FileMap) (decl : Syntax) : Option Finding := do
  let sig ← decl.getArgs.find? fun s =>
    s.isOfKind ``Command.declSig || s.isOfKind ``Command.optDeclSig
  let spec ← sig[1].find? (·.isOfKind ``Term.typeSpec)
  let goal := spec[1]
  let val ← decl.getArgs.find? (·.isOfKind ``Command.declValSimple)
  let `(term| by $t:tactic) := val[1] | none
  match t with
  | `(tactic| simp) =>
    let `(term| $lhs = $rhs) := goal | none
    -- Restrict this rule to a named operand. Placeholders and type-directed overloaded
    -- expressions can denote different things even when their spelling is identical.
    guard (lhs.raw.isIdent && rhs.raw.isIdent && lhs.raw.getId == rhs.raw.getId)
    finding file t "simpRfl" "rfl"
  | `(tactic| simpa using%$kw $h:ident) =>
    -- A later binder could shadow a name in this hypothesis type.
    let binder ← sig[0].getArgs.back?
    guard (binder.isOfKind ``Term.explicitBinder && binder[1].getArgs.any (·.getId == h.getId))
    let type := binder[2][1]
    let gr ← goal.getRange?
    let tr ← type.getRange?
    guard (slice file tr.start tr.stop == slice file gr.start gr.stop)
    let kr ← kw.getRange?
    let hr ← h.raw.getRange?
    let head ← t.raw[0].getTailPos?
    guard ((slice file head kr.start).trimAscii.isEmpty)
    finding file t "exactUsing" ("exact" ++ slice file kr.stop hr.stop)
  | _ => none

/-- Look for tactics only inside actual proof blocks. Quoted Lean code is data. -/
private partial def walk (file : FileMap) (name : String) (stx : Syntax)
    (inProof : Bool) (acc : Array Finding) : Array Finding := Id.run do
  if stx.isQuot then return acc
  let mut acc := acc
  if let some fix := directProof file stx then acc := acc.push fix
  if inProof && stx.isOfKind ``Tactic.obtain then
    if let some fix := splitObtain file name stx then acc := acc.push fix
  let inProof := inProof || stx.isOfKind ``Term.byTactic
  for child in stx.getArgs do
    acc := walk file name child inProof acc
  return acc

def lint (env : Environment) (text : String) : IO Report := do
  let ctx := mkInputContext text "<document>"
  let (_, initial, messages) ← parseHeader ctx
  let mut report : Report := {}
  if messages.hasErrors then return { report with skippedCommands := 1 }
  let mut name := "hObtained"
  while text.contains name do name := name ++ "'"
  let mut state := initial
  repeat
    let (cmd, next, errors) := parseCommand ctx {env, options := {}} state {}
    state := next
    if isTerminalCommand cmd then break
    if errors.hasErrors then
      report := {report with skippedCommands := report.skippedCommands + 1}
    else
      -- Limit rewrites to declarations, including those under a scoped set_option.
      let mut decl := cmd
      while decl.isOfKind ``Command.in do decl := decl[2]
      if decl.isOfKind ``Command.declaration || decl.isOfKind ``Grammar.lemmaDecl then
        report := {report with findings := walk ctx.fileMap name decl false report.findings}
  return report

end LeanPerf

/-- Parse JSON-encoded documents on stdin, one per line. The grammar comes exclusively from this package and its toolchain. -/
unsafe def main (args : List String) : IO Unit := do
  let [sysroot, library] := args | throw <| IO.userError "expected Lean toolchain root and parser library"
  searchPathRef.set [← getLibDir sysroot, library]
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{module := `LeanPerf.Grammar}] {}
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let text ← IO.ofExcept (Json.parse line >>= fromJson? (α := String))
    stdout.putStrLn (toJson (← LeanPerf.lint env text)).compress
    stdout.flush
