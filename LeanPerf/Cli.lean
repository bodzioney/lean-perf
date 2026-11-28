import LeanPerf.Rules
import LeanPerf.Lints
import LeanPerf.SyntaxDedup
import LeanPerf.Unused
import LeanPerf.Project
import LeanPerf.Steps
import LeanPerf.Edit
import Std.Sync.Channel
import Std.Sync.Mutex

/-!
# Command line and language server

Every pass reports `Finding`s; this module previews them as unified diffs, applies them
atomically per file, checks rewritten files, benchmarks them, and serves them over LSP.

* The syntax rules parse with this package's own grammar, in this process. They never read the
  target's Lake configuration and never run its code.
* The syntactic duplicate pass reads source files only.
* The elaborated passes (`--dedup`, `--tactics`) run this executable under `lake env` in the
  target project, which does run the target's Lake configuration and imported metaprograms.
-/

open Lean System

namespace LeanPerf.Cli

/-- Rule name, description, and a token whose absence means the rule cannot fire. -/
def ruleTable : List (String × String × String) :=
  (Lints.catalog.filter (·.group == "syntax")).map fun l => (l.name, l.description, l.token)
def ruleNames : List String := ruleTable.map (·.1)
def ruleMessage (r : String) : String := ((ruleTable.find? (·.1 == r)).map (·.2.1)).getD r
def dedupModes : List String := ["auto", "syntax", "elaborate"]

def hasSub (s t : String) : Bool := (s.splitOn t).length > 1

/-- A finding from any pass. Syntax rules carry only an edit; the others carry a range and a
    message, and an edit when they have a checked replacement. -/
structure Finding where
  rule : String
  message : Option String := none
  «lemma» : Option String := none
  range : Option Lsp.Range := none
  edit : Option Lsp.TextEdit := none
  /-- The steps the edit takes out, or 1000 for each declaration (`Steps.worth`). -/
  gain : Nat := 0
  deriving ToJson, FromJson, Inhabited

structure Analysis where
  findings : Array Finding := #[]
  skipped : Nat := 0
  /-- The tactic steps and declarations of the file as it was read, when the pass counted them. -/
  steps : Option (Nat × Nat) := none

/-- A pass: analyze a file (optionally unsaved text), check a candidate text, and shut down. -/
structure Analyzer where
  analyze : FilePath → Option String → IO Analysis
  check : FilePath → String → IO (Array String)
  close : IO Unit := pure ()

/-! ## Package and project -/

/-- `<package>/.lake/build/bin/leanperf` -/
def package : IO FilePath := do
  let app ← IO.appPath
  let some p := app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | throw <| IO.userError s!"cannot locate the LeanPerf package from {app}"
  return p

/-- The environment for the syntax rules: this package's grammar and toolchain only. -/
unsafe def grammarEnv : IO Environment := do
  let pkg ← package
  -- Resolve the toolchain in our package. The workspace may pin another, or none that exists.
  let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := pkg }
  if out.exitCode != 0 then throw <| IO.userError s!"cannot find LeanPerf's Lean toolchain: {out.stderr}"
  let sysroot : FilePath := out.stdout.trimAscii.toString
  searchPathRef.set [← getLibDir sysroot, pkg / ".lake" / "build" / "lib" / "lean"]
  enableInitializersExecution
  importModules (loadExts := true) #[{ module := `LeanPerf.Grammar }] {}

def toolchainMismatch (root : FilePath) : IO (Option String) := do
  let ours := (← IO.FS.readFile ((← package) / "lean-toolchain")).trimAscii.toString
  let pin := root / "lean-toolchain"
  let theirs ← if ← pin.pathExists then pure (← IO.FS.readFile pin).trimAscii.toString else pure ours
  return if theirs != ours then
    some s!"its toolchain ({theirs}) differs from LeanPerf's ({ours}), whose .olean files it cannot read"
  else none

def srcDir (root : FilePath) : IO FilePath := do
  try return (← Project.settings.settingsAt root).1 catch _ => return root

/-- Why the elaborated pass cannot analyze `paths` in the project at `root`. -/
def elaborationBlocker (root : FilePath) (paths : Array FilePath) : IO (Option String) := do
  if let some r ← toolchainMismatch root then return some r
  let out ← try IO.Process.output { cmd := "lake", args := #["--no-build", "env", "printenv", "LEAN_PATH"], cwd := root }
    catch _ => return some "Lake cannot set up the project without building"
  if out.exitCode != 0 then return some "Lake cannot set up the project without building"
  let search := (out.stdout.trimAscii.toString.splitOn ":").filter (· != "") |>.map FilePath.mk
  let src ← srcDir root
  let mut stack := paths
  let mut seen : Std.HashSet String := {}
  while let some p := stack.back? do
    stack := stack.pop
    if seen.contains p.toString then continue
    seen := seen.insert p.toString
    for m in SyntaxDedup.headerImports (← IO.FS.readFile p) do
      let source := modToFilePath src m.toName "lean"
      if ← source.pathExists then stack := stack.push source
      else
        let mut built := false
        for d in search do
          if ← (modToFilePath (root / d) m.toName "olean").pathExists then built := true; break
        unless built do return some s!"{m} is not built"
  return none

/-! ## Analyzers -/

def syntaxAnalyzer (root : FilePath) (paths : Array FilePath) : IO Analyzer := do
  let ix ← IO.mkRef (← ({ src := ← IO.FS.realPath (← srcDir root) } : SyntaxDedup.Index).load paths)
  return {
    analyze := fun path text => do
      let (ix', fs, skipped) ← (← ix.get).analyze path text
      ix.set ix'
      return { skipped, findings := fs.map fun f =>
        { rule := f.rule, message := some f.message, «lemma» := some f.«lemma», range := some f.range } }
    check := fun _ _ => throw <| IO.userError "the syntactic pass suggests no proofs to check" }

/-- Unused theorems of `paths`, from the source text of every module under the project's `srcDir`. -/
def unusedAnalyzer (root : FilePath) (paths : Array FilePath) : IO Analyzer := do
  let src ← IO.FS.realPath (← srcDir root)
  let all ← Project.files #[src]
  let files ← all.mapM fun p => return Unused.parse p (SyntaxDedup.moduleName src p) (← IO.FS.readFile p)
  let targets ← paths.mapM fun p => return (← IO.FS.realPath p).toString
  let found := Unused.analyze files (Std.HashSet.ofArray targets)
  return {
    analyze := fun path text => do
      let some text := text | return {}
      let some cmds := found[(← IO.FS.realPath path).toString]? | return {}
      let chars := text.toList.toArray
      return { findings := cmds.map fun (_, c) =>
        let range : Lsp.Range := ⟨SyntaxDedup.lspPos chars c.lead, SyntaxDedup.lspPos chars c.stop⟩
        { rule := "unusedTheorem", message := some s!"{c.name} is not mentioned anywhere else in the project",
          range := some range, edit := some { range, newText := "" } } }
    check := fun _ _ => pure #[] }

/-- This executable under `lake env` in the target project, answering one JSON request per line. -/
def elaboratedAnalyzer (root : FilePath) (paths : Array FilePath) (general := true)
    (jobs : Option Nat := none) (tacticSaving : Option Nat := none) (shorter compress layout := false)
    (propose : Option String := none) (disabled : List String := []) : IO Analyzer := do
  if let some r ← toolchainMismatch root then
    throw <| IO.userError s!"cannot elaborate the project: {r}"
  let (h, listing) ← IO.FS.createTempFile
  h.putStr (toJson (paths.map (·.toString))).compress
  h.flush
  let args := #["--project", "--serve"] ++ (if general then #[] else #["--no-general"]) ++
    (disabled.map ("--skip-lint=" ++ ·)).toArray ++
    (tacticSaving.map (fun n => #["--tactics", "--batch-replay", s!"--min-saving={n}"])).getD #[] ++
    (if shorter then #["--shorter"] else #[]) ++
    (if compress then #["--compress"] else #[]) ++
    (if layout then #["--layout"] else #[]) ++
    (propose.map (#["--propose=" ++ ·])).getD #[] ++
    (jobs.map (#[s!"--jobs={·}"])).getD #[] ++ #[s!"--file-list={listing}"]
  let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, cwd := root,
                                 stdin := .piped, stdout := .piped, stderr := .inherit }
  -- Take the only reference to the pipe, so that dropping it closes the server's input.
  let (input, child) ← child.takeStdin
  let stdin ← IO.mkRef (some input)
  let request (fields : List (String × Json)) : IO Json := do
    let some i ← stdin.get | throw <| IO.userError "LeanPerf dedup is closed"
    i.putStrLn (Json.mkObj fields).compress
    i.flush
    let line ← child.stdout.getLine
    if line.isEmpty then throw <| IO.userError "LeanPerf dedup stopped unexpectedly"
    let r ← IO.ofExcept (Json.parse line)
    if let .ok e := r.getObjValAs? String "error" then throw <| IO.userError e
    return r
  let textField (t : Option String) := (t.map fun t => [("text", toJson t)]).getD []
  -- A proposer, or `foldHelper`, may fold away a theorem that no other module mentions.
  let external ← if propose.isNone && !(compress && !disabled.contains "foldHelper") then pure (fun _ => pure []) else do
    let src ← IO.FS.realPath (← srcDir root)
    let all ← Project.files #[src]
    let files ← all.mapM fun p => return Unused.parse p (SyntaxDedup.moduleName src p) (← IO.FS.readFile p)
    let mentions (f : Unused.File) : Std.HashSet String :=
      (f.commands.foldl (fun acc c => acc ++ c.idents) f.free).foldl
        (fun acc t => acc.insertMany (Unused.components t)) {}
    let sets := files.map mentions
    let mut count : Std.HashMap String Nat := {}
    for m in sets do
      for c in m do count := count.insert c (count.getD c 0 + 1)
    let byPath : Std.HashMap String Nat := Std.HashMap.ofList (files.toList.zipIdx.map fun (f, i) => (f.path.toString, i))
    pure fun (path : FilePath) => do
      let some i := byPath[(← IO.FS.realPath path).toString]? | return []
      let own := sets[i]!
      let names := files[i]!.commands.filterMap (·.«theorem»)
      let outside := names.filter fun n => count.getD n 0 > (if own.contains n then 1 else 0)
      return [("external", toJson outside)]
  return {
    analyze := fun path text => do
      let r ← request ([("path", toJson path.toString)] ++ textField text ++ (← external path))
      if tacticSaving.isSome && (← IO.ofExcept (r.getObjValAs? Nat "elabErrors")) > 0 then
        throw <| IO.userError "tactic analysis could not elaborate the original module"
      let findings ← IO.ofExcept (r.getObjValAs? (Array Finding) "findings")
      let steps := match r.getObjValAs? Nat "steps", r.getObjValAs? Nat "decls" with
        | .ok s, .ok d => some (s, d)
        | _, _ => none
      return { findings, skipped := (r.getObjValAs? Nat "skippedCommands").toOption.getD 0, steps }
    check := fun path text => do
      let r ← request [("path", toJson path.toString), ("text", toJson text), ("check", true)]
      IO.ofExcept (r.getObjValAs? (Array String) "errors")
    close := do
      stdin.set none  -- the last reference: closes the pipe, and the server exits
      let _ ← child.wait
      IO.FS.removeFile listing }

/-- The elaborated pass when the dependencies are built, else the syntactic pass. -/
def dedupAnalyzer (root : FilePath) (paths : Array FilePath) (mode : String)
    (jobs : Option Nat := none) (rules := Lints.names "dedup") : IO Analyzer := do
  let root ← IO.FS.realPath root
  let mut mode := mode
  if mode == "auto" then
    let reason ← elaborationBlocker root paths
    if let some r := reason then IO.eprintln s!"LeanPerf dedup: {r}; using the syntactic pass"
    mode := if reason.isSome then "syntax" else "elaborate"
  if mode == "syntax" then syntaxAnalyzer root paths else
    elaboratedAnalyzer root paths (general := rules.contains "specialCase") (jobs := jobs)
      (disabled := ["duplicate"].filter (!rules.contains ·))

def ruleAnalyzer (env : Environment) (rules : List String) : Analyzer where
  analyze _ text? := do
    let some text := text? | return {}
    unless rules.any fun r => hasSub text (((ruleTable.find? (·.1 == r)).map (·.2.2)).getD r) do return {}
    let r ← Rules.lint env text
    let findings := (r.findings.filter (rules.contains ·.rule)).map fun f =>
      ({ rule := f.rule, edit := some f.edit } : Finding)
    return { skipped := r.skippedCommands, findings }
  check _ _ := pure #[]

/-! ## Edits -/

def posLt (a b : Lsp.Position) : Bool := a.line < b.line || (a.line == b.line && a.character < b.character)
def posLe (a b : Lsp.Position) : Bool := !posLt b a

/-- Keep an outer edit intact if its source contains another reported edit. -/
def independent (fs : Array Finding) : Array Finding := Id.run do
  let withEdit := fs.filterMap fun f => f.edit.map (f, ·)
  let sorted := withEdit.qsort fun (_, a) (_, b) =>
    posLt a.range.start b.range.start || (a.range.start == b.range.start && posLt b.range.end a.range.end)
  let mut out := #[]
  let mut stop : Lsp.Position := ⟨0, 0⟩
  let mut first := true
  for (f, e) in sorted do
    if first || posLe stop e.range.start then
      out := out.push f
      stop := e.range.end
      first := false
  return out

private structure SourceEdit where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  text : String
  gain : Nat := 0
  deriving Inhabited

/-- What the edit is worth: the steps and declarations it takes out, then the UTF-8 bytes after
    newline conversion. -/
private def SourceEdit.saving (e : SourceEdit) : Int :=
  Steps.worth e.gain ((e.stop.byteIdx - e.start.byteIdx : Int) - e.text.utf8ByteSize)

/-- The disjoint edits worth the most together. Combining disjoint edits inside a proof can be worth
    more than replacing the entire proof. -/
private def smallestSource (edits : Array SourceEdit) : Array SourceEdit :=
  let sorted := (edits.filter (·.saving > 0)).qsort fun a b =>
    a.stop < b.stop || (a.stop == b.stop && (a.start < b.start || (a.start == b.start && a.text < b.text)))
  (bestDisjoint (Array.range sorted.size) (sorted[·]!.start.byteIdx) (sorted[·]!.stop.byteIdx)
    (sorted[·]!.saving)).map (sorted[·]!)

def rewrite (text : String) (fs : Array Finding) (shorter := false) : String × Nat := Id.run do
  let map := FileMap.ofString text
  let lines := (text.splitOn "\n").toArray
  let candidates := if shorter then fs else independent fs
  let edits := candidates.filterMap fun f => do
    let e ← f.edit
    let span := map.lspRangeToUtf8Range e.range
    let crlf := (lines[e.range.start.line]?.getD "").endsWith "\r"
    let new := if crlf then "\r\n".intercalate (e.newText.splitOn "\n") else e.newText
    return { start := span.start, stop := span.stop, text := new, gain := f.gain : SourceEdit }
  let edits := if shorter then smallestSource edits else edits
  let mut out := ""
  let mut cursor : String.Pos.Raw := 0
  for e in edits do
    out := out ++ String.Pos.Raw.extract text cursor e.start ++ e.text
    cursor := e.stop
  return (out ++ String.Pos.Raw.extract text cursor text.rawEndPos, edits.size)

/-! ## Unified diffs (Myers), formatted as Python's `difflib.unified_diff` -/

def splitLines (s : String) : Array String :=
  let parts := s.splitOn "\n"
  let n := parts.length
  (parts.toArray.zipIdx.filterMap fun (p, i) =>
    if i + 1 < n then some (p ++ "\n") else if p.isEmpty then none else some p)

/-- Edit script: `(tag, i, j)` with tag `=`, `-` (a[i]) or `+` (b[j]). -/
def myers (a b : Array String) : Array (Char × Nat × Nat) := Id.run do
  let n := a.size
  let m := b.size
  let mx := n + m
  let off := mx + 1
  let mut v : Array Nat := Array.replicate (2 * mx + 3) 0
  let mut hist : Array (Array Nat) := #[]
  let mut final := 0
  let idx (k : Int) : Nat := (off + k).toNat
  for d in [0:mx + 1] do
    hist := hist.push v
    let mut done := false
    for kk in [0:d + 1] do
      let k : Int := 2 * kk - d
      let down := k == -(d : Int) || (k != d && v[idx (k - 1)]! < v[idx (k + 1)]!)
      let mut x := if down then v[idx (k + 1)]! else v[idx (k - 1)]! + 1
      let mut y := (x - k).toNat
      while x < n && y < m && a[x]! == b[y]! do x := x + 1; y := y + 1
      v := v.set! (idx k) x
      if x ≥ n && y ≥ m then done := true; break
    if done then final := d; break
  let mut ops : Array (Char × Nat × Nat) := #[]
  let mut x := n
  let mut y := m
  for d' in [0:final] do
    let d := final - d'
    let w := hist[d]!
    let k : Int := x - y
    let prevK := if k == -(d : Int) || (k != d && w[idx (k - 1)]! < w[idx (k + 1)]!) then k + 1 else k - 1
    let px := w[idx prevK]!
    let py := (px - prevK).toNat
    while x > px && y > py do ops := ops.push ('=', x - 1, y - 1); x := x - 1; y := y - 1
    if x == px then ops := ops.push ('+', x, y - 1) else ops := ops.push ('-', x - 1, y)
    x := px
    y := py
  while x > 0 && y > 0 do ops := ops.push ('=', x - 1, y - 1); x := x - 1; y := y - 1
  return ops.reverse

/-- `(tag, i1, i2, j1, j2)` opcodes. -/
def opcodes (a b : Array String) : Array (String × Nat × Nat × Nat × Nat) := Id.run do
  let ops := myers a b
  let mut out := #[]
  let mut i := 0
  let mut j := 0
  let mut k := 0
  while k < ops.size do
    if ops[k]!.1 == '=' then
      let (i0, j0) := (i, j)
      while k < ops.size && ops[k]!.1 == '=' do i := i + 1; j := j + 1; k := k + 1
      out := out.push ("equal", i0, i, j0, j)
    else
      let (i0, j0) := (i, j)
      while k < ops.size && ops[k]!.1 != '=' do
        if ops[k]!.1 == '-' then i := i + 1 else j := j + 1
        k := k + 1
      let tag := if i > i0 && j > j0 then "replace" else if i > i0 then "delete" else "insert"
      out := out.push (tag, i0, i, j0, j)
  return out

def unifiedDiff (a b : String) (fromFile toFile : String) (ctx := 3) : String := Id.run do
  let la := splitLines a
  let lb := splitLines b
  let mut codes := opcodes la lb
  if codes.isEmpty then codes := #[("equal", 0, 1, 0, 1)]
  if let some (t, i1, i2, j1, j2) := codes[0]? then
    if t == "equal" then codes := codes.set! 0 (t, max i1 (i2 - ctx), i2, max j1 (j2 - ctx), j2)
  if let some (t, i1, i2, j1, j2) := codes.back? then
    if t == "equal" then codes := codes.set! (codes.size - 1) (t, i1, min i2 (i1 + ctx), j1, min j2 (j1 + ctx))
  let mut groups := #[]
  let mut group := #[]
  for (t, i1, i2, j1, j2) in codes do
    let mut (i1, j1) := (i1, j1)
    if t == "equal" && i2 - i1 > 2 * ctx then
      group := group.push (t, i1, min i2 (i1 + ctx), j1, min j2 (j1 + ctx))
      groups := groups.push group
      group := #[]
      i1 := max i1 (i2 - ctx)
      j1 := max j1 (j2 - ctx)
    group := group.push (t, i1, i2, j1, j2)
  if group.size > 0 && !(group.size == 1 && group[0]!.1 == "equal") then groups := groups.push group
  let range (start stop : Nat) : String :=
    let len := stop - start
    if len == 1 then s!"{start + 1}" else if len == 0 then s!"{start},0" else s!"{start + 1},{len}"
  let mut out := ""
  for g in groups do
    if out.isEmpty then out := s!"--- {fromFile}\n+++ {toFile}\n"
    let (_, f1, _, f3, _) := g[0]!
    let (_, _, l2, _, l4) := g.back!
    out := out ++ s!"@@ -{range f1 l2} +{range f3 l4} @@\n"
    for (t, i1, i2, j1, j2) in g do
      if t == "equal" then for l in la.extract i1 i2 do out := out ++ " " ++ l
      if t == "replace" || t == "delete" then for l in la.extract i1 i2 do out := out ++ "-" ++ l
      if t == "replace" || t == "insert" then for l in lb.extract j1 j2 do out := out ++ "+" ++ l
  return out

/-! ## Checking and saving -/

/-- Elaborate `text` as `path` with the target's Lake configuration; seconds taken. -/
def lakeCheck (path : FilePath) (text : String) : IO Float := do
  let t0 ← IO.monoNanosNow
  let out ← IO.Process.output
    { cmd := "lake", args := #["--no-build", "--no-cache", "lean", path.toString, "--", "--stdin"] } text
  if out.exitCode != 0 then
    throw <| IO.userError s!"Lake check failed\n{out.stdout}{out.stderr}"
  return (← IO.monoNanosNow).toFloat / 1e9 - t0.toFloat / 1e9

/-- Write `new` unless the file changed since it was read. The file is rewritten in place, which
    keeps its permissions and links. -/
def save (path : FilePath) (original : ByteArray) (new : String) : IO Unit := do
  if (← path.symlinkMetadata).type == .symlink || (← IO.FS.readBinFile path) != original then
    throw <| IO.userError "file changed during analysis"
  IO.FS.writeFile path new

def fmt2 (x : Float) : String :=
  let c := (x * 100).round.toUInt64.toNat
  let frac := c % 100
  s!"{c / 100}.{if frac < 10 then "0" else ""}{frac}"

def median (xs : Array Float) : Float :=
  let s := xs.qsort (· < ·)
  if s.size == 0 then 0 else if s.size % 2 == 1 then s[s.size / 2]! else (s[s.size / 2 - 1]! + s[s.size / 2]!) / 2

/-! ## Command line -/

structure Args where
  paths : Array FilePath := #[]
  lsp := false
  rules : List String := ruleNames
  apply := false
  check := false
  bench : Nat := 0
  dedup := false
  dedupPass : Option String := none
  jobs : Option Nat := none
  shorter := false
  tactics := false
  /-- `--tactics` was given, not only implied by `--compress`. -/
  speed := false
  compress := false
  cosmetic := false
  unused := false
  layout := false
  propose : Option String := none
  minSaving : Nat := 1

def usage : String :=
  "usage: leanperf --golf [--cosmetic] [--strip-comments] [--keep-unused] [--no-optimize] [--speed] [--rounds N] [--jobs N] paths …\n" ++
  "       leanperf [--lsp] [--rules R,…] [--apply] [--check] [--bench N] [--dedup] " ++
  "[--dedup-pass {auto,syntax,elaborate}] [--tactics] [--compress] [--cosmetic] [--unused] [--layout] [--propose CMD] " ++
  "[--min-saving N] [--jobs N] " ++
  "[--shorter] [paths …]

A Lean proof linter, batch rewriter and LSP server.

  paths            Lean files or directories
  --golf           every shrinking pass in order, each edit checked: --unused, --dedup, rounds of
                   --unused and --compress until nothing changes, then --tactics. With
                   --cosmetic also byte-only edits and --layout, --strip-comments first deletes
                   comments, --keep-unused keeps theorems nothing uses. --tactics, last, only
                   takes cheaper tactics that add no bytes: --speed takes them all, --no-optimize none
  --lsp            serve LSP over stdio
  --list-lints     show the lint names, modes and descriptions
  --rules R,…      enable only these lints within the chosen mode
  -A, --allow R,…  suppress these lints within the chosen mode
  --apply          apply fixes in place
  --check          also elaborate rewritten files before writing them
  --bench N        time N original and N rewritten Lake checks
  --dedup          find theorems that restate or specialize existing ones
  --dedup-pass P   'elaborate' uses the target's Lean and built dependencies, 'syntax' only source
                   text, and 'auto' (the default) elaborates when it can; implies --dedup
  --tactics        replace tactics with cheaper ones that close the same goals, and drop
                   `set_option … in` overrides a command does not need (elaborates the target)
  --min-saving N   with --tactics, the smallest saving worth an edit, in heartbeats (default 1)
  --compress       take tactic steps and declarations out of proofs, each edit checked; implies
                   --shorter --check. Add --tactics for the lints that make tactics cheaper
  --cosmetic       with --compress, also the lints that only save bytes, such as shorter names
  --unused         delete theorems that nothing else in the project mentions, reading only
                   source text; run from the project root
  --layout         join lines that fit within 100 columns when the command parses the same
                   (with --rules stripComments,joinLines, also delete comments inside declarations)
  --propose CMD    send each theorem to the shell command CMD and keep the shortest rewrite it
                   proposes that Lean accepts with the same statement; implies --check
  --jobs N         parallel workers for skeletons and batch tactic replay (default 2)
  --shorter        select only replacements that shrink the source in UTF-8
"

def parseArgs (argv : List String) : Except String Args := do
  let mut a : Args := {}
  let mut selected : Option (List String) := none
  let mut allowed := []
  let mut rest := argv
  let value (flag : String) (rest : List String) : Except String (String × List String) :=
    match rest with
    | v :: r => pure (v, r)
    | [] => throw s!"argument {flag}: expected one argument"
  while let x :: r := rest do
    rest := r
    let (flag, inline) := match x.splitOn "=" with
      | f :: v :: more => if f.startsWith "--" then (f, some ("=".intercalate (v :: more))) else (x, none)
      | _ => (x, none)
    let take : Except String (String × List String) :=
      match inline with | some v => pure (v, rest) | none => value flag rest
    match flag with
    | "--lsp" => a := { a with lsp := true }
    | "--apply" => a := { a with apply := true }
    | "--check" => a := { a with check := true }
    | "--dedup" => a := { a with dedup := true }
    | "--shorter" => a := { a with shorter := true }
    | "--tactics" => a := { a with tactics := true, speed := true }
    | "--cosmetic" => a := { a with cosmetic := true }
    | "--compress" => a := { a with tactics := true, shorter := true, check := true, compress := true }
    | "--unused" => a := { a with unused := true }
    | "--layout" => a := { a with layout := true }
    | "--propose" => let (v, r) ← take; rest := r; a := { a with propose := some v, shorter := true, check := true }
    | "--rules" => let (v, r) ← take; rest := r; selected := some (v.splitOn ",")
    | "--allow" | "-A" => let (v, r) ← take; rest := r; allowed := allowed ++ v.splitOn ","
    | "--bench" =>
      let (v, r) ← take; rest := r
      let some n := v.toNat? | throw "argument --bench: invalid int value"
      a := { a with bench := n }
    | "--jobs" =>
      let (v, r) ← take; rest := r
      let some n := v.toNat? | throw "argument --jobs: invalid int value"
      a := { a with jobs := some n }
    | "--min-saving" =>
      let (v, r) ← take; rest := r
      let some n := v.toNat? | throw "argument --min-saving: invalid int value"
      a := { a with minSaving := n }
    | "--dedup-pass" =>
      let (v, r) ← take; rest := r
      unless dedupModes.contains v do throw s!"argument --dedup-pass: invalid choice: '{v}'"
      a := { a with dedupPass := some v }
    | "-h" | "--help" => throw "help"
    | _ =>
      if x.startsWith "-" then throw s!"unrecognized arguments: {x}"
      a := { a with paths := a.paths.push x }
  if let some j := a.jobs then
    if j < 1 || !(a.dedup || a.dedupPass.isSome || a.tactics || a.layout || a.propose.isSome) ||
        a.dedupPass == some "syntax" then
      throw "--jobs requires a positive integer and an elaborated, auto or layout pass"
  if a.lsp && a.shorter then throw "--shorter requires batch input"
  a := { a with dedup := a.dedup || a.dedupPass.isSome }
  if (a.lsp && (a.paths.size > 0 || a.apply || a.check || a.bench > 0 || a.dedup || a.tactics)) ||
      !(a.lsp || a.paths.size > 0) then
    throw "select --lsp alone or supply Lean paths with batch options"
  if a.dedup && a.tactics then throw "--dedup and --tactics are separate passes"
  if a.unused && (a.dedup || a.tactics || a.lsp) then throw "--unused is a separate pass"
  if a.layout && (a.dedup || a.tactics || a.unused || a.lsp) then throw "--layout is a separate pass"
  if a.propose.isSome && (a.dedup || a.tactics || a.unused || a.layout || a.lsp) then
    throw "--propose is a separate pass"
  let available := if a.dedup then match a.dedupPass with
      | some "syntax" => ["syntacticDuplicate"]
      | some "elaborate" => ["duplicate", "specialCase"]
      | _ => Lints.names "dedup"
    else if a.tactics then Lints.names "tactics" ++ (if a.compress then Lints.names "compress" else [])
    else if a.unused then Lints.names "unused"
    else if a.layout then Lints.names "layout"
    else if a.propose.isSome then Lints.names "propose"
    else ruleNames
  -- `--compress` takes steps and declarations out of proofs. Lints that only save bytes wait for
  -- `--cosmetic`, and those that make tactics cheaper for `--tactics`.
  let wanted := selected.getD (available.filter fun n => !Lints.optIn.contains n &&
    (a.cosmetic || !Lints.cosmetic.contains n) && !(a.compress && !a.speed && (Lints.names "tactics").contains n))
  unless (wanted ++ allowed).all available.contains do
    throw s!"available lints in this mode: {", ".intercalate available}"
  return { a with rules := available.filter fun r => wanted.contains r && !allowed.contains r }

def label (path : FilePath) : IO String := do
  let cwd := (← IO.currentDir).toString ++ "/"
  let p := path.toString
  return if p.startsWith cwd then (p.drop cwd.length).toString else p

/-- Report and rewrite each file. `verify` elaborates a candidate, throwing on failure. With
    `atomic`, edits in different files depend on each other: nothing is written unless every
    file succeeds. -/
def runBatch (paths : Array FilePath) (args : Args) (an : Analyzer)
    (verify : FilePath → String → IO Unit) (atomic := false) : IO UInt32 := do
  let mut failed := 0
  let mut count := 0
  let mut skipped := 0
  let mut counted : Option (Nat × Nat) := none
  let mut pending := #[]
  for path in paths do
    let lbl ← label path
    try
      let original ← IO.FS.readBinFile path
      let some text := String.fromUTF8? original | throw <| IO.userError "not UTF-8"
      let r ← an.analyze path (some text)
      let r := { r with findings := r.findings.filter (args.rules.contains ·.rule) }
      skipped := skipped + r.skipped
      if let some (s, d) := r.steps then
        let (s0, d0) := counted.getD (0, 0)
        counted := some (s0 + s, d0 + d)
      for f in r.findings do
        if let (some msg, some rg) := (f.message, f.range) then
          IO.eprintln s!"{lbl}:{rg.start.line + 1}:{rg.start.character + 1}: {f.rule}: {msg}"
      let (new, n) := rewrite text r.findings args.shorter
      if n == 0 || new == text then continue
      if args.bench > 0 then
        let mut times : Array (Array Float) := #[#[], #[]]
        for i in [:args.bench] do
          for variant in (if i % 2 == 0 then [0, 1] else [1, 0]) do
            let t ← lakeCheck path (if variant == 0 then text else new)
            times := times.modify variant (·.push t)
        IO.eprintln s!"{lbl}: original {fmt2 (median times[0]!)}s, rewritten {fmt2 (median times[1]!)}s (median of {args.bench} Lake checks each)"
      else if args.check then verify path new
      if args.apply then
        if atomic then pending := pending.push (path, original, new) else save path original new
      else IO.print (unifiedDiff text new s!"a/{lbl}" s!"b/{lbl}")
      count := count + n
    catch e =>
      IO.eprintln s!"{lbl}: {e}"
      failed := failed + 1
  if atomic && !pending.isEmpty then
    if failed > 0 then
      IO.eprintln s!"wrote none of the {pending.size} rewritten files, since their edits depend on each other"
      count := 0
    else
      for (path, original, new) in pending do
        try save path original new
        catch e => IO.eprintln s!"{← label path}: {e}"; failed := failed + 1
  if let some (s, d) := counted then IO.eprintln s!"counted: {s} tactic steps, {d} declarations before the edits"
  IO.eprintln s!"{count} edits, {skipped} unparsed commands, {failed} failed files"
  return if failed > 0 then 1 else 0

/-- Checking against skeletons: no build needed. -/
def skeletonVerify (an : Analyzer) (path : FilePath) (new : String) : IO Unit := do
  let errors ← an.check path new
  unless errors.isEmpty do
    if !(← an.check path (← IO.FS.readFile path)).isEmpty then
      throw <| IO.userError ("cannot check: the file as written does not elaborate against skeletons either\n" ++
        "\n".intercalate errors.toList)
    throw <| IO.userError ("check failed\n" ++ "\n".intercalate errors.toList)

/-! ## Language server -/

def readMessage (s : IO.FS.Stream) : IO (Option Json) := do
  let mut length := none
  repeat
    let line ← s.getLine
    if line.isEmpty then return none
    if line == "\r\n" || line == "\n" then break
    if let [k, v] := line.splitOn ":" then
      if k.trimAscii.toString.toLower == "content-length" then length := v.trimAscii.toString.toNat?
  let some n := length | throw <| IO.userError "missing Content-Length"
  let mut body := ByteArray.empty
  while body.size < n do
    let chunk ← s.read (n - body.size).toUSize
    if chunk.isEmpty then return none
    body := body ++ chunk
  let some text := String.fromUTF8? body | throw <| IO.userError "message is not UTF-8"
  return some (← IO.ofExcept (Json.parse text))

def writeMessage (s : IO.FS.Stream) (msg : Json) : IO Unit := do
  let msg := match msg with
    | .obj kvs => Json.obj (kvs.insert "jsonrpc" "2.0")
    | j => j
  let data := msg.compress.toUTF8
  s.write s!"Content-Length: {data.size}\r\n\r\n".toUTF8
  s.write data
  s.flush

def uriPath (uri : String) : Option FilePath := do
  let p ← (uri.dropPrefix? "file://").map (·.toString)
  let bytes := p.toUTF8
  let hex (b : UInt8) : Option UInt8 :=
    if b ≥ 48 && b ≤ 57 then some (b - 48) else if b ≥ 97 && b ≤ 102 then some (b - 87)
    else if b ≥ 65 && b ≤ 70 then some (b - 55) else none
  let mut out := ByteArray.empty
  let mut i := 0
  while i < bytes.size do
    let b := bytes[i]!
    if b == 37 && i + 2 < bytes.size then
      match hex bytes[i+1]!, hex bytes[i+2]! with
      | some h, some l => out := out.push (h * 16 + l); i := i + 3; continue
      | _, _ => pure ()
    out := out.push b
    i := i + 1
  return FilePath.mk (← String.fromUTF8? out)

structure Doc where
  version : Int
  text : String
  findings : Array Finding := #[]
  dedup : Array Finding := #[]

abbrev Item := String × Int × FilePath × String

structure Worker where
  queue : Std.CloseableChannel Item
  task : Task (Except IO.Error Unit)

structure Server where
  env : Environment
  out : IO.FS.Stream
  lock : Std.BaseMutex
  rules : IO.Ref (List String)
  enabled : IO.Ref Bool
  dedup : IO.Ref (Option String)
  root : IO.Ref FilePath
  worker : IO.Ref (Option Worker)
  docs : IO.Ref (Std.HashMap String Doc)
  versioned : IO.Ref Bool
  shutdown : IO.Ref Bool

def Server.locked (s : Server) (x : IO α) : IO α := do
  s.lock.lock
  try x finally s.lock.unlock

/-- Caller holds the lock. -/
def Server.sendDiagnostics (s : Server) (uri : String) : IO Unit := do
  let some doc := (← s.docs.get)[uri]? | return
  let diag (range : Lsp.Range) (sev : Nat) (code msg : String) : Json :=
    Json.mkObj [("range", toJson range), ("severity", sev), ("source", "LeanPerf"),
                ("code", code), ("message", msg)]
  let ds := doc.findings.filterMap (fun f => f.edit.map fun e => diag e.range 4 f.rule (ruleMessage f.rule)) ++
    doc.dedup.filterMap (fun f => f.range.map fun r => diag r 3 f.rule (f.message.getD f.rule))
  writeMessage s.out <| Json.mkObj [("method", "textDocument/publishDiagnostics"), ("params",
    Json.mkObj [("uri", uri), ("version", toJson doc.version), ("diagnostics", Json.arr ds)])]

def Server.stopWorker (s : Server) (wait : Bool) : IO Unit := do
  let some w ← s.worker.get | return
  s.worker.set none
  let _ ← w.queue.close.toBaseIO
  if wait then
    -- Let pending analyses publish, unless they are still elaborating dependencies.
    let deadline := (← IO.monoMsNow) + 60000
    while !(← IO.hasFinished w.task) && (← IO.monoMsNow) < deadline do
      IO.sleep 10

/-- Analyze buffers in the background. The first request decides the pass in `auto` mode and
    elaborates the dependencies; then only the newest version of each buffer is analyzed. -/
def Server.startWorker (s : Server) (mode : String) : IO Worker := do
  let queue ← Std.CloseableChannel.new
  let root ← s.root.get
  let task ← IO.asTask (prio := .dedicated) do
    let some first ← IO.wait (← queue.recv) | return
    let an ← try dedupAnalyzer root #[first.2.2.1] mode
      catch e => IO.eprintln s!"LeanPerf dedup stopped: {e}"; return
    let mut pending := #[first]
    repeat
      while let some x ← queue.tryRecv do pending := pending.push x
      let mut latest : Array Item := #[]
      for x in pending do
        latest := (latest.filter (·.1 != x.1)).push x
      for (uri, version, path, text) in latest do
        let findings ← try pure (← an.analyze path (some text)).findings
          catch e => IO.eprintln s!"LeanPerf dedup: {path}: {e}"; pure #[]
        s.locked do
          let docs ← s.docs.get
          if let some doc := docs[uri]? then
            if doc.version == version && (← s.enabled.get) && (← s.dedup.get).isSome then
              s.docs.set (docs.insert uri { doc with dedup := findings })
              s.sendDiagnostics uri
      let some x ← IO.wait (← queue.recv) | break
      pending := #[x]
    an.close
  return { queue, task }

/-- Caller holds the lock. -/
def Server.publish (s : Server) (uri : String) : IO Unit := do
  let some doc := (← s.docs.get)[uri]? | return
  let rules ← if ← s.enabled.get then s.rules.get else pure []
  let findings := (← (ruleAnalyzer s.env rules).analyze "" (some doc.text)).findings
  s.docs.modify (·.insert uri { doc with findings, dedup := #[] })
  s.sendDiagnostics uri
  let some mode ← s.dedup.get | return
  unless ← s.enabled.get do return
  let some path := uriPath uri | return
  unless ← path.pathExists do return
  if (← path.metadata).type != .file then return
  let w ← match ← s.worker.get with
    | some w => pure w
    | none => do let w ← s.startWorker mode; s.worker.set (some w); pure w
  let _ ← w.queue.send (uri, doc.version, path, doc.text)

def Server.configure (s : Server) (o : Json) : IO Unit := do
  if let .ok r := o.getObjVal? "rules" then
    let some names := (fromJson? (α := List String) r).toOption.filter (·.all ruleNames.contains)
      | throw <| IO.userError s!"expected an array containing rule names from {", ".intercalate ruleNames}"
    s.rules.set names
  if let .ok e := o.getObjVal? "enabled" then
    let .ok b := fromJson? (α := Bool) e | throw <| IO.userError "enabled must be a boolean"
    s.enabled.set b
  if let .ok d := o.getObjVal? "dedup" then
    let mode ← match d with
      | .bool true => pure (some "auto")
      | .bool false => pure none
      | .str m => if dedupModes.contains m then pure (some m) else
          throw <| IO.userError s!"dedup must be a boolean or one of {", ".intercalate dedupModes}"
      | _ => throw <| IO.userError s!"dedup must be a boolean or one of {", ".intercalate dedupModes}"
    if mode != (← s.dedup.get) then s.stopWorker false  -- the next buffer starts the new pass
    s.dedup.set mode

def Server.actions (s : Server) (p : Json) : IO Json := do
  let uri ← IO.ofExcept ((p.getObjVal? "textDocument") >>= (·.getObjValAs? String "uri"))
  let some doc := (← s.docs.get)[uri]? | return Json.arr #[]
  if doc.findings.isEmpty && doc.dedup.isEmpty then return Json.arr #[]
  let only := ((p.getObjVal? "context").toOption.bind fun c => (c.getObjValAs? (Array String) "only").toOption).getD #[]
  let wanted (kind : String) := only.isEmpty || only.any fun k => kind == k || kind.startsWith (k ++ ".")
  let versioned ← s.versioned.get
  let action (title kind : String) (fs : Array Finding) : Json :=
    let edits := Json.arr (fs.filterMap fun f => f.edit.map toJson)
    let ws := if versioned then
        Json.mkObj [("documentChanges", Json.arr #[Json.mkObj [
          ("textDocument", Json.mkObj [("uri", uri), ("version", toJson doc.version)]), ("edits", edits)]])]
      else Json.mkObj [("changes", Json.mkObj [(uri, edits)])]
    Json.mkObj [("title", title), ("kind", kind), ("edit", ws)]
  let mut out := #[]
  if wanted "quickfix" then
    let r ← IO.ofExcept (p.getObjValAs? Lsp.Range "range")
    for f in doc.findings ++ doc.dedup.filter (·.edit.isSome) do
      let some span := f.range <|> f.edit.map (·.range) | continue
      if posLe span.start r.end && posLt r.start span.end then
        let title := match f.«lemma» with
          | some l => if l.isEmpty then f.message.getD (ruleMessage f.rule) else s!"Prove with {l}"
          | none => ruleMessage f.rule
        out := out.push (action title "quickfix" #[f])
  if wanted "source.fixAll.leanPerf" && !doc.findings.isEmpty then
    out := out.push (action "Apply all LeanPerf fixes" "source.fixAll.leanPerf" (independent doc.findings))
  return Json.arr out

/-- Caller holds the lock. Throws `method not found: …` for an unknown method. -/
def Server.handle (s : Server) (method : String) (p : Json) : IO Json := do
  let str (j : Json) (k : String) : IO String := IO.ofExcept (j.getObjValAs? String k)
  match method with
  | "initialize" =>
    let ve := ((p.getObjVal? "capabilities") >>= (·.getObjVal? "workspace") >>= (·.getObjVal? "workspaceEdit") >>=
      (·.getObjValAs? Bool "documentChanges")).toOption.getD false
    s.versioned.set ve
    if let .ok uri := p.getObjValAs? String "rootUri" then
      if let some r := uriPath uri then s.root.set r
    let opts := (p.getObjVal? "initializationOptions").toOption.getD (Json.mkObj [])
    s.configure (if opts.isNull then Json.mkObj [] else opts)
    return Json.mkObj [("capabilities", Json.mkObj [("positionEncoding", "utf-16"), ("textDocumentSync", (1 : Nat)),
        ("codeActionProvider", Json.mkObj [("codeActionKinds", Json.arr #["quickfix", "source.fixAll.leanPerf"])])]),
      ("serverInfo", Json.mkObj [("name", "LeanPerf")])]
  | "shutdown" => s.shutdown.set true; return Json.null
  | "textDocument/didOpen" =>
    let d ← IO.ofExcept (p.getObjVal? "textDocument")
    let uri ← str d "uri"
    s.docs.modify (·.insert uri { version := ← IO.ofExcept (d.getObjValAs? Int "version"), text := ← str d "text" })
    s.publish uri
    return Json.null
  | "textDocument/didChange" =>
    let d ← IO.ofExcept (p.getObjVal? "textDocument")
    let uri ← str d "uri"
    let version ← IO.ofExcept (d.getObjValAs? Int "version")
    let some doc := (← s.docs.get)[uri]? | throw <| IO.userError s!"unknown document {uri}"
    if version > doc.version then
      let changes ← IO.ofExcept (p.getObjValAs? (Array Json) "contentChanges")
      let text ← str changes.back! "text"
      s.docs.modify (·.insert uri { doc with version, text })
      s.publish uri
    return Json.null
  | "textDocument/didClose" =>
    let uri ← IO.ofExcept ((p.getObjVal? "textDocument") >>= (·.getObjValAs? String "uri"))
    s.docs.modify (·.erase uri)
    writeMessage s.out <| Json.mkObj [("method", "textDocument/publishDiagnostics"),
      ("params", Json.mkObj [("uri", uri), ("diagnostics", Json.arr #[])])]
    return Json.null
  | "workspace/didChangeConfiguration" =>
    let settings := ((p.getObjVal? "settings") >>= (·.getObjVal? "leanPerf")).toOption.getD (Json.mkObj [])
    s.configure settings
    for (uri, _) in (← s.docs.get).toList do s.publish uri
    return Json.null
  | "textDocument/codeAction" => s.actions p
  | "initialized" | "$/cancelRequest" | "$/setTrace" => return Json.null
  | m => throw <| IO.userError s!"method not found: {m}"

def runServer (env : Environment) (rules : List String) : IO UInt32 := do
  let s : Server := {
    env, out := ← IO.getStdout, lock := ← Std.BaseMutex.new, rules := ← IO.mkRef rules
    enabled := ← IO.mkRef true, dedup := ← IO.mkRef none, root := ← IO.mkRef (← IO.currentDir)
    worker := ← IO.mkRef none, docs := ← IO.mkRef {}, versioned := ← IO.mkRef false
    shutdown := ← IO.mkRef false }
  let stdin ← IO.getStdin
  repeat
    let some msg ← readMessage stdin | break
    let method := (msg.getObjValAs? String "method").toOption.getD ""
    if method == "exit" then return if ← s.shutdown.get then 0 else 1
    let params := (msg.getObjVal? "params").toOption.getD Json.null
    let params := if params.isNull then Json.mkObj [] else params
    let id? := (msg.getObjVal? "id").toOption
    let reply ← s.locked do
      try return Except.ok (← s.handle method params)
      catch e => return Except.error (toString e)
    if method == "shutdown" then s.stopWorker true
    if let some id := id? then
      let body := match reply with
        | .ok r => [("id", id), ("result", r)]
        | .error e =>
          let code : Int := if e.startsWith "method not found" then -32601 else -32602
          [("id", id), ("error", Json.mkObj [("code", toJson code), ("message", toJson e)])]
      s.locked (writeMessage s.out (Json.mkObj body))
  return 0

/-! ## Entry point -/

/-- `leanperf --golf PATHS`: every pass that shrinks proofs, in the order that lets each feed the
    next. Theorems that nothing uses go first, so that no later pass works on them and more helpers
    have one user to fold into; then duplicates cite the theorem they restate; then rounds of
    `--unused` and `--compress` take steps and declarations out of proofs until a round changes
    nothing; and last `--tactics` makes the remaining steps cheaper. Each pass is this program run
    again, and writes only edits that Lean has checked. -/
def golf (argv : List String) : IO UInt32 := do
  let mut cosmetic := false
  let mut strip := false
  let mut unused := true
  let mut optimize := true
  let mut speed := false
  let mut rounds := 6
  let mut extra : Array String := #[]
  let mut paths : Array String := #[]
  let mut rest := argv.filter (· != "--golf")
  while let a :: r := rest do
    rest := r
    match a with
    | "--cosmetic" => cosmetic := true
    | "--strip-comments" => strip := true
    | "--keep-unused" => unused := false
    | "--no-optimize" => optimize := false
    | "--speed" => speed := true
    | "--rounds" | "--jobs" =>
      let v :: r := rest | IO.eprintln s!"leanperf: error: {a} needs a value"; return 2
      rest := r
      if a == "--rounds" then rounds := v.toNat! else extra := extra ++ #[a, v]
    | _ =>
      if a.startsWith "-" then IO.eprintln s!"leanperf: error: --golf does not take {a}"; return 2
      paths := paths.push a
  if paths.isEmpty then IO.eprintln "leanperf: error: --golf needs paths"; return 2
  let files ← Project.files (paths.map FilePath.mk)
  let size : IO Nat := files.foldlM (fun n p => return n + (← IO.FS.readBinFile p).size) 0
  let mut failed := false
  let pass (args : Array String) : IO (Nat × Bool) := do
    let o ← IO.Process.output { cmd := (← IO.appPath).toString, args := args ++ extra ++ paths }
    let summary := (o.stderr.splitOn "\n").reverse.find? (·.endsWith "failed files")
    let n := (summary.bind (·.splitOn " edits" |>.head?.bind String.toNat?)).getD 0
    if o.exitCode != 0 then
      IO.eprintln s!"{" ".intercalate args.toList}: {(o.stderr.trimAscii.toString.splitOn "\n").getLastD ""}"
    return (n, o.exitCode != 0)
  -- Steps and declarations, from a pass that only parses.
  let counts : IO (Option (Nat × Nat)) := do
    let o ← IO.Process.output { cmd := (← IO.appPath).toString,
                                args := #["--layout", "--rules", "joinLines"] ++ extra ++ paths }
    let some l := (o.stderr.splitOn "\n").find? (·.startsWith "counted: ") | return none
    match (l.drop 9).toString.splitOn " " with
    | s :: _ :: _ :: d :: _ => return (s.toNat?.bind fun s => (d.toNat?.map (s, ·)))
    | _ => return none
  let describe (c : Option (Nat × Nat)) (bytes : Nat) : String :=
    match c with
    | some (s, d) => s!"{s} tactic steps, {d} declarations, {bytes} bytes"
    | none => s!"{bytes} bytes"
  let before ← counts
  let bytes0 ← size
  IO.println s!"start: {describe before bytes0}"
  if strip then
    let (n, f) ← pass #["--layout", "--rules", "stripComments,joinLines", "--apply", "--check"]
    failed := failed || f
    IO.println s!"comments: {n} edits, {← size} bytes"
  if unused then
    let (n, f) ← pass #["--unused", "--check", "--apply"]
    failed := failed || f
    IO.println s!"unused theorems: {n} edits, {← size} bytes"
  let (n, f) ← pass #["--dedup", "--check", "--apply"]
  failed := failed || f
  IO.println s!"duplicates: {n} edits, {← size} bytes"
  for i in [1:rounds + 1] do
    let (u, f) ← if unused && i > 1 then pass #["--unused", "--check", "--apply"] else pure (0, false)
    failed := failed || f
    let (c, f) ← pass (#["--compress", "--apply"] ++ (if cosmetic then #["--cosmetic"] else #[]))
    failed := failed || f
    let (l, f) ← if cosmetic then pass #["--layout", "--apply", "--check"] else pure (0, false)
    failed := failed || f
    IO.println s!"round {i}: {u} unused, {c} compress and {l} layout edits, {← size} bytes"
    if u + c + l == 0 then break
  if optimize then
    -- Cheaper tactics that add no bytes, unless speed matters more than size.
    let (n, f) ← pass (#["--tactics", "--apply", "--check"] ++ (if speed then #[] else #["--shorter"]))
    failed := failed || f
    IO.println s!"cheaper tactics: {n} edits, {← size} bytes"
  IO.println s!"end: {describe (← counts) (← size)} (from {describe before bytes0})"
  return if failed then 1 else 0

unsafe def run (argv : List String) : IO UInt32 := do
  if argv.contains "--golf" then return ← golf argv
  if argv == ["--list-lints"] then
    for lint in Lints.catalog do IO.println s!"{lint.name}\t{lint.group}\t{lint.description}"
    return 0
  let args ← match parseArgs argv with
    | .ok a => pure a
    | .error "help" => IO.print usage; return 0
    | .error e => IO.eprint usage; IO.eprintln s!"leanperf: error: {e}"; return 2
  try
    if args.unused then
      let paths ← Project.files args.paths
      return ← runBatch paths args (← unusedAnalyzer (← IO.currentDir) paths) (atomic := true)
        fun p t => discard <| lakeCheck p t
    if args.dedup || args.tactics || args.layout || args.propose.isSome then
      let paths ← Project.files args.paths
      let root ← IO.currentDir
      let an ← if args.tactics || args.layout || args.propose.isSome then
          elaboratedAnalyzer root paths (jobs := args.jobs)
            (tacticSaving := args.minSaving) (shorter := args.shorter) (compress := args.compress)
            (layout := args.layout) (propose := args.propose)
            (disabled := (Lints.names "tactics" ++ Lints.names "compress" ++ Lints.names "layout" ++
              Lints.names "propose").filter
              (!args.rules.contains ·))
        else dedupAnalyzer root paths (args.dedupPass.getD "auto") args.jobs args.rules
      try runBatch paths args an (skeletonVerify an) finally an.close
    else
      let env ← grammarEnv
      if args.lsp then return ← runServer env args.rules
      runBatch (← Project.files args.paths) args (ruleAnalyzer env args.rules) fun p t => discard <| lakeCheck p t
  catch e =>
    IO.eprintln (toString e)
    return 1

end LeanPerf.Cli
