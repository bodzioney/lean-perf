import LeanPerf.Cli
import LeanPerf.SyntaxDedup

/-! Integration tests: run with `lake test`. Each test runs the `leanperf` executable on a copy of a
fixture and checks its output and its effect on the files. -/

open Lean System LeanPerf

structure Out where
  code : UInt32
  out : String
  err : String

def root : IO FilePath := IO.currentDir
def exe : IO FilePath := return (← root) / ".lake" / "build" / "bin" / "leanperf"

def run (args : Array String) (cwd : Option FilePath := none) (input? : Option String := none) : IO Out := do
  let o ← IO.Process.output { cmd := (← exe).toString, args, cwd := (← cwd.getDM root) } input?
  return { code := o.exitCode, out := o.stdout, err := o.stderr }

def sh (cmd : String) (args : Array String) (cwd : FilePath) : IO Out := do
  let o ← IO.Process.output { cmd, args, cwd }
  return { code := o.exitCode, out := o.stdout, err := o.stderr }

def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
def count (hay needle : String) : Nat := (hay.splitOn needle).length - 1

def check (cond : Bool) (msg : String) : IO Unit := unless cond do throw <| IO.userError msg
def checkNot (cond : Bool) (msg : String) : IO Unit := check (!cond) msg
def ok (o : Out) : IO Unit := check (o.code == 0) s!"exit {o.code}\n{o.err}"
def hasErr (o : Out) (s : String) : IO Unit := check (has o.err s) s!"stderr lacks {s.quote}\n{o.err}"
def hasOut (o : Out) (s : String) : IO Unit := check (has o.out s) s!"stdout lacks {s.quote}\n{o.out}"

partial def copyTree (src dst : FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    if e.fileName == ".lake" then continue
    if ← e.path.isDir then copyTree e.path (dst / e.fileName)
    else IO.FS.writeBinFile (dst / e.fileName) (← IO.FS.readBinFile e.path)

def withTemp (f : FilePath → IO α) : IO α := do
  let d ← IO.FS.createTempDir
  try f (← IO.FS.realPath d) finally IO.FS.removeDirAll d

/-- A copy of the dedup fixture project, with nothing built. -/
def withFixture (f : FilePath → IO α) : IO α := withTemp fun d => do
  let r := d / "fixture"
  copyTree ((← root) / "tests" / "dedup") r
  f r

def lsp (msgs : Array Json) (cwd : Option FilePath := none) : IO (UInt32 × Array Json) := do
  let child ← IO.Process.spawn { cmd := (← exe).toString, args := #["--lsp"], cwd := (← cwd.getDM root),
                                 stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let s := IO.FS.Stream.ofHandle stdin
  for m in msgs do Cli.writeMessage s m
  let _ := stdin  -- dropped here: closes the server's input
  let out := IO.FS.Stream.ofHandle child.stdout
  let mut replies := #[]
  repeat
    let some m ← Cli.readMessage out | break
    replies := replies.push m
  return (← child.wait, replies)

def msg (method : String) (params : Json) (id? : Option Nat := none) : Json :=
  Json.mkObj ([("method", toJson method), ("params", params)] ++ (id?.map fun i => [("id", toJson i)]).getD [])

def get (j : Json) (path : List String) : Json := path.foldl (fun j k => (j.getObjVal? k).toOption.getD Json.null) j

/-! ## Syntax rules -/

def checkedPreview : IO Unit := do
  let f := (← root) / "tests" / "Examples.lean"
  let original ← IO.FS.readBinFile f
  let r ← run #["--check", f.toString]
  ok r; hasErr r "3 edits"; hasOut r "+  have hObtained' := f"
  check ((← IO.FS.readBinFile f) == original) "file changed"

def staticApplyNeverLoadsTheProject : IO Unit := withTemp fun d => do
  let marker := d / "executed"
  IO.FS.writeFile (d / "lean-toolchain") "intentionally-unavailable"
  IO.FS.writeFile (d / "lakefile.lean") "invalid project configuration"
  let f := d / "Example.lean"
  let src := ("import Missing.Dependency\n#eval IO.FS.writeFile \"" ++ marker.toString ++ "\" \"ran\"\n" ++
    "/- example (x : Nat) : x = x := by simp -/\n" ++
    "def quoted := \"example (x : Nat) : x = x := by simp\"\n" ++
    "example (𝒳 : Nat) : 𝒳 = 𝒳 := by simp\n" ++
    "example (x : Nat) : 0 + x = x := by simp\n" ++
    "example (x : Nat) : x = x := by\n  first | simp | rfl\n" ++
    "example (h : True) : True := by simpa using h\n")
  let original := "\r\n".intercalate (src.splitOn "\n")
  IO.FS.writeFile f original
  let r ← run #["--apply", "--rules", "simpRfl", d.toString] d
  ok r
  let expected := "𝒳 := by rfl".intercalate (original.splitOn "𝒳 := by simp")
  check ((← IO.FS.readFile f) == expected) s!"unexpected result:\n{← IO.FS.readFile f}"
  checkNot (← marker.pathExists) "project code ran"
  let again ← run #["--rules", "simpRfl", f.toString] d
  ok again; check (again.out == "") again.out

def reflexivityTerm : IO Unit := withTemp fun d => do
  let path := d / "Reflexive.lean"
  let src := "example (n : Nat) : n = n := by\n  rfl\nexample (n : Nat) : n = n := by /- keep -/ rfl\n" ++
    "example (P : Prop) : P ↔ P := by rfl\n"
  IO.FS.writeFile path src
  let r ← run #["--rules", "rflTerm", "--shorter", "--check", "--apply", path.toString]
  ok r
  check ((← IO.FS.readFile path) == "rfl".intercalate (src.splitOn "by\n  rfl")) (← IO.FS.readFile path)

def failedCheckPreservesSource : IO Unit := withTemp fun d => do
  let f := d / "Broken.lean"
  IO.FS.writeFile f "example (x : Nat) : x = x := by simp\nexample : False := by exact True.intro\n"
  let original ← IO.FS.readBinFile f
  let r ← run #["--apply", "--check", f.toString]
  check (r.code != 0) "check passed"; hasErr r "Lake check failed"
  check ((← IO.FS.readBinFile f) == original) "file changed"

def languageServer : IO Unit := do
  let body := "example (𝒳 : Nat) : 𝒳 = 𝒳 := by simp\n"
  let uri := "file:///unsaved%20proof.lean"
  let doc := Json.mkObj [("uri", uri)]
  let col : Nat := ((body.splitOn "simp")[0]!).foldl (fun (n : Nat) c => n + if c.toNat > 0xFFFF then 2 else 1) 0
  let caret := Json.mkObj [("line", (0 : Nat)), ("character", col)]
  let params := Json.mkObj [("textDocument", doc), ("range", Json.mkObj [("start", caret), ("end", caret)]),
    ("context", Json.mkObj [("diagnostics", Json.arr #[])])]
  let fixAll := Json.mkObj [("textDocument", doc), ("range", Json.mkObj [("start", caret), ("end", caret)]),
    ("context", Json.mkObj [("only", Json.arr #["source.fixAll"]), ("diagnostics", Json.arr #[])])]
  let (code, out) ← lsp #[
    msg "initialize" (Json.mkObj [("capabilities", Json.mkObj [("workspace", Json.mkObj [("workspaceEdit",
      Json.mkObj [("documentChanges", true)])])]), ("initializationOptions", Json.mkObj [("rules", Json.arr #["simpRfl"])])]) (some 1),
    msg "initialized" (Json.mkObj []),
    msg "textDocument/didOpen" (Json.mkObj [("textDocument", Json.mkObj [("uri", uri), ("version", (1 : Nat)),
      ("languageId", "lean"), ("text", body)])]),
    msg "textDocument/codeAction" params (some 2),
    msg "textDocument/codeAction" fixAll (some 3),
    msg "workspace/didChangeConfiguration" (Json.mkObj [("settings", Json.mkObj [("leanPerf", Json.mkObj [("enabled", false)])])]),
    msg "textDocument/codeAction" params (some 4),
    msg "workspace/didChangeConfiguration" (Json.mkObj [("settings", Json.mkObj [("leanPerf", Json.mkObj [("enabled", true)])])]),
    msg "textDocument/didChange" (Json.mkObj [("textDocument", Json.mkObj [("uri", uri), ("version", (2 : Nat))]),
      ("contentChanges", Json.arr #[Json.mkObj [("text", "rfl".intercalate (body.splitOn "simp"))]])]),
    msg "textDocument/codeAction" params (some 5),
    msg "textDocument/didClose" (Json.mkObj [("textDocument", doc)]),
    msg "shutdown" Json.null (some 6),
    msg "exit" Json.null]
  check (code == 0) s!"exit {code}"
  let reply (i : Nat) := ((out.find? fun m => get m ["id"] == toJson i).map (get · ["result"])).getD Json.null
  let notes := out.filter fun m => (get m ["id"]).isNull
  check (get (reply 1) ["capabilities", "positionEncoding"] == "utf-16") "encoding"
  let diag := ((get notes[0]! ["params", "diagnostics"]).getArr?.toOption.getD #[])[0]!
  check (get diag ["code"] == "simpRfl") "code"
  check (get diag ["range", "start"] == caret) "caret"
  let some #[quick, fixAll'] := (reply 2).getArr?.toOption | throw <| IO.userError s!"actions {reply 2}"
  check (get quick ["kind"] == "quickfix") "kind"
  let change := ((get quick ["edit", "documentChanges"]).getArr?.toOption.getD #[])[0]!
  check (get change ["textDocument"] == Json.mkObj [("uri", uri), ("version", (1 : Nat))]) "versioned"
  check (get change ["edits"] == Json.arr #[Json.mkObj [("range", get diag ["range"]), ("newText", "rfl")]]) "edits"
  check (reply 3 == Json.arr #[fixAll']) "fixAll"
  check (reply 4 == Json.arr #[]) "disabled"
  check (reply 5 == Json.arr #[]) "fixed"
  check (get notes.back! ["params", "diagnostics"] == Json.arr #[]) "closed"

/-! ## Skeleton builds -/

def native (r : FilePath) (args : Array String) : IO Out := run (#["--project"] ++ args) r

def cacheReuse : IO Unit := withFixture fun r => do
  let src := r / "Fixture"
  IO.FS.writeFile (src / "Leaf.lean") "import Fixture.Other\nimport Fixture.Twin\n"
  IO.FS.writeFile (src / "Alone.lean") "def alone := 0\n"
  let build (hits misses : Nat) (jobs := 2) : IO Unit := do
    let o ← native r #["--build-only", s!"--jobs={jobs}", "Fixture"]
    ok o; hasErr o s!"{hits} reused, {misses} built"
  build 0 6; build 6 0 (jobs := 1)
  let base := src / "Base.lean"
  -- Change the content but keep the modification time.
  let _ ← sh "cp" #["-p", base.toString, (r / "stamp").toString] r
  IO.FS.writeFile base ((← IO.FS.readFile base) ++ "\n-- input content changed\n")
  let _ ← sh "touch" #["-r", (r / "stamp").toString, base.toString] r
  build 1 5; build 6 0
  let config := r / "lakefile.toml"
  IO.FS.writeFile config ("autoImplicit = true".intercalate ((← IO.FS.readFile config).splitOn "autoImplicit = false"))
  build 0 6
  checkNot (← (r / ".lake" / "build").pathExists) "Lake built"

def failedSkeletonRetried : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Other.lean"
  for (src, reason) in [("import Fixture.Base\ndef bad := missingName\n", "missingName"),
                        ("import Fixture.Other\n", "cyclic project import")] do
    IO.FS.writeFile path src
    let o ← native r #["--build-only", path.toString]
    check (o.code != 0) "succeeded"; hasErr o reason
  for e in ← (r / ".lake" / "leanperf" / "objects").readDir do
    checkNot (has e.fileName ".tmp-") s!"leftover {e.fileName}"
  IO.FS.writeFile path "import Fixture.Base\ndef fixed := 1\n"
  let o ← native r #["--build-only", path.toString]
  ok o; hasErr o "1 reused, 1 built"

def moduleParts : IO Unit := withFixture fun r => do
  IO.FS.writeFile (r / "Fixture" / "Provider.lean") "module\npublic import Lean\npublic meta def probe : Nat := 7\n"
  IO.FS.writeFile (r / "Fixture" / "Consumer.lean")
    "module\npublic meta import Fixture.Provider\nrun_cmd unless probe == 7 do throwError \"wrong value\"\n"
  for hits in [0, 2] do
    let o ← native r #["--build-only", "Fixture/Consumer.lean"]
    ok o; hasErr o s!"{hits} reused"
  checkNot (← (r / ".lake" / "build").pathExists) "Lake built"

def workersOverlap : IO Unit := withFixture fun r => do
  let mut paths := #[]
  for (name, peer) in [("Left", "Right"), ("Right", "Left")] do
    let p := r / s!"{name}.lean"
    IO.FS.writeFile p (s!"import Lean\nrun_cmd do\n  IO.FS.writeFile \"{name}.started\" \"\"\n" ++
      s!"  for _ in [:500] do\n    if ← System.FilePath.pathExists \"{peer}.started\" then return\n" ++
      "    IO.sleep 20\n  throwError \"independent module never started\"\n")
    paths := paths.push p.toString
  ok (← native r (#["--jobs=2", "--build-only"] ++ paths))
  for n in ["Left", "Right"] do IO.FS.removeFile (r / s!"{n}.started")
  let o ← native r (#["--jobs=1", "--build-only"] ++ paths)
  ok o; hasErr o "2 reused, 0 built"
  for n in ["Left", "Right"] do checkNot (← (r / s!"{n}.started").pathExists) "elaborated again"

def concurrentColdBuilds : IO Unit := withFixture fun r => do
  ok (← sh "lake" #["--no-build", "env", "true"] r)
  let args := #["--project", "--build-only", "--jobs=2", "Fixture"]
  let first ← IO.Process.spawn { cmd := (← exe).toString, args, cwd := r, stdout := .piped, stderr := .piped }
  let second ← run args r
  let firstErr ← first.stderr.readToEnd
  check ((← first.wait) == 0) firstErr
  ok second
  let again ← native r #["--build-only", "Fixture"]
  ok again; hasErr again "4 reused, 0 built"
  check ((← (r / ".lake" / "leanperf" / "objects").readDir).size == 4) "objects"

/-! ## Duplicate theorems -/

def relativeIndices : IO Unit := do
  let key (name src : String) : String :=
    let s := src.toList.toArray
    (SyntaxDedup.canonical #[(some name, some #["T"])] ((SyntaxDedup.tokenize s).map (·.1))).1
  let shadow := key "x" "H (fun (x : F x) => let y := x; y)"
  check (shadow == key "a" "H (fun (b : F a) => let c := b; c)") shadow
  check (has shadow "F #0") shadow
  check (has shadow ":= #0 ; #0") shadow
  check (shadow != key "a" "H (fun (b : F a) => let c := a; c)") "let value"
  check (shadow != key "a" "H (fun (b : F a) => let c := b; b)") "let body"
  check (shadow != key "a" "G (fun (b : F a) => let c := b; c)") "head"

def deBruijnShadowing : IO Unit := withFixture fun r => do
  let src := r / "Fixture"
  IO.FS.writeFile (src / "Relation.lean") "axiom Holds : (Nat → Nat → Nat) → Prop\naxiom witness (f) : Holds f\n"
  IO.FS.writeFile (src / "Original.lean") ("import Fixture.Relation\n" ++
    "theorem original : Holds (fun x => fun y => x) := witness _\n" ++
    "theorem inner : Holds (fun x => fun x => x) := witness _\n")
  IO.FS.writeFile (src / "Renamed.lean") ("import Fixture.Relation\n" ++
    "theorem outerCopy : Holds (fun a => fun b => a) := witness _\n" ++
    "theorem innerCopy : Holds (fun a => fun b => b) := witness _\n")
  let paths := #["Fixture/Original.lean", "Fixture/Renamed.lean"]
  for mode in ["syntax", "elaborate"] do
    let (o, report) ← if mode == "syntax" then do
        let o ← run (#["--dedup-pass", mode] ++ paths) r; pure (o, o.err)
      else do
        let o ← native r (#["--no-general", "--jobs=2"] ++ paths)
        let again ← native r (#["--no-general", "--jobs=1"] ++ paths.reverse)
        check (again.out == o.out) "nondeterministic"; hasErr again "3 reused, 0 built"
        pure (o, o.out)
    ok o
    check (has report "outerCopy restates original") report
    check (has report "innerCopy restates inner") report
    checkNot (has report "innerCopy restates original") report
    checkNot (has report "outerCopy restates inner") report

def shorterKeepsShrinking : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Shorten.lean"
  let small := "theorem small (n m : Nat) : n + m = m + n := by omega\n"
  let long := "theorem long (n m : Nat) : n + m = m + n := by\n" ++
    "  have commutative : n + m = m + n := Nat.add_comm n m\n  exact commutative\n"
  IO.FS.writeFile path (small ++ long)
  let o ← run #["--dedup-pass", "elaborate", "--jobs", "1", "--shorter", "--check", "--apply", path.toString] r
  ok o
  let t ← IO.FS.readFile path
  check (has t small && !(has t "have commutative")) t
  check (count o.err "1 edits" == 1) o.err

def unbuiltProject : IO Unit := withFixture fun r => do
  let o ← run #["--dedup", "Fixture"] r
  ok o
  for s in ["elaborating 4 skeletons", "Fixture/Use.lean:3:9: duplicate: my_add_comm restates Nat.add_comm\n",
      "my_lt_le restates (with arguments reordered) Nat.lt_of_lt_of_le\n",
      "wrap_sum restates (with arguments reordered) wrap_two\n",
      "wrap_self restates wrap_refl, which this module does not import",
      "wrap_zero restates wrap_hidden, which is private to another module\n", "wrap_succ restates wrap_one\n",
      "wrap_refl restates wrap_self, which this module does not import", "wrap_mul is a special case of wrap_self\n",
      "Fixture/Twin.lean:4:17: duplicate: wrap_hidden restates wrap_hidden, which is private to another module\n",
      "Fixture/Base.lean:5:17: duplicate: wrap_hidden restates wrap_hidden, which is private to another module\n"] do
    hasErr o s
  check (has o.err "specialCase: two_eq is a special case of Nat.add_one\n" ||
         has o.err "specialCase: two_eq is a special case of Nat.one_add\n") o.err
  for s in ["PANIC", "wrap_one restates", "Base.lean:3:", "wrap_iff"] do checkNot (has o.err s) s!"unexpected {s}"
  for s in ["+theorem my_add_comm (n m : Nat) : n + m = m + n := @Nat.add_comm n m\n",
      "+theorem my_lt_le (a b c : Nat) (h₂ : b ≤ c) (h₁ : a < b) : a < c := @Nat.lt_of_lt_of_le a b c h₁ h₂\n",
      "Wrap (x + y) := @wrap_two x y h k\n", "Wrap (a * 2) := @wrap_self _\n", "Wrap (k + 1) := @wrap_one k hk\n",
      "∀ m, n + m = m + n := by intro m; exact @Nat.add_comm n m\n",
      "a < c := by intro _ _; exact @my_lt_le a b c (by assumption) (by assumption)\n"] do
    hasOut o s
  checkNot (has o.out "+theorem wrap_self") o.out
  check (has o.out "n + m := by intro m n; exact @Nat.add_comm m n\n" ||
         has o.out "n + m := by intro m n; exact @comm_after m n\n") o.out

def syntacticPass : IO Unit := withFixture fun r => do
  let o ← run #["--dedup-pass", "syntax", "Fixture"] r
  ok o; check (o.out == "") o.out
  let found := ((o.err.splitOn "\n").filter (has · ": syntacticDuplicate: ")).map fun l =>
    ": ".intercalate (((l.splitOn ": ").drop 2))
  let expected := ["wrap_hidden restates wrap_hidden, which is private to another module",
    "wrap_hidden restates wrap_hidden, which is private to another module",
    "wrap_refl restates wrap_self, which this module does not import",
    "wrap_self restates wrap_refl, which this module does not import",
    "wrap_sum restates (with arguments reordered) wrap_two",
    "wrap_zero restates wrap_hidden, which is private to another module",
    "wrap_succ restates wrap_one", "lt_le_after restates my_lt_le"].map (· ++ " (matched by syntax)")
  let sort (l : List String) := (l.toArray.qsort (· < ·)).toList
  check (sort found == sort expected) s!"{found}"
  checkNot (← (r / ".lake").pathExists) "Lake ran"

def autoFallsBack : IO Unit := withFixture fun r => do
  IO.FS.writeFile (r / "Fixture" / "Orphan.lean") ("import Missing.Dependency\nimport Fixture.Base\n\n" ++
    "theorem wrap_pair (c d : Nat) (h : Wrap c) (k : Wrap d) : Wrap (c + d) := rfl\n")
  let o ← run #["--dedup", "Fixture/Orphan.lean"] r
  ok o
  hasErr o "Missing.Dependency is not built; using the syntactic pass"
  hasErr o "Fixture/Orphan.lean:4:9: syntacticDuplicate: wrap_pair restates wrap_two (matched by syntax)\n"

def syntacticRunsNothing : IO Unit := withTemp fun d => do
  let marker := d / "executed"
  IO.FS.writeFile (d / "lean-toolchain") "intentionally-unavailable"
  IO.FS.writeFile (d / "lakefile.lean") "invalid project configuration"
  IO.FS.writeFile (d / "Example.lean") ("import Missing.Dependency\n#eval IO.FS.writeFile \"" ++ marker.toString ++
    "\" \"ran\"\n/-- A doc comment with theorem syntax: theorem fake (n : Nat) : n = n -/\n" ++
    "theorem first {α : Type u} (xs : List α) : xs ++ [] = xs := by simp\n" ++
    "theorem second.{v} {β : Type v} (ys : List β) : ys ++ [] = ys := List.append_nil ys\n")
  let o ← run #["--dedup", "Example.lean"] d
  ok o; hasErr o "differs from LeanPerf's"
  hasErr o "Example.lean:5:9: syntacticDuplicate: second restates first (matched by syntax)"
  checkNot (has o.err "fake") o.err
  checkNot (← marker.pathExists) "project code ran"

def checkedApplyWithoutBuild : IO Unit := withFixture fun r => do
  let use := r / "Fixture" / "Use.lean"
  let o ← run #["--dedup", "--check", "--apply", use.toString] r
  ok o; hasErr o "importing 0 built, elaborating 2 skeletons"
  let t ← IO.FS.readFile use
  check (has t "Wrap (k + 1) := @wrap_one k hk\n" && has t ":= by intro m; exact @Nat.add_comm n m\n") t
  checkNot (← (r / ".lake" / "build").pathExists) "Lake built"

def checkRejectsWrongProof : IO Unit := withFixture fun r => do
  let use := r / "Fixture" / "Use.lean"
  let text ← IO.FS.readFile use
  let wrong := ":= @Nat.le_refl _".intercalate (text.splitOn ":= by omega")
  let request (source : String) := (Json.mkObj [
    ("path", toJson use.toString), ("text", toJson source), ("check", toJson true)]).compress ++ "\n"
  let o ← run #["--project", "--serve", use.toString] r (some (request text ++ request wrong))
  ok o
  let [valid, invalid] := o.out.trimAscii.toString.splitOn "\n" | throw <| IO.userError o.out
  let errors (line : String) := IO.ofExcept <| (Json.parse line) >>= (·.getObjValAs? (Array String) "errors")
  check (← errors valid).isEmpty valid
  let es ← errors invalid
  check (es.size == 1 && es[0]!.startsWith "6:") invalid

def checkedApplyWithBuild : IO Unit := withFixture fun r => do
  ok (← sh "lake" #["build"] r)
  let use := r / "Fixture" / "Use.lean"
  let o ← run #["--dedup", "--check", "--apply", use.toString] r
  ok o; hasErr o "importing 1 built, elaborating 1 skeletons"
  let t ← IO.FS.readFile use
  for s in ["n + m = m + n := @Nat.add_comm n m\n", "Wrap (x + y) := @wrap_two x y h k\n",
            "Wrap (k + 1) := @wrap_one k hk\n", "theorem wrap_self (n : Nat) : Wrap n := rfl\n"] do
    check (has t s) s!"lacks {s}\n{t}"
  let again ← run #["--dedup", use.toString] r
  check (again.out == "") again.out

def lspSyntax : IO Unit := withFixture fun r => do
  let use := r / "Fixture" / "Use.lean"
  let text := (← IO.FS.readFile use) ++ "\ntheorem wrap_pair (c d : Nat) (h : Wrap c) (k : Wrap d) : Wrap (c + d) := rfl\n"
  let uri := s!"file://{use}"
  let (code, out) ← lsp #[
    msg "initialize" (Json.mkObj [("rootUri", toJson s!"file://{r}"), ("capabilities", Json.mkObj []),
      ("initializationOptions", Json.mkObj [("dedup", "syntax"), ("rules", Json.arr #[])])]) (some 1),
    msg "textDocument/didOpen" (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri), ("version", (1 : Nat)),
      ("languageId", "lean"), ("text", toJson text)])]),
    msg "shutdown" Json.null (some 2), msg "exit" Json.null] r
  check (code == 0) s!"exit {code}"
  let msgs := out.filterMap fun m => do
    guard (get m ["method"] == "textDocument/publishDiagnostics")
    (get m ["params", "diagnostics"]).getArr?.toOption
  let all := msgs.foldl (· ++ ·) #[] |>.map (get · ["message"])
  check (all.contains "wrap_pair restates wrap_two (matched by syntax)") s!"{all}"
  checkNot (← (r / ".lake").pathExists) "Lake ran"

def lspElaborated : IO Unit := withFixture fun r => do
  let use := r / "Fixture" / "Use.lean"
  let uri := s!"file://{use}"
  -- Unsaved, and the same as an earlier theorem in its module without reordering.
  let text := ("theorem wrap_add_comm (y x : Nat) (k : Wrap y) (h : Wrap x) :\n    Wrap (x + y) := rfl\n\ntheorem wrap_mul").intercalate
    ((← IO.FS.readFile use).splitOn "theorem wrap_mul")
  let child ← IO.Process.spawn { cmd := (← exe).toString, args := #["--lsp"], cwd := r,
                                 stdin := .piped, stdout := .piped, stderr := .inherit }
  let input := IO.FS.Stream.ofHandle child.stdin
  let output := IO.FS.Stream.ofHandle child.stdout
  let receive (p : Json → Bool) : IO Json := do
    repeat
      let some m ← Cli.readMessage output | break
      if p m then return m
    throw <| IO.userError "server stopped"
  Cli.writeMessage input <| msg "initialize" (Json.mkObj [("rootUri", toJson s!"file://{r}"), ("capabilities", Json.mkObj []),
    ("initializationOptions", Json.mkObj [("dedup", true), ("rules", Json.arr #["simpRfl"])])]) (some 1)
  let _ ← receive (get · ["id"] == toJson 1)
  Cli.writeMessage input <| msg "textDocument/didOpen" (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri),
    ("version", (1 : Nat)), ("languageId", "lean"), ("text", toJson text)])])
  let d ← receive fun m => get m ["method"] == "textDocument/publishDiagnostics" &&
    (get m ["params", "diagnostics"]).getArr?.toOption.any (·.size > 0)
  check (get d ["params", "version"] == toJson 1) "version"
  let diags := (get d ["params", "diagnostics"]).getArr?.toOption.getD #[]
  let some added := diags.find? fun x => (get x ["message"]).getStr?.toOption.any (·.startsWith "wrap_add_comm ")
    | throw <| IO.userError s!"{diags}"
  check (get added ["message"] == "wrap_add_comm restates wrap_sum") s!"{added}"
  check (get added ["severity"] == toJson 3 && get added ["code"] == "duplicate") s!"{added}"
  let caret := get added ["range", "start"]
  Cli.writeMessage input <| msg "textDocument/codeAction" (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("range", Json.mkObj [("start", caret), ("end", caret)]), ("context", Json.mkObj [("diagnostics", Json.arr #[])])]) (some 2)
  let a ← receive (get · ["id"] == toJson 2)
  let some #[action] := (get a ["result"]).getArr?.toOption | throw <| IO.userError s!"{a}"
  check (get action ["title"] == "Prove with wrap_sum") s!"{action}"
  let edits := (get action ["edit", "changes", uri]).getArr?.toOption.getD #[]
  check (edits.size == 1 && get edits[0]! ["newText"] == ":= @wrap_sum y x k h") s!"{edits}"
  Cli.writeMessage input <| msg "shutdown" Json.null (some 3)
  let _ ← receive (get · ["id"] == toJson 3)
  Cli.writeMessage input <| msg "exit" Json.null
  check ((← child.wait) == 0) "exit code"

/-! ## Cheaper tactics -/

def tactics : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Tactics.lean"
  IO.FS.writeFile path ("set_option maxHeartbeats 400000 in\ntheorem a (xs : List Nat) : (xs ++ []).length = xs.length := by simp\n\n" ++
    "theorem d (xs ys : List Nat) (h : xs = ys) : (xs ++ []).length = ys.length := by simpa using congrArg List.length h\n")
  let o ← run #["--tactics", "--min-saving", "0", "--check", "--apply", path.toString] r
  ok o
  hasErr o "unneededOption: `set_option maxHeartbeats` is not needed here"
  hasErr o "fasterTactic: simpa using congrArg List.length h → simpa only [List.append_nil] using"
  let t ← IO.FS.readFile path
  check (!(has t "set_option") && has t "simpa only [List.append_nil] using congrArg List.length h") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def tacticCache : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Leaf.lean"
  let base := r / "Fixture" / "Base.lean"
  let marker := r / "replays"
  let source := "import Lean\nimport Fixture.Base\n" ++
    "run_cmd IO.FS.withFile \"replays\" .append fun h => h.putStrLn \"ran\"\n" ++
    "theorem leaf (xs ys : List Nat) (h : xs = ys) : (xs ++ []).length = ys.length := by simpa using congrArg List.length h\n"
  IO.FS.writeFile path source
  let scan (saving : Nat) := run #["--tactics", "--min-saving", toString saving,
    path.toString, base.toString, path.toString] r
  let first ← scan 0
  ok first; hasErr first "1 built"; hasErr first "fasterTactic"
  let cached ← scan 0
  ok cached; hasErr cached "1 reused, 0 built"
  check (first.out == cached.out && (← IO.FS.readFile marker) == "ran\n") cached.out
  let high ← scan 100000
  ok high; check (high.out == "") high.out
  IO.FS.writeFile base ((← IO.FS.readFile base) ++ "\n-- dependency changed\n")
  ok (← scan 0)
  check ((← IO.FS.readFile marker) == "ran\nran\nran\n") "threshold or dependency cache key"
  IO.FS.writeFile path (source ++ "example : False := True.intro\n")
  for _ in [:2] do
    let broken ← scan 0
    check (broken.code != 0) "broken tactic input succeeded"
    hasErr broken "1 failed files"
  check ((← IO.FS.readFile marker) == "ran\nran\nran\nran\nran\n") "cached an incomplete analysis"

def arithmeticPremises : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Arithmetic.lean"
  -- Stand-ins let this core-only fixture exercise premise discovery and replay. The unused
  -- local must disappear and the longer explicit proof must not hide a shorter alternative.
  IO.FS.writeFile path ("macro \"nlinarith\" : tactic => `(tactic| first | rfl | rfl | rfl | assumption)\n" ++
    "macro \"linarith\" : tactic => `(tactic| first | rfl | assumption)\n" ++
    "macro \"linarith\" \" only \" \"[\" h:ident \"]\" : tactic => `(tactic| exact $h)\n" ++
    "theorem choose (P Q : Prop) (unused : Q) (needed : P) : P := by nlinarith\n")
  let args := #["--tactics", "--min-saving", "0", "--check", path.toString]
  let fastest ← run args r
  ok fastest; hasOut fastest ": P := by linarith only [needed]\n"
  let shorter ← run (args.push "--shorter") r
  ok shorter; hasOut shorter ": P := by linarith\n"

def proofCompression : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Compress.lean"
  let untouched := "example (P : Prop) (h : P) : P := by /- retain this explanation -/ exact h\n"
  IO.FS.writeFile path ("axiom Tag : Nat → Prop\naxiom tagWitness (n : Nat) : Tag (n + 1)\n" ++
    "theorem previous (x : Nat) : Tag (x + 1) := tagWitness x\n" ++
    "example (y : Nat) : Tag (y + 1) := by\n  have intermediate := tagWitness y\n  exact intermediate\n" ++
    "example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by\n  constructor\n  · exact h.mpr\n  · exact h.mp\n" ++
    "example (P Q : Prop) (h : P) (k : Q) : P ∧ Q := by\n  constructor\n  · exact h\n  · exact k\n" ++ untouched)
  let o ← run #["--compress", "--apply", path.toString] r
  ok o; hasErr o "reuseProof"
  let t ← IO.FS.readFile path
  check (has t ": Tag (y + 1) := previous y" || has t ": Tag (y + 1) := tagWitness y") t
  check (has t ": Q ↔ P := Iff.symm h" || has t ": Q ↔ P := h.symm") t
  check (has t ": P ∧ Q := ⟨h, k⟩" && has t untouched) t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def overlappingSavings : IO Unit := do
  let change (a b : Nat) (s : String) : Cli.Finding := {
    rule := "test", edit := some { range := ⟨⟨0, a⟩, ⟨0, b⟩⟩, newText := s } }
  let src := "αβγδεζηθ"
  let outer := change 0 8 "some long text"
  let inner := #[change 0 4 "a", change 4 8 "b"]
  check (Cli.rewrite src (inner.push outer) true == ("ab", 2)) "missed disjoint savings"
  check (Cli.rewrite src (inner.push (change 0 8 "x")) true == ("x", 1)) "missed outer savings"

def tests : List (String × IO Unit) := [
  ("checked preview", checkedPreview), ("static apply never loads the project", staticApplyNeverLoadsTheProject),
  ("reflexivity term", reflexivityTerm), ("failed check preserves source", failedCheckPreservesSource),
  ("language server", languageServer), ("cache reuse and invalidation", cacheReuse),
  ("failed or cyclic skeleton retried", failedSkeletonRetried), ("module parts", moduleParts),
  ("workers overlap", workersOverlap), ("concurrent cold builds", concurrentColdBuilds),
  ("relative indices", relativeIndices), ("de Bruijn shadowing", deBruijnShadowing),
  ("shorter keeps shrinking proofs", shorterKeepsShrinking), ("unbuilt project", unbuiltProject),
  ("syntactic pass", syntacticPass), ("auto falls back", autoFallsBack),
  ("syntactic pass runs nothing", syntacticRunsNothing), ("checked apply without a build", checkedApplyWithoutBuild),
  ("check rejects a wrong proof", checkRejectsWrongProof), ("checked apply with a build", checkedApplyWithBuild),
  ("language server, syntax pass", lspSyntax), ("language server, elaborated pass", lspElaborated),
  ("cheaper tactics", tactics), ("tactic cache and dependency skeletons", tacticCache),
  ("arithmetic premise selection", arithmeticPremises), ("proof compression", proofCompression),
  ("maximum nonoverlapping savings", overlappingSavings)]

def main (args : List String) : IO UInt32 := do
  ok (← sh "lake" #["build", "leanperf"] (← root))
  let mut failed := 0
  for (name, t) in tests do
    if !args.isEmpty && !args.any (has name ·) then continue
    try
      t
      IO.println s!"ok    {name}"
    catch e =>
      IO.println s!"FAIL  {name}: {e}"
      failed := failed + 1
    (← IO.getStdout).flush
  IO.println s!"{failed} failed"
  return if failed > 0 then 1 else 0
