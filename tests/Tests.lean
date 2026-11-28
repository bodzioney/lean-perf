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

/-- Run LeanPerf. Its proposers are off unless `env` turns them on, so that what a test expects
    does not depend on the dictionary that comes with LeanPerf. -/
def run (args : Array String) (cwd : Option FilePath := none) (input? : Option String := none)
    (env : Array (String × Option String) := #[("LEANPERF_PAIR_MODEL", some "")]) : IO Out := do
  let o ← IO.Process.output { cmd := (← exe).toString, args, cwd := (← cwd.getDM root), env } input?
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

/-- A checkout rewrites a source without changing it. Its `.olean` is then older than the source, but
    Lake's hashes show it is current, so it is imported rather than replaced by a skeleton. -/
def touchedSourceStillBuilt : IO Unit := withFixture fun r => do
  ok (← sh "lake" #["build"] r)
  let base := r / "Fixture" / "Base.lean"
  -- Rewrite the dependency with the same text, a second later than its `.olean`.
  ok (← sh "sleep" #["1"] r)
  IO.FS.writeFile base (← IO.FS.readFile base)
  let o ← run #["--dedup", (r / "Fixture" / "Use.lean").toString] r
  ok o; hasErr o "importing 1 built, elaborating 1 skeletons"

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
    "theorem d (xs ys : List Nat) (h : xs = ys) : (xs ++ []).length = ys.length := by simpa using congrArg List.length h\n" ++
    "theorem e (a b : Nat) (h : a = b) : a + 0 = b := by erw [Nat.add_zero, h]\n" ++
    "theorem g (a b : Nat) (h : a < b) : a + 1 ≤ b := by grind\n")
  let o ← run #["--tactics", "--min-saving", "0", "--check", "--apply", path.toString] r
  ok o
  hasErr o "unneededOption: `set_option maxHeartbeats` is not needed here"
  hasErr o "fasterTactic: simpa using congrArg List.length h → simpa only [List.append_nil] using"
  hasErr o "fasterTactic: erw [Nat.add_zero, h] → rw [Nat.add_zero, h]"
  hasErr o "fasterTactic: grind →"
  let t ← IO.FS.readFile path
  check (!(has t "set_option") && has t "simpa only [List.append_nil] using congrArg List.length h" &&
    !has t "erw" && !has t "by grind\n") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def unneededSeals : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Seals.lean"
  let needed := "seal g in\ntheorem needsSeal : g 1 = g 1 := by\n  fail_if_success have : g 1 = 1 := rfl\n  rfl\n"
  IO.FS.writeFile path ("def g (n : Nat) : Nat := n\n\n-- Keeps definitional checks from unfolding `g`.\n" ++
    "seal g in\ntheorem unrelated (n : Nat) : n = n := rfl\n\n" ++ needed)
  let o ← run #["--tactics", "--rules", "unneededSeal", "--check", "--apply", path.toString] r
  ok o; hasErr o "unneededSeal: `seal` is not needed here"; hasErr o "1 edits"
  let t ← IO.FS.readFile path
  check (has t "def g (n : Nat) : Nat := n\n\ntheorem unrelated" && has t needed) t
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
  IO.FS.writeFile path ("macro \"nlinarith\" : tactic => `(tactic| first | rfl | rfl | rfl | exact Or.inl (by assumption))\n" ++
    "macro \"linarith\" : tactic => `(tactic| first | rfl | exact Or.inl (by assumption))\n" ++
    "macro \"linarith\" \" only \" \"[\" h:ident \"]\" : tactic => `(tactic| exact Or.inl $h)\n" ++
    "theorem choose (P Q : Prop) (unused : Q) (needed : P) : P ∨ False := by nlinarith\n")
  let args := #["--tactics", "--min-saving", "0", "--check", path.toString]
  let fastest ← run args r
  ok fastest; hasOut fastest ": P ∨ False := by linarith only [needed]\n"
  let shorter ← run (args.push "--shorter") r
  ok shorter; hasOut shorter ": P ∨ False := by linarith\n"

def parallelReplays : IO Unit := withFixture fun r => do
  let write (name peer : String) := do
    let path := r / "Fixture" / (name ++ ".lean")
    IO.FS.writeFile path ("import Lean\nrun_cmd do\n" ++
      s!"  IO.FS.writeFile {name.quote} \"\"\n" ++
      s!"  for _ in [:250] do\n    if ← System.FilePath.pathExists {peer.quote} then break\n    IO.sleep 20\n" ++
      s!"  unless ← System.FilePath.pathExists {peer.quote} do throwError \"missing concurrent replay\"\n" ++
      "set_option maxHeartbeats 500000 in\nexample : True := True.intro\n")
    return path
  let a ← write "First" "Second"
  let b ← write "Second" "First"
  let c := r / "Fixture" / "Third.lean"
  IO.FS.writeFile c "set_option maxHeartbeats 600000 in\nexample : True := True.intro\n"
  let args := #["--tactics", "--check", c.toString, b.toString, a.toString]
  let cold ← run (args ++ #["--jobs", "2"]) r
  ok cold; hasErr cold "3 edits"
  let warm ← run (args ++ #["--jobs", "1"]) r
  ok warm; check (cold.out == warm.out) warm.out
  -- An unsaved buffer can differ from the saved snapshot being analyzed by a worker.
  let req := Json.mkObj [("path", toJson a.toString), ("text", toJson "example : False := True.intro\n")]
  let buffer ← run #["--project", "--serve", "--batch-replay", "--tactics", "--jobs=2",
    a.toString, b.toString] r (some (req.compress ++ "\n"))
  ok buffer
  let reply ← IO.ofExcept (Json.parse buffer.out)
  check ((reply.getObjValAs? Nat "elabErrors").toOption.any (· > 0)) buffer.out

def explicitArithmeticPremises : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Explicit.lean"
  let commented := "example : Picked (3, 4) := by nlinarith [picked /- keep -/ (3, 4)]\n"
  IO.FS.writeFile path ("axiom Picked : Nat × Nat → Prop\naxiom picked (p : Nat × Nat) : Picked p\n" ++
    "syntax \"nlinarith\" \"[\" term,* \"]\" : tactic\n" ++
    "macro_rules | `(tactic| nlinarith [$h:term]) => `(tactic| first | rfl | rfl | rfl | exact $h)\n" ++
    "syntax \"linarith\" \"only\" \"[\" term,* \"]\" : tactic\n" ++
    "macro_rules | `(tactic| linarith only [$h:term]) => `(tactic| exact $h)\n" ++
    "example : Picked (1, 2) := by nlinarith [picked (1, 2)]\n" ++ commented)
  let o ← run #["--tactics", "--min-saving", "0", "--check", "--apply", path.toString] r
  ok o
  let rewritten ← IO.FS.readFile path
  check (has rewritten "by linarith only [picked (1, 2)]\n" && has rewritten commented) rewritten

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

def signatureCompression : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Signatures.lean"
  let comment := "theorem annotated (x : Nat) : @Eq.{1} /- preserve -/ Nat x x := rfl\n"
  IO.FS.writeFile path ("import Lean\nuniverse u\n" ++
    "theorem identityAt : ∀ {A : Type u} [choice : Inhabited A] (item : A), @Eq.{u + 1} A item item := by intros; rfl\n" ++
    "example : 1 = 1 := identityAt (A := Nat) (choice := inferInstance) (item := 1)\n" ++
    "theorem pinned : Nonempty.{2} PUnit.{2} := ⟨PUnit.unit⟩\n" ++
    "run_cmd do\n  let d ← Lean.getConstInfo `pinned\n" ++
    "  unless d.levelParams.isEmpty do throwError \"pinned acquired a universe parameter\"\n" ++ comment)
  let o ← run #["--compress", "--cosmetic", "--apply", path.toString] r
  ok o; hasErr o "shorterSignature"
  let text ← IO.FS.readFile path
  check (has text comment && !has text "@Eq.{u + 1}") text
  ok (← sh "lake" #["env", "lean", path.toString] r)

def relationChains : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Relations.lean"
  IO.FS.writeFile path ("theorem chain (A B C D : Prop) (step : (A ↔ B) ∧ (C ↔ B)) (tail : C ↔ D) : A ↔ D := by\n" ++
    "  constructor\n  · intro a; exact tail.mp (step.2.mpr (step.1.mp a))\n" ++
    "  · intro d; exact step.1.mpr (step.2.mp (tail.mpr d))\n" ++
    "theorem takeRight (P Q : Prop) (h : P ∧ Q) : Q := by\n  obtain ⟨_, q⟩ := h\n  exact q\n")
  -- `simp_all` closes the first theorem in fewer bytes; this test is about the relation chain.
  let o ← run #["--compress", "--cosmetic", "-A", "shorterBlock", "--apply", path.toString] r
  ok o
  let t ← IO.FS.readFile path
  check (has t ": A ↔ D := (step.1.trans step.2.symm).trans tail" && has t ": Q := h.2") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def pruneHaves : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Prune.lean"
  IO.FS.writeFile path ("axiom Secret : Prop\naxiom secret : Secret\naxiom Goal : Prop\naxiom solve : Secret → Goal\n" ++
    "theorem pruned : Goal := by\n  have needed : Secret := secret\n" ++
    "  have unnecessary : True := by\n    exact True.intro\n" ++
    "  have annotated : True := by /- keep this explanation -/ trivial\n" ++
    "  apply solve\n  first | assumption | sorry\n")
  -- `unneededStep` deletes the same line, and `termCompile` with `shorterBlock` take out more steps
  -- than the deletion; this test is about `unusedHave`.
  let o ← run #["--compress", "-A", "unneededStep,termCompile,shorterBlock", "--apply", path.toString] r
  ok o; hasErr o "unusedHave"
  let text ← IO.FS.readFile path
  check (!has text "unnecessary" && has text "have needed" && has text "have annotated") text
  ok (← sh "lake" #["env", "lean", path.toString] r)

def alternativeProof : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Route.lean"
  let protectedProof := "theorem protectedRoute (make : True → Ticket) : Result := by\n" ++
    "  have localTicket := make True.intro\n  exact @issue localTicket\n"
  let annotated := "theorem annotated (a : A) : C := by\n  /- explain the route -/\n  exact finish (via a)\n"
  let source := "axiom A : Prop\naxiom B : Prop\naxiom C : Prop\n" ++
    "axiom via : A → B\naxiom finish : B → C\n" ++
    "theorem route (a : A) (b : B) : C := by\n  have intermediate := via a\n  exact finish intermediate\n" ++
    "class Ticket : Prop where\n  valid : True\naxiom grant : Ticket\nattribute [instance] grant\n" ++
    "axiom Result : Prop\naxiom issue [Ticket] : Result\n" ++ protectedProof ++ annotated
  IO.FS.writeFile path source
  let flags := #["--compress", "--rules", "reprove", path.toString]
  let preview ← run flags r
  ok preview; hasOut preview "+theorem route (a : A) (b : B) : C := finish b"
  check ((← IO.FS.readFile path) == source) "preview modified source"
  let applied ← run (flags.push "--apply") r
  ok applied; hasErr applied "reprove:"
  let rewritten ← IO.FS.readFile path
  check (has rewritten " : C := finish b" && has rewritten protectedProof && has rewritten annotated) rewritten
  let again ← run flags r
  ok again; check again.out.isEmpty again.out
  ok (← sh "lake" #["env", "lean", path.toString] r)

def redundantSteps : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Steps.lean"
  let source := "import Lean\naxiom P : Nat → Prop\naxiom p : ∀ n, P n\ndef Q (n : Nat) : Prop := P n\n" ++
    "axiom ex : ∀ n : Nat, ∃ m, m = n\n" ++
    "theorem typed (n : Nat) : P n ∧ P (n + 1) := by\n" ++
    "  have h : P n := p n\n" ++
    "  have h' : Q (n + 1) := p (n + 1)\n" ++
    "  have : P (n + 2) := p (n + 2)\n" ++
    "  have hb : P (n + 3) := by exact p _\n" ++
    "  obtain ⟨m, hm⟩ : ∃ m,\n      m = n := ex n\n" ++
    "  obtain ⟨k, hk⟩ : ∃ k, k = n := ⟨n, rfl⟩\n" ++
    "  show P n ∧ P (n + 1)\n  exact ⟨h, h'⟩\n" ++
    "theorem reshaped (n : Nat) : Q n := by\n  show P n\n  exact p n\n" ++
    "theorem plain (n : Nat) : n = n := by\n  classical\n  rfl\n" ++
    "theorem needed (q : Prop) : True := by\n  classical\n" ++
    "  have : (if q then 1 else 0) ≤ 1 := by split <;> decide\n  trivial\n" ++
    -- The inferred type reaches the same instance by another path. Only elaborating the whole
    -- theorem shows whether the rest of the proof notices.
    "class Le (α : Type) where le : α → α → Prop\ninstance leNat : Le Nat := ⟨Nat.le⟩\n" ++
    "class Order (α : Type) extends Le α\ninstance : Order Nat := { le := Nat.le }\n" ++
    "axiom refl' {α : Type} [Order α] (a : α) : Le.le a a\n" ++
    "open Lean Elab Meta Tactic in\nelab \"exact_syntactic \" h:ident : tactic => withMainContext do\n" ++
    "  let e ← elabTerm h none\n" ++
    "  unless (← instantiateMVars (← inferType e)) == (← getMainTarget).consumeMData do\n" ++
    "    throwError \"the types differ\"\n  closeMainGoal `exact_syntactic e\n" ++
    "theorem viaOrder : @Le.le Nat leNat 1 1 := by\n  have v : @Le.le Nat leNat 1 1 := refl' 1\n  exact v\n" ++
    "theorem strictOrder : @Le.le Nat leNat 1 1 := by\n  have s : @Le.le Nat leNat 1 1 := refl' 1\n  exact_syntactic s\n"
  IO.FS.writeFile path source
  let o ← run #["--compress", "--rules", "restatedType,redundantShow,unneededClassical", "--apply", path.toString] r
  ok o; hasErr o "6 edits"
  let t ← IO.FS.readFile path
  for kept in ["have h' : Q (n + 1) := p (n + 1)", "have hb : P (n + 3) := by exact p _",
      "obtain ⟨k, hk⟩ : ∃ k, k = n := ⟨n, rfl⟩", "  show P n\n", "  classical\n  have",
      "have s : @Le.le Nat leNat 1 1 := refl' 1"] do
    check (has t kept) s!"removed {kept.quote}\n{t}"
  for dropped in ["have h := p n\n", "have := p (n + 2)\n", "obtain ⟨m, hm⟩ := ex n\n",
      "⟨n, rfl⟩\n  exact ⟨h, h'⟩", "n = n := by\n  rfl", "have v := refl' 1\n"] do
    check (has t dropped) s!"missing {dropped.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

def simpErasures : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Erase.lean"
  let keep := "theorem keep (n : Nat) (h : n + 0 = two) : n = two := by\n  simp [-two_eq] at h\n  exact h\n"
  IO.FS.writeFile path ("def two : Nat := 2\n@[simp] theorem two_eq : two = 2 := rfl\n" ++ keep ++
    "theorem drop (n : Nat) (h : n + 0 = 3) : n = 3 := by\n  simp [-two_eq] at h\n  exact h\n" ++
    "theorem part (n : Nat) (h : n + 0 = two) : n = two := by\n  simp [-two_eq, -Nat.mul_one] at h\n  exact h\n")
  let o ← run #["--compress", "--rules", "unneededErasure", "--apply", path.toString] r
  ok o; hasErr o "2 edits"
  let t ← IO.FS.readFile path
  check (has t keep && has t "n = 3 := by\n  simp at h\n" && has t "simp [-two_eq] at h\n  exact h\n" &&
    !has t "Nat.mul_one") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def shorterBlocks : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Blocks.lean"
  let commented := "theorem commented (a b : Nat) (h : a = b) : a + 0 = b := by\n  rw [Nat.add_zero]\n" ++
    "  -- now it is the hypothesis\n  exact h\n"
  let data := "def d : Nat := by\n  apply Nat.succ\n  exact Nat.zero\n"
  IO.FS.writeFile path ("axiom Hard : Prop\naxiom hard : Hard\n@[irreducible] def f (n : Nat) : Nat := n + 1\n" ++
    "theorem whole (a b : Nat) (h : a = b) : a + 0 = b := by\n  rw [Nat.add_zero]\n  exact h\n" ++
    "theorem bullets (n : Nat) : n + 0 = n ∧ 0 + n = n := by\n  constructor\n" ++
    "  · rw [Nat.add_zero]\n  · rw [Nat.zero_add]\n" ++
    "theorem tail (a b : Nat) (h : a ≤ b) : Hard ∧ a ≤ b + 1 := by\n  refine ⟨hard, ?_⟩\n" ++
    "  apply Nat.le_trans h\n  apply Nat.le_succ\n" ++
    "theorem nested (n : Nat) : Hard ∧ f n ≠ 0 := by\n  refine ⟨hard, ?_⟩\n" ++
    "  have key : f n = n + 1 := by\n    rw [f]\n  rw [key]\n  exact Nat.succ_ne_zero n\n" ++
    "structure Both (p q : Prop) : Prop where\n  l : p\n  r : q\n" ++
    "theorem fanned (a b : Nat) (h : a = b) : Both (a + 0 = b) (b = a + 0) := by\n" ++
    "  constructor\n  · rw [Nat.add_zero]\n    exact h\n  · rw [Nat.add_zero]\n    exact h.symm\n" ++
    commented ++ data ++ "theorem short : 1 = 1 := by rfl\n")
  let o ← run #["--compress", "--rules", "shorterBlock", "--apply", path.toString] r
  ok o
  let t ← IO.FS.readFile path
  for s in ["a + 0 = b := by omega\n", "0 + n = n := by simp\n", "refine ⟨hard, ?_⟩\n  omega\n",
      "(b = a + 0) := by constructor <;> ",
      commented, data, "theorem short : 1 = 1 := by rfl\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  check (!has t "Nat.succ_ne_zero") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def shorterSimp : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "ShorterSimp.lean"
  let needed := "  simp only [f_eq, g_eq] at h\n"
  let commented := "  simp only [Nat.add_zero, /- keep this -/ Nat.zero_add] at h\n"
  let fanned := "  constructor <;> simp [f_eq, g_eq]\n"
  let tiny := "theorem tiny (n : Nat) : n + 0 = n := by simp []\n"
  IO.FS.writeFile path ("set_option linter.unusedSimpArgs false\n" ++
    "axiom P : Nat → Nat → Prop\naxiom marked : Nat → Nat\n" ++
    "@[simp] axiom marked_eq (n : Nat) : marked n = n\n" ++
    "axiom f : Nat → Nat\naxiom g : Nat → Nat\n" ++
    "axiom f_eq (n : Nat) : f n = n\naxiom g_eq (n : Nat) : g n = n\n" ++
    "axiom nested (xs : List Nat) : g xs.length = xs.length\n" ++
    "def wrap (n : Nat) := n\ndef unused (n : Nat) := n\n" ++
    "theorem partialList (n : Nat) (h : P (n + 0) (marked n)) : P n (marked n) := by\n" ++
    "  simp only [Nat.add_zero, Nat.zero_add] at h\n  exact h\n" ++
    "theorem wholeList (n : Nat) : n + 0 = n := by\n  simp only [Nat.add_zero]\n" ++
    "theorem keepBoth (n : Nat) (h : P (f n) (g n)) : P n n := by\n" ++ needed ++ "  exact h\n" ++
    "theorem keepComment (n : Nat) (h : P (n + 0) (marked n)) : P n (marked n) := by\n" ++ commented ++ "  exact h\n" ++
    "theorem dropOnly (n : Nat) (h : P (f n) n) : P n n := by\n" ++
    "  simp only [f_eq, ← (nested [1, 2]), Nat.zero_add] at h\n  exact h\n" ++
    "theorem erasure (n : Nat) (h : P (n + 0) (marked n)) : P n (marked n) := by\n" ++
    "  simp [Nat.add_zero, -marked_eq] at h\n  exact h\n" ++
    "theorem allList (n : Nat) : n + 0 = n := by\n  simp_all only [Nat.add_zero]\n" ++
    "theorem usingList (n : Nat) (h : P n n) : P (n + 0) n := by\n  simpa only [Nat.add_zero] using h\n" ++
    "theorem dsimpList (n : Nat) (h : P (wrap n) n) : P n n := by\n" ++
    "  dsimp only [wrap, unused] at h\n  exact h\n" ++
    "theorem twoGoals (n : Nat) : f n = n ∧ g n = n := by\n" ++ fanned ++ tiny)
  let o ← run #["--compress", "--rules", "shorterSimp", "--apply", path.toString] r
  ok o; hasErr o "7 edits"
  let t ← IO.FS.readFile path
  for s in [needed, commented, fanned, tiny, "  simp only [Nat.add_zero] at h\n", "  simp\n",
      "  simp [f_eq] at h\n", "  simp [-marked_eq] at h\n", "  simp_all\n",
      "  simpa using h\n", "  dsimp [wrap] at h\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

def redundantAscriptions : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Ascriptions.lean"
  let cast := "theorem casted (m : Nat) : ((m : Int) + 1 : Int) = (m : Int) + 1 := by\n  exact rfl\n"
  let needed := "theorem needed : (0 : Int) - 1 < 0 := by\n  have h : (0 : Int) - 1 < 0 := by decide\n  exact h\n"
  IO.FS.writeFile path ("axiom P : Nat → Prop\naxiom p : ∀ n, P n\n" ++
    "theorem pair (n : Nat) : P n ∧ P (n + 1) := by\n  exact ⟨(p n : P n), (p (n + 1) : P (n + 1))⟩\n" ++
    "theorem binders : ∀ n, P n := by\n  exact fun (n : Nat) => p n\n" ++
    "theorem typed : ∀ n, P n := by\n  exact fun n : Nat => p n\n" ++
    "theorem applied (n : Nat) : P (n + 1) := by\n  exact (p (n + 1) : P (n + 1))\n" ++ cast ++ needed ++
    "theorem inferred (n : Nat) : n + 0 = n := by\n  have h := (Nat.add_zero n : n + 0 = n)\n  exact h\n")
  let o ← run #["--compress", "--rules", "redundantAscription", "--apply", path.toString] r
  ok o
  let t ← IO.FS.readFile path
  for s in ["exact ⟨p n, p (n + 1)⟩\n", "binders : ∀ n, P n := by\n  exact fun n => p n\n", "exact fun n => p n\ntheorem applied",
      "exact p (n + 1)\n", cast, needed, "have h := Nat.add_zero n\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

def joinedLines : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Layout.lean"
  let multi := "theorem multi (a : Nat) : a = a := by\n  have h : a = a := rfl\n  exact h\n"
  let long := "theorem long (aaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbb cccccccccccccccccccccccc : Nat) :\n" ++
    "    aaaaaaaaaaaaaaaaaaaa + bbbbbbbbbbbbbbbbbbbbbbbbbbbb ≥ bbbbbbbbbbbbbbbbbbbbbbbbbbbb + 0 := by\n  omega\n"
  let commented := "theorem commented (a : Nat) : a = a := by\n  -- reflexivity\n  rfl\n"
  let bullets := "theorem bullets : True ∧ True := by\n  constructor\n  · trivial\n  · trivial\n"
  IO.FS.writeFile path ("theorem sig (a : Nat)\n    (b : Nat) : a + b = b + a := by\n  omega\n" ++ multi ++
    "theorem term (a b : Nat) (h : a = b) : b = a := by\n  exact\n    h.symm\n" ++ long ++ commented ++
    bullets ++ "def f (n : Nat) : Nat :=\n  n +\n    1\n" ++
    "theorem opens (a b : Nat) (h : a = b) : b = a := by\n  exact\n    Eq.symm\n      h\n")
  let o ← run #["--layout", "--apply", path.toString] r
  ok o
  let t ← IO.FS.readFile path
  for s in ["theorem sig (a : Nat) (b : Nat) : a + b = b + a := by omega\n", multi,
      "theorem term (a b : Nat) (h : a = b) : b = a := by exact h.symm\n", long, commented, bullets,
      "def f (n : Nat) : Nat := n + 1\n", "(h : a = b) : b = a := by exact Eq.symm h\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Comments inside declarations go only when asked for; docstrings, string literals and the
    comments between declarations stay. A bullet takes the step its comment had pushed down. -/
def strippedComments : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Comments.lean"
  let doc := "/-- The docstring stays. -/\ntheorem doc (a : Nat) : a = a := by\n"
  let between := "-- between declarations\n"
  -- Declarations are only parsed, so `variable` naming one fails to elaborate; that must not matter.
  IO.FS.writeFile path ("def CommentCarrier := Nat\nvariable (c : CommentCarrier)\n" ++
    doc ++ "  -- reflexivity\n  rfl -- done\n" ++ between ++
    "theorem bullets : True ∧ True := by\n  constructor\n  · -- the first\n    trivial\n  · trivial\n" ++
    "def s : String := \"-- not a comment\" /- inline -/\n")
  let o ← run #["--layout", "--apply", path.toString] r
  ok o
  check (has (← IO.FS.readFile path) "-- reflexivity") "comments go without --rules"
  let o ← run #["--layout", "--rules", "stripComments", "--apply", path.toString] r
  ok o; hasErr o "stripComments:"
  let t ← IO.FS.readFile path
  for s in [doc ++ "  rfl\n" ++ between, "  · trivial\n  · trivial\n", "def s : String := \"-- not a comment\"\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- A local proof named once is inlined; one named twice stays, and so does one that no inlined
    form of elaborates. `by exact e` becomes `e`, `intro` with `exact` a `fun`, and `.mp` `.1`. -/
def golfRules : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Golf.lean"
  let twice := "theorem twice (a b : Nat) (h : a = b) : b = a ∧ b = a := by\n  have h' : b = a := h.symm\n  exact ⟨h', h'⟩\n"
  IO.FS.writeFile path ("theorem once (a b : Nat) (h : a = b) : b = a := by\n  have h' : b = a := h.symm\n" ++
    "  exact h'\n" ++ twice ++
    "theorem typed (a : Nat) : a + 0 = a := by\n  have h : a + 0 = a := rfl\n  rw [h]\n" ++
    "theorem term (p q : Prop) (hp : p) (h : p → q) : q := by exact h hp\n" ++
    "theorem proj (p q : Prop) (hp : p) (h : p ↔ q) : q := h.mp hp\n" ++
    "theorem intros (p : Prop) : p → p := by\n  intro x\n  exact x\n")
  let o ← run #["--compress", "--rules", "inlineHave,termExact,shortProjection", "--apply", path.toString] r
  ok o; hasErr o "inlineHave:"; hasErr o "termExact:"
  let t ← IO.FS.readFile path
  -- `rw [rfl]` and `rw [(rfl : a + 0 = a)]` both fail: `rfl` proves `a = a`, which rewrites nothing.
  for s in ["b = a := by\n  exact h.symm\n", twice, "have h : a + 0 = a := rfl\n  rw [h]\n", "q := h hp\n",
      "q := h.1 hp\n", "p → p := fun x ↦ x\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Flat destructuring is replaced by projections when the shorter proof elaborates. -/
def golfObtainProjection : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "ObtainProjection.lean"
  let pair := "theorem pair (A B : Prop) (h : A ∧ B) : B ∧ A := by\n"
  let iff := "theorem directions (A B : Prop) (h : A ↔ B) : B ↔ A := by\n"
  let triple := "theorem triple (A B C : Prop) (h : A ∧ B ∧ C) : C ∧ B ∧ A := by\n"
  let wildcard := "theorem wildcard (n m : Nat) (h : n = m ∧ True) : m = n := by\n"
  let keep :=
    "theorem witness (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n := by\n" ++
    "  obtain ⟨n, hn⟩ := h\n  exact ⟨n, hn⟩\n" ++
    "theorem unused (A B : Prop) (h : A ∧ B) : A := by\n" ++
    "  obtain ⟨a, b⟩ := h\n  exact a\n" ++
    "theorem commented (A B : Prop) (h : A ∧ B) : B ∧ A := by\n" ++
    "  obtain ⟨a, b⟩ := h -- keep this\n  exact And.intro b a\n" ++
    "theorem rebound (A B : Prop) (h : A ∧ B) : B ∧ A := by\n" ++
    "  obtain ⟨a, b⟩ := h\n  have h : A ∧ B := ⟨a, b⟩\n  exact And.intro b a\n"
  IO.FS.writeFile path (pair ++ "  obtain ⟨a, b⟩ := h\n  exact And.intro b a\n" ++
    iff ++ "  rcases h with ⟨a, b⟩\n  exact Iff.intro b a\n" ++
    triple ++ "  obtain ⟨a, b, c⟩ := h\n  constructor\n  · exact c\n  · exact And.intro b a\n" ++
    wildcard ++ "  obtain ⟨a, _⟩ := h\n  exact a.symm\n" ++ keep)
  let o ← run #["--compress", "--rules", "obtainProjection", "--apply", path.toString] r
  ok o; hasErr o "obtainProjection:"
  let t ← IO.FS.readFile path
  let expected := pair ++ "  exact And.intro h.2 h.1\n" ++
    iff ++ "  exact Iff.intro h.2 h.1\n" ++
    triple ++ "  constructor\n  · exact h.2.2\n  · exact And.intro h.2.1 h.1\n" ++
    wildcard ++ "  exact h.1.symm\n" ++ keep
  check (t == expected) s!"unexpected projection rewrites\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Structural steps become terms with tactic leaves, preserving comments and unsupported blocks. -/
def golfTermCompile : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "TermCompile.lean"
  let unbulleted := "theorem unbulleted (p q : Prop) (a : p) (b : q) : p ∧ q := by\n" ++
    "  constructor\n  exact a\n  exact b\n"
  let commented := "theorem commented (p : Prop) (h : p) : p ∧ p := by\n" ++
    "  constructor\n  · exact h\n  /- keep this -/\n  · exact h\n"
  let wide := "theorem wide (p : Prop) (firstProofOfTheProposition : p) (secondProofOfTheClaim : p) : p ∧ p := "
  let longName := "proof" ++ String.ofList (List.replicate 46 'X')
  let overwide := s!"theorem overwide (p : Prop) ({longName} : p) : p ∧ p := by\n" ++
    s!"  refine ⟨\n    ?_, ?_⟩\n  · exact {longName}\n  · exact {longName}\n"
  IO.FS.writeFile path (
    "theorem pair (p q : Prop) (a : p) (b : q) : p ∧ q := by\n  constructor\n  · exact a\n  · exact b\n" ++
    "theorem abstract (p : Prop) : p → p ∧ p := by\n  intro x\n  constructor\n  · exact x\n  · exact x\n" ++
    "theorem refined (p : Prop) (h : p) : p ∧ p := by\n  refine ⟨?_, h⟩\n  · exact h\n" ++
    "theorem refinedRest (n : Nat) : 0 + n = n ∧ True := by\n  refine ⟨?_, True.intro⟩\n  simp\n" ++
    "theorem refinedApp (n : Nat) : 0 + n = n ∧ True := by\n  refine And.intro ?_ ?_\n  · simp\n  · exact True.intro\n" ++
    "theorem withSimp (n : Nat) : 0 + n = n ∧ True := by\n  constructor\n  · simp\n  · exact True.intro\n" ++
    wide ++ "by\n  constructor\n  · exact firstProofOfTheProposition\n  · exact secondProofOfTheClaim\n" ++
    unbulleted ++ commented ++ overwide)
  let o ← run #["--compress", "--rules", "termCompile", "--apply", path.toString] r
  ok o; hasErr o "termCompile:"
  let t ← IO.FS.readFile path
  for s in ["p ∧ q := ⟨a, b⟩\n", "p → p ∧ p := fun x ↦ ⟨x, x⟩\n", "p ∧ p := ⟨h, h⟩\n",
      "refinedRest (n : Nat) : 0 + n = n ∧ True := ⟨by simp, True.intro⟩\n",
      "refinedApp (n : Nat) : 0 + n = n ∧ True := And.intro (by simp) True.intro\n",
      "withSimp (n : Nat) : 0 + n = n ∧ True := ⟨by simp, True.intro⟩\n",
      wide ++ "\n  ⟨firstProofOfTheProposition, secondProofOfTheClaim⟩\n", unbulleted, commented, overwide] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Adjacent tactics combine when their locations match and the replacement preserves the layout
    and comments. -/
def golfTacticPairs : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "GolfPairs.lean"
  let different := "  simp only [Nat.zero_add] at h\n  exact h'\n"
  let commented := "  rw [Nat.add_zero]\n  /- keep this -/\n  rw [Nat.zero_add]\n"
  let sameLine := "  rw [Nat.add_zero]; rw [Nat.zero_add]\n"
  let indent := String.ofList (List.replicate 68 ' ')
  let wide := s!"{indent}rw [Nat.add_zero, Nat.zero_add]\n{indent}rw [h]\n"
  IO.FS.writeFile path (
    "theorem simpOnly (a b : Nat) (h : 0 + a = b) : a = b := by\n  simp only [Nat.zero_add] at h\n  exact h\n" ++
    "theorem simpList (a b : Nat) (h : 0 + a = b) : a = b := by\n  simp [Nat.zero_add] at h\n  exact h\n" ++
    "theorem simpBare (a b : Nat) (h : 0 + a = b) : a = b := by\n  simp at h\n  exact h\n" ++
    "theorem rwAt (a b : Nat) (h : 0 + a = b) : a = b := by\n  rw [Nat.zero_add] at h\n  exact h\n" ++
    "theorem mergeGoal (a b : Nat) (h : a = b) : a + 0 = 0 + b := by\n  rw [Nat.add_zero, Nat.zero_add,]\n  rw [h]\n" ++
    "theorem mergeHyp (a b : Nat) (h : a + 0 = 0 + b) : b = a := by\n" ++
    "  rw [Nat.add_zero] at h\n  rw [Nat.zero_add] at h\n  exact h.symm\n" ++
    "theorem different (a b : Nat) (h : 0 + a = b) (h' : a = b) : a = b := by\n" ++ different ++
    "theorem commented (a : Nat) : a + 0 = 0 + a := by\n" ++ commented ++
    "theorem sameLine (a : Nat) : a + 0 = 0 + a := by\n" ++ sameLine ++
    "theorem wide (a b : Nat) (h : a = b) : a + 0 = 0 + b := by\n" ++ wide)
  let o ← run #["--compress", "--rules", "simpaUsing,rwaAt,mergeRw", "--apply", path.toString] r
  ok o; hasErr o "simpaUsing:"; hasErr o "rwaAt:"; hasErr o "mergeRw:"
  let t ← IO.FS.readFile path
  for s in ["  simpa only [Nat.zero_add] using h\n", "  simpa [Nat.zero_add] using h\n", "  simpa using h\n",
      "  rwa [Nat.zero_add] at h\n", "  rw [Nat.add_zero, Nat.zero_add, h]\n",
      "  rw [Nat.add_zero, Nat.zero_add] at h\n  exact h.symm\n", different, commented, sameLine, wide] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- A theorem that only one other uses folds into it as a `have`, by plain name or by dot notation;
    one that two theorems use stays. A wrapper that only applies another theorem takes its proof. -/
def foldedHelpers : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Fold.lean"
  let shared := "theorem sharedFoldStep (a : Nat) : a + 0 = a := Nat.add_zero a\n"
  IO.FS.writeFile path ("theorem foldStep (a : Nat) : a + 0 = a := Nat.add_zero a\n" ++
    "theorem foldUser (b : Nat) : b + 0 = b := by\n  rw [foldStep]\n" ++
    "structure FoldBox where\n  val : Nat\n" ++
    "theorem FoldBox.valNe (x : FoldBox) (h : 0 < x.val) : x.val ≠ 0 := Nat.pos_iff_ne_zero.1 h\n" ++
    "theorem foldDot (x : FoldBox) (h : 0 < x.val) : x.val ≠ 0 := x.valNe h\n" ++ shared ++
    "theorem sharedA (b : Nat) : b + 0 = b := by rw [sharedFoldStep]\n" ++
    "theorem sharedB (b : Nat) : b + 0 = b := sharedFoldStep b\n" ++
    "theorem baseFold (n : Nat) : 0 + n = n := by simp\n" ++
    "theorem wrapFold (n : Nat) : 0 + n = n := baseFold n\n" ++
    "theorem useBaseFold (m : Nat) : 0 + m = m := by rw [baseFold]\n" ++
    "theorem baseIffFold {p : Prop} : p ↔ p := Iff.rfl\n" ++
    "theorem wrapIffFold {p : Prop} : p ↔ p := baseIffFold\n" ++
    "theorem useIffFold (p : Prop) (h : p) : p := baseIffFold.mp h\n")
  let o ← run #["--compress", "--rules", "foldHelper", "--apply", path.toString] r
  ok o; hasErr o "foldHelper:"
  let t ← IO.FS.readFile path
  for s in ["theorem foldUser (b : Nat) : b + 0 = b := by\n  have h0 (a : Nat) : a + 0 = a := Nat.add_zero a\n  rw [h0]\n",
      "x.val ≠ 0 := by\n  have h0 (x : FoldBox) (h : 0 < x.val) : x.val ≠ 0 := Nat.pos_iff_ne_zero.1 h\n  exact h0 x h\n",
      shared, "theorem wrapFold (n : Nat) : 0 + n = n := by simp\n", "rw [wrapFold]",
      -- A use with a field after the name moves to the wrapper too.
      "theorem wrapIffFold {p : Prop} : p ↔ p := Iff.rfl\n", ":= wrapIffFold.mp h\n"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  for s in ["theorem foldStep", "theorem FoldBox.valNe", "theorem baseFold", "theorem baseIffFold"] do
    check (!has t s) s!"{s} should be folded\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Locals a proof binds get the shortest free names; the statement's binders keep theirs. -/
def shortenedNames : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Names.lean"
  IO.FS.writeFile path ("theorem renamed (a b : Nat) (h : a = b) : b = a ∧ b = a := by\n" ++
    "  have symmetric_fact : b = a := h.symm\n  exact ⟨symmetric_fact, symmetric_fact⟩\n")
  let o ← run #["--compress", "--rules", "shortNames", "--apply", path.toString] r
  ok o; hasErr o "shortNames:"
  let t ← IO.FS.readFile path
  check (has t "(h : a = b) : b = a ∧ b = a := by\n  have s : b = a := h.symm\n  exact ⟨s, s⟩\n") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Two adjacent steps become one when the rest of the block still closes the goal with it, and a
    run of steps shrinks to one step by step. -/
def contractedPairs : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Pairs.lean"
  let kept := "theorem kept (a b : Nat) (h : a = b) : b = a := by\n  subst h\n  rfl\n"
  IO.FS.writeFile path ("theorem rws (a b : Nat) (h : a = b) : 0 + a + 0 = b := by\n" ++
    "  rw [Nat.add_zero]\n  rw [Nat.zero_add]\n  exact h\n" ++
    "theorem intros (p q : Prop) (hq : q) : p → p → q := by\n  intro x\n  intro y\n  exact hq\n" ++
    "theorem single (p q : Prop) (hq : q) : p → q := by\n  intro x\n  exact hq\n" ++ kept)
  let o ← run #["--compress", "--rules", "contractPair", "--apply", path.toString] r
  ok o; hasErr o "contractPair:"
  let t ← IO.FS.readFile path
  -- One step in place of two, though `exact fun x y ↦ hq` takes more bytes than its two steps.
  -- `exact fun x ↦ hq` takes as many bytes as `intro x` and `exact hq`, and one step fewer.
  for s in ["  rw [Nat.add_zero, Nat.zero_add]\n  exact h\n", "  exact fun x y ↦ hq\n",
      "p → q := by\n  exact fun x ↦ hq\n", kept] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)
  -- The dictionary that comes with LeanPerf, used when no proposer is named, goes on: it knows
  -- steps for `rw [L]` before `exact h`, such as `rwa [L]`.
  let o ← run #["--compress", "--rules", "contractPair", "--apply", path.toString] r (env := #[])
  ok o
  let t ← IO.FS.readFile path
  check (!has t "  exact h\n" && has t "  exact fun x y ↦ hq\n") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- A proposer is any command; Lean decides which of its rewrites to keep. The first round has only
    unsound or failing candidates, and the second, sent their errors, a correct one. -/
def proposedRewrites : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Propose.lean"
  let short := "theorem short (n : Nat) : n = n := rfl\n"
  IO.FS.writeFile path ("/-- The docstring stays. -/\ntheorem long (a b : Nat) (h : a = b) : b + 0 = a := by\n" ++
    "  have h1 : b = a := h.symm\n  have h2 : b + 0 = b := Nat.add_zero b\n  have h3 : a = a := rfl\n" ++
    "  rw [h2]\n  exact h1\n" ++ short)
  let sig := "theorem long (a b : Nat) (h : a = b) : b + 0 = a"
  let script := r / "propose.sh"
  IO.FS.writeFile script ("#!/bin/sh\ninput=$(cat)\nprintf '%s' \"$input\" >> " ++ (r / "requests.log").toString ++
    "\necho >> " ++ (r / "requests.log").toString ++ "\ncase \"$input\" in\n" ++
    "  *'\"round\":0'*) echo '{\"candidates\": [\"axiom long (a b : Nat) (h : a = b) : b + 0 = a\", " ++
    "\"" ++ sig ++ " := sorry\", \"theorem long (a b : Nat) : True := trivial\", \"" ++ sig ++ " := by simp\"]}' ;;\n" ++
    "  *) echo '{\"candidates\": [\"" ++ sig ++ " := by omega\"]}' ;;\nesac\n")
  discard <| sh "chmod" #["+x", script.toString] r
  let o ← run #["--propose", script.toString, "--apply", path.toString] r
  ok o; hasErr o "rewrite:"
  let t ← IO.FS.readFile path
  check (has t ("/-- The docstring stays. -/\n" ++ sig ++ " := by omega\n" ++ short)) t
  let log ← IO.FS.readFile (r / "requests.log")
  -- One theorem was long enough to send, and the second request carried the errors of the first.
  check (((log.splitOn "\n").filter (!·.isEmpty)).length == 2) log
  check (has log "\"round\":1" && has log "unsolved goals" && !has log "theorem short") log
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- A helper that only the next theorem uses, and that no other module mentions, may be folded in;
    a candidate that drops the theorem the group must keep is rejected. -/
def proposedGroups : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Group.lean"
  let helper := "theorem helper (a b : Nat) (h : a = b) : b = a := by\n  have h1 : b = a := h.symm\n  exact h1\n"
  let main := "theorem main (a b : Nat) (h : a = b) : b + 0 = a := by\n  have h2 : b + 0 = b := Nat.add_zero b\n" ++
    "  rw [h2]\n  exact helper a b h\n"
  IO.FS.writeFile path (helper ++ "\n" ++ main)
  let sig := "theorem main (a b : Nat) (h : a = b) : b + 0 = a"
  let script := r / "propose.sh"
  IO.FS.writeFile script ("#!/bin/sh\ninput=$(cat)\nprintf '%s\\n' \"$input\" >> " ++ (r / "requests.log").toString ++
    "\nprintf '%s\\n' '{\"candidates\": [\"theorem helper (a b : Nat) (h : a = b) : b = a := h.symm\", " ++
    "\"theorem extra : True := trivial\\n" ++ sig ++ " := by omega\", \"" ++ sig ++ " := by omega\"]}'\n")
  discard <| sh "chmod" #["+x", script.toString] r
  let o ← run #["--propose", script.toString, "--apply", path.toString] r
  ok o; hasErr o "helper lemma"
  let t ← IO.FS.readFile path
  check (t == sig ++ " := by omega\n") t
  check (has (← IO.FS.readFile (r / "requests.log")) "\"free\":[\"helper\"]") "no free helper"
  ok (← sh "lake" #["env", "lean", path.toString] r)

def unneededSteps : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Steps2.lean"
  let needed := "theorem needed (a b : Nat) (h : a = b) : b = a := by\n  subst h\n  rfl\n"
  IO.FS.writeFile path ("theorem detour (a b : Nat) (h : a = b) : a + 0 = b := by\n  have h' : b = a := h.symm\n" ++
    "  rw [Nat.add_zero]\n  exact h\n" ++ needed)
  let o ← run #["--compress", "--rules", "unneededStep", "--apply", path.toString] r
  ok o; hasErr o "unneededStep:"
  let t ← IO.FS.readFile path
  -- `a + 0` reduces to `a`, so `exact h` alone closes the goal.
  check (has t "a + 0 = b := by\n  exact h\n" && has t needed) t
  ok (← sh "lake" #["env", "lean", path.toString] r)

/-- Mathlib's `lemma` is a separate command whose macro expands to `theorem`. -/
def lemmaDeclarations : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Lemmas.lean"
  IO.FS.writeFile path ("import Lean\nopen Lean in\n" ++
    "syntax (name := lemma) declModifiers group(\"lemma \" declId ppIndent(declSig) declVal) : command\n" ++
    "open Lean in\n@[macro «lemma»] def expandLemma : Macro := fun stx =>\n" ++
    "  let stx := stx.modifyArg 1 fun stx =>\n" ++
    "    let stx := stx.modifyArg 0 (mkAtomFrom · \"theorem\" (canonical := true))\n" ++
    "    stx.setKind ``Parser.Command.theorem\n" ++
    "  pure <| stx.setKind ``Parser.Command.declaration\n" ++
    "lemma pruned (n : Nat) : n = n := by\n  have unused : True := True.intro\n  rfl\n")
  let o ← run #["--compress", "--rules", "unusedHave", "--apply", path.toString] r
  ok o; hasErr o "unusedHave:"
  let t ← IO.FS.readFile path
  check (has t "lemma pruned (n : Nat) : n = n := by\n  rfl\n") t
  ok (← sh "lake" #["env", "lean", path.toString] r)

def unusedInstances : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Binders.lean"
  IO.FS.writeFile path ("class Fancy (n : Nat) : Prop where ok : True\n" ++
    "class Needed (n : Nat) : Prop where pos : 0 < n\n" ++
    "def Dec (p : Prop) [Decidable p] : Bool := decide p\n" ++
    "theorem loose (n : Nat) [Fancy n] [Needed n] : 0 < n := Needed.pos\n" ++
    -- The statement uses the instance, so another instance would change what it says.
    "theorem depends (p : Prop) [Decidable p] (h : Dec p = true) : Dec p = true := h\n" ++
    "theorem named (n : Nat) [inst : Fancy n] : True := trivial\n" ++
    "theorem positional (n : Nat) [Fancy n] : True := trivial\n" ++
    "example : True := @positional 3 ⟨trivial⟩\n" ++
    "theorem multiline (n : Nat)\n    [Fancy n]\n    [Needed n] : 0 < n := Needed.pos\n")
  let o ← run #["--compress", "--rules", "unusedInstance", "--apply", path.toString] r
  ok o; hasErr o "2 edits"
  let t ← IO.FS.readFile path
  for s in ["theorem loose (n : Nat) [Needed n] : 0 < n", "[Decidable p] (h : Dec p = true)",
      "[inst : Fancy n]", "theorem positional (n : Nat) [Fancy n]", "theorem multiline (n : Nat)\n    [Needed n] :"] do
    check (has t s) s!"missing {s.quote}\n{t}"
  ok (← sh "lake" #["env", "lean", path.toString] r)

def unusedTheorems : IO Unit := withFixture fun r => do
  let dead := r / "Fixture" / "Dead.lean"
  let other := r / "Fixture" / "DeadOther.lean"
  IO.FS.writeFile dead ("namespace Dead\n\n/-- Only `chain` uses this. -/\ntheorem helper : True := trivial\n\n" ++
    "theorem chain : True := helper\n\ntheorem used : True := trivial\n\n" ++
    "@[simp] theorem tagged : True := trivial\n\n" ++
    "set_option linter.unusedVariables false in\ntheorem prefixed (h : True) : True := trivial\n\n" ++
    "theorem _root_.Nat.selfEq (n : Nat) : n = n := rfl\n\n" ++
    "theorem commented : True := trivial\n\ntheorem shared : True := trivial\n\nend Dead\n")
  IO.FS.writeFile other "import Fixture.Dead\n\ntheorem otherDead : True := Dead.shared\n"
  IO.FS.writeFile (r / "Fixture" / "DeadUse.lean") ("import Fixture.DeadOther\n\n" ++
    "-- `commented` is mentioned here\ntheorem top : True := Dead.used\n\n" ++
    "example (n : Nat) : n = n := n.selfEq\n")
  -- An unused theorem that another file's unused theorem mentions stays unless both go.
  let alone ← run #["--unused", "--apply", dead.toString] r
  ok alone; hasErr alone "3 edits"
  let t ← IO.FS.readFile dead
  for n in ["helper", "chain", "prefixed", "set_option"] do check (!has t n) s!"{n} remains\n{t}"
  for n in ["used", "tagged", "selfEq", "commented", "shared"] do check (has t n) s!"{n} was deleted\n{t}"
  check (!has t "\n\n\n") t
  let both ← run #["--unused", "--apply", dead.toString, other.toString] r
  ok both; hasErr both "2 edits"
  check (!has (← IO.FS.readFile dead) "shared" && !has (← IO.FS.readFile other) "otherDead") both.err
  ok (← sh "lake" #["build"] r)
  -- Edits in different files are written together or not at all.
  let kept := (← IO.FS.readFile dead).replace "end Dead" "theorem extra : True := trivial\n\nend Dead"
  IO.FS.writeFile dead kept
  IO.FS.writeFile other "import Fixture.Dead\n\ntheorem another : True := trivial\n\nexample : True := by exact\n"
  let failing ← run #["--unused", "--check", "--apply", dead.toString, other.toString] r
  check (failing.code != 0) failing.err; hasErr failing "wrote none"
  check ((← IO.FS.readFile dead) == kept && has (← IO.FS.readFile other) "another") failing.err

/-- Theorems with the same last name in different namespaces are told apart by resolving each
    mention as Lean would. -/
def unusedNamespaces : IO Unit := withFixture fun r => do
  let names := r / "Fixture" / "Names.lean"
  IO.FS.writeFile names ("namespace A\n\ntheorem foo : True := trivial\n\ntheorem bar : True := trivial\n\nend A\n\n" ++
    "namespace B\n\ntheorem foo : True := trivial\n\ntheorem bar : True := trivial\n\ntheorem baz : True := trivial\n\nend B\n\n" ++
    "structure S where\n  x : Nat\n\ntheorem S.qux (s : S) : s.x = s.x := rfl\n\n" ++
    "theorem S.unusedQux (s : S) : s.x = s.x := rfl\n")
  IO.FS.writeFile (r / "Fixture" / "NamesUse.lean") ("import Fixture.Names\n\ntheorem t1 : True := A.foo\n\n" ++
    "namespace B\n\ntheorem t2 : True := bar\n\nend B\n\nexample (s : S) : s.x = s.x := s.qux\n")
  let o ← run #["--unused", "--apply", names.toString] r
  ok o; hasErr o "4 edits"
  let t ← IO.FS.readFile names
  for kept in ["namespace A\n\ntheorem foo", "theorem bar : True := trivial\n\nend B", "S.qux"] do
    check (has t kept) s!"{kept} was deleted\n{t}"
  for gone in ["theorem bar : True := trivial\n\nend A", "namespace B\n\ntheorem foo", "baz", "unusedQux"] do
    check (!has t gone) s!"{gone} remains\n{t}"
  ok (← sh "lake" #["build"] r)

def matchingTypes : IO Unit := withFixture fun r => do
  let path := r / "Fixture" / "Search.lean"
  let negative := "theorem mismatch (n m : Nat) (a : Token n) (b : Grant m) : Reward := fallback n m a b\n"
  IO.FS.writeFile path ("axiom Token : Nat → Prop\naxiom Both : Nat → Nat → Prop\naxiom Won : Prop\n" ++
    "axiom Finished : Prop\naxiom Reward : Prop\naxiom win (n : Nat) : Token n → Won\n" ++
    "axiom doneWith (a b : Nat) : Both a b → Finished\n" ++
    "theorem original (a b : Nat) (h : Token a) : Won := win a h\n" ++
    "theorem swapped (b a : Nat) (w : Token a) : Won := win a w\n" ++
    "theorem paired (a b c : Nat) (h : Both a b) : Finished := doneWith a b h\n" ++
    "theorem swapPair (c b a : Nat) (h : Both a b) : Finished := doneWith a b h\n" ++
    "axiom Grant : Nat → Prop\naxiom getReward (n : Nat) : Token n → Grant n → Reward\n" ++
    "theorem grant (n : Nat) (h : Token n) (k : Grant n) : Reward := getReward n h k\n" ++
    "theorem joined (m : Nat) (w : Token m ∧ Grant m) : Reward := getReward _ w.1 w.2\n" ++
    "theorem ambiguous (n m : Nat) (ok : Token n) (permit : Grant n) (decoy : Token m) : Reward := getReward _ ok permit\n" ++
    "axiom fallback (n m : Nat) : Token n → Grant m → Reward\n" ++ negative)
  let o ← run #["--dedup-pass", "elaborate", "--check", "--apply", path.toString] r
  ok o; hasErr o "4 edits"; hasErr o "swapped restates (with arguments reordered) original"
  hasErr o "swapPair restates (with arguments reordered) paired"
  hasErr o "joined is a special case of grant"; hasErr o "ambiguous is a special case of grant"
  check (has (← IO.FS.readFile path) negative) "mismatched indices were accepted"
  ok (← sh "lake" #["env", "lean", path.toString] r)

def lintSelection : IO Unit := withFixture fun r => do
  let list ← run #["--list-lints"] r
  ok list; hasOut list "specialCase\tdedup\t"; hasOut list "unusedHave\tcompress\t"
  let path := r / "Fixture" / "Use.lean"
  let args := #["--dedup-pass", "elaborate", "--check", path.toString]
  let exact ← run (args ++ #["--rules", "duplicate"]) r
  ok exact; hasErr exact "duplicate:"; checkNot (has exact.err "specialCase:") exact.err
  let general ← run (args ++ #["-A", "duplicate"]) r
  ok general; hasErr general "specialCase:"; checkNot (has general.err "duplicate:") general.err
  let invalid ← run (args ++ #["--rules", "unusedHave"]) r
  check (invalid.code == 2) invalid.err
  let p := r / "Fixture" / "Named.lean"
  IO.FS.writeFile p ("theorem named : @Eq.{1} Nat 1 1 := by\n" ++
    "  have unused : True := True.intro\n  rfl\n")
  let pruning ← run #["--compress", "--rules", "unusedHave", "--apply", p.toString] r
  ok pruning; hasErr pruning "unusedHave:"
  check ((← IO.FS.readFile p) == "theorem named : @Eq.{1} Nat 1 1 := by\n  rfl\n") pruning.err

def permutedStatements : IO Unit := withFixture fun r => do
  let permutations (items : List String) := items.foldl (init := [[]]) fun ps x =>
    ps.flatMap fun p => (List.range (p.length + 1)).map fun i => p.take i ++ x :: p.drop i
  let facts := (permutations ["(h : E a b)", "(i : E b c)", "(j : E c d)"]).toArray
  let mut text := "axiom E : Nat → Nat → Prop\naxiom Target : Prop\naxiom witness : Target\n"
  for (order, n) in (permutations ["a", "b", "c", "d"]).zipIdx do
    text := text ++ s!"theorem path{n} ({" ".intercalate order} : Nat) " ++
      " ".intercalate facts[n % facts.size]! ++ " : Target := witness\n"
  let star := "theorem star (a b c d : Nat) (h : E a b) (i : E a c) (j : E a d) : Target := witness\n"
  let p := r / "Fixture" / "Permutations.lean"
  IO.FS.writeFile p (text ++ star)
  let o ← run #["--dedup-pass", "elaborate", "--rules", "duplicate", "--check", "--apply", p.toString] r
  ok o; hasErr o "23 edits"
  check (has (← IO.FS.readFile p) star) "a star graph matched a directed path"
  ok (← sh "lake" #["env", "lean", p.toString] r)

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
  ("check rejects a wrong proof", checkRejectsWrongProof), ("checked apply with a build", checkedApplyWithBuild), ("touched source still built", touchedSourceStillBuilt),
  ("language server, syntax pass", lspSyntax), ("language server, elaborated pass", lspElaborated),
  ("cheaper tactics", tactics), ("unneeded seals", unneededSeals), ("tactic cache and dependency skeletons", tacticCache),
  ("parallel tactic replay", parallelReplays), ("arithmetic premise selection", arithmeticPremises),
  ("explicit arithmetic premises", explicitArithmeticPremises),
  ("proof compression", proofCompression),
  ("maximum nonoverlapping savings", overlappingSavings), ("signature compression", signatureCompression),
  ("local relation chains", relationChains), ("prune unused local proofs", pruneHaves),
  ("search for an alternative proof", alternativeProof),
  ("redundant proof steps", redundantSteps), ("simp erasures", simpErasures), ("shorter blocks", shorterBlocks), ("shorter simp", shorterSimp), ("unneeded steps", unneededSteps), ("redundant ascriptions", redundantAscriptions), ("joined lines", joinedLines), ("stripped comments", strippedComments), ("golf rules", golfRules), ("golf obtain projection", golfObtainProjection), ("golf term compile", golfTermCompile), ("golf tactic pairs", golfTacticPairs), ("folded helpers", foldedHelpers), ("contracted pairs", contractedPairs), ("shortened names", shortenedNames), ("proposed rewrites", proposedRewrites), ("proposed groups", proposedGroups), ("lemma declarations", lemmaDeclarations),
  ("unused theorems", unusedTheorems), ("unused theorems by namespace", unusedNamespaces), ("unused instance arguments", unusedInstances),
  ("type matching with dependent and unused arguments", matchingTypes), ("select named lints", lintSelection),
  ("permuted dependent statements", permutedStatements)]

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
