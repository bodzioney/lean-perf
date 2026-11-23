import Lean

open Lean System

namespace LeanPerf.Build

def log (msg : String) : IO Unit := do (← IO.getStderr).putStrLn s!"leanperf-dedup: {msg}"

def readJson [FromJson α] (path : FilePath) : IO α := do
  IO.ofExcept <| Json.parse (← IO.FS.readFile path) >>= fromJson?

structure Artifact where
  mod : Name
  dir : FilePath
  deriving Inhabited, ToJson, FromJson

structure Job extends Artifact where
  source : FilePath
  sourceHash : UInt64
  headerKey : UInt64
  deps : Array Artifact
  options : Array String
  requested : Bool
  deriving Inhabited, ToJson, FromJson

structure Signature where
  name : Name
  key : UInt64
  range : Lsp.Range
  deriving ToJson, FromJson, Inhabited

structure Manifest where
  decls : Array Signature
  deps : Array Artifact
  parts : ImportArtifacts
  deriving Inhabited, ToJson, FromJson

def artifactMap (roots : Array Artifact) : IO (NameMap ImportArtifacts) := do
  let mut arts := {}
  let mut todo := roots
  while let some ref := todo.back? do
    todo := todo.pop
    if arts.contains ref.mod then continue
    let info : Manifest ← readJson (ref.dir / "info.json")
    arts := arts.insert ref.mod info.parts
    todo := todo ++ info.deps
  return arts

def moduleOf (root path : FilePath) : Name :=
  let rel := (path.toString.dropPrefix? (root.toString ++ "/")).map (·.toString) |>.getD path.toString
  ((rel.dropSuffix ".lean").toString.splitOn "/").foldl Name.mkStr .anonymous

structure Source where
  path : FilePath
  imports : Array Name
  digest : UInt64
  headerKey : UInt64
  deriving Inhabited

structure Plan where
  sources : Std.HashMap Name Source
  jobs : Std.HashMap Name Job
  order : Array Name


private def stamp (p : FilePath) : IO UInt64 := do
  let s ← p.metadata
  return hash (p.toString, s.byteSize, s.modified.sec, s.modified.nsec)

/-- Copy the direct import names out of the mapped header before releasing its region. -/
private def objectImports (path : FilePath) : IO (Array Name) := do
  let (data, region) ← readModuleData path
  try
    IO.ofExcept <| Json.parse (toJson (data.imports.map (·.module))).compress >>= fromJson?
  finally unsafe region.free

/-- Include transitive external artifacts, even when only an indirect dependency was rebuilt. -/
private partial def objectKey (sp : Lean.SearchPath) (syslib : FilePath)
    (memo : IO.Ref (Std.HashMap Name UInt64)) (m : Name) : IO UInt64 := do
  if let some key := (← memo.get)[m]? then return key
  let some p ← sp.findModuleWithExt "olean" m | throw <| IO.userError s!"missing import {m}"
  let mut key ← stamp p
  -- The installed core library is identified by the pinned compiler and sysroot.
  if !p.toString.startsWith (syslib.toString ++ "/") then
    for part in #[p.addExtension "server", p.addExtension "private", p.withExtension "ir",
        p.withExtension "ir.sig"] do
      if ← part.pathExists then key := mixHash key (← stamp part)
    for dep in ← objectImports p do
      key := mixHash key (← objectKey sp syslib memo dep)
  memo.modify (·.insert m key)
  return key

def plan (root cache : FilePath) (paths : Array FilePath) (options : Array String) : IO Plan := do
  let requested := paths.foldl (init := ({} : Std.HashMap Name FilePath)) fun acc p =>
    acc.insert (moduleOf root p) p
  let mut sources : Std.HashMap Name Source := {}
  let mut order := #[]
  let mut finished : Std.HashSet Name := {}
  let mut external : Std.HashSet Name := {}
  let mut stack := ((requested.keys.toArray.qsort Name.quickLt).map (·, false)).reverse
  while let some (m, done_) := stack.back? do
    stack := stack.pop
    if finished.contains m || external.contains m then continue
    if done_ then
      order := order.push m
      finished := finished.insert m
      continue
    if sources.contains m then throw <| IO.userError s!"cyclic project import at {m}"
    let p := requested[m]?.getD (modToFilePath root m "lean")
    unless ← p.pathExists do
      external := external.insert m
      continue
    let input ← IO.FS.readFile p
    let (header, _, msgs) ← Parser.parseHeader (Parser.mkInputContext input p.toString)
    let hdr : Elab.HeaderSyntax := header
    let imps := hdr.imports
    if msgs.hasErrors then throw <| IO.userError s!"cannot parse imports of {p}"
    let imports := imps.map (·.module)
    sources := sources.insert m { path := p, imports, digest := hash input, headerKey := hash (hdr.isModule, imps) }
    stack := stack.push (m, true) ++ (imports.reverse.map (·, false))
  let sp ← searchPathRef.get
  let syslib ← getLibDir (← findSysroot)
  let mut seed := hash (root.toString, options, Lean.githash, sp.map (·.toString),
    (← IO.getEnv "LEANPERF_FULL").isSome, ← stamp (← IO.appPath))
  for file in ["lake-manifest.json", "lakefile.toml", "lakefile.lean", "lean-toolchain"] do
    let p := (← IO.currentDir) / file
    if ← p.pathExists then seed := mixHash seed (hash (← IO.FS.readFile p))
  let memo ← IO.mkRef {}
  let mut jobs : Std.HashMap Name Job := {}
  let mut keys : Std.HashMap Name UInt64 := {}
  for m in order do
    let src := sources[m]!
    let deps := src.imports.filterMap fun i => jobs[i]?.map (·.toArtifact)
    let built ← sp.findModuleWithExt "olean" m
    if !requested.contains m && deps.isEmpty then
      if let some p := built then
        if (← p.metadata).modified >= (← src.path.metadata).modified then
          keys := keys.insert m (← objectKey sp syslib memo m)
          continue
    let mut key := mixHash seed (hash (m, src.digest))
    for i in src.imports do
      let depKey ← keys[i]?.getDM (objectKey sp syslib memo i)
      key := mixHash key depKey
    keys := keys.insert m key
    jobs := jobs.insert m {
      mod := m, dir := cache / "objects" / toString key
      source := src.path, sourceHash := src.digest, headerKey := src.headerKey, deps, options, requested := requested.contains m }
  log s!"{sources.size} project modules: importing {order.size - jobs.size} built, elaborating {jobs.size} skeletons"
  return { sources, jobs, order := order.filter jobs.contains }

private abbrev Child := IO.Process.Child { stdin := .piped, stdout := .piped }

/-- A worker keeps one set of imports in memory. Retiring it releases all mmap regions
    and Lean initializer state when the import context changes. -/
abbrev Slot := IO.Ref (Option (UInt64 × Child))

def stop (slot : Slot) : IO Unit := do
  if let some (_, child) ← slot.swap none then
    try
      child.stdin.putStrLn ""
      child.stdin.flush
    catch _ => pure ()
    let _ ← child.wait

def submit (slot : Slot) (key : UInt64) (dir : FilePath) (query : Bool) : IO Unit := do
  let cached ← slot.get
  let child ← match cached with
    | some (k, child) => if k == key then pure child else stop slot *> spawn
    | none => spawn
  slot.set (some (key, child))
  child.stdin.putStrLn (Json.mkObj [("dir", toJson dir), ("query", toJson query)]).compress
  child.stdin.flush
  let line ← child.stdout.getLine
  if line.isEmpty then
    stop slot
    throw <| IO.userError s!"Lean worker exited without a result for {dir}"
  let reply ← IO.ofExcept (Json.parse line)
  if let .ok msg := reply.getObjValAs? String "error" then throw <| IO.userError msg
where
  spawn : IO Child := do
    IO.Process.spawn { cmd := (← IO.appPath).toString, args := #["--worker-loop"],
                       stdin := .piped, stdout := .piped }

private def publish (tmp dest : FilePath) : IO Unit := do
  try IO.FS.rename tmp dest catch e =>
    unless ← (dest / "info.json").pathExists do throw e

/-- A directory rename publishes the manifest and all .olean parts together. Independent
    invocations may race to publish the same immutable object. -/
private def buildOne (slot : Slot) (j : Job) : IO Unit := do
  let tmp := FilePath.mk s!"{j.dir}.tmp-{← IO.Process.getPID}-{← IO.rand 0 0xffffffff}"
  IO.FS.createDir tmp
  try
    IO.FS.writeFile (tmp / "job.json") (toJson j).compress
    submit slot j.headerKey tmp false
    IO.FS.removeFile (tmp / "job.json")
    publish tmp j.dir
  finally
    if ← tmp.pathExists then IO.FS.removeDirAll tmp

def build (p : Plan) (workers : Nat) : IO Unit := do
  let mut counts : Std.HashMap Name Nat := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut ready := #[]
  let mut hits := 0
  let mut waitingHits : Std.HashSet Name := {}
  for m in p.order do
    let j := p.jobs[m]!
    let deps := j.deps.filter (fun d => counts.contains d.mod)
    if ← (j.dir / "info.json").pathExists then
      hits := hits + 1
      if deps.isEmpty then continue
      -- A cache entry can survive eviction of one of its imports.
      waitingHits := waitingHits.insert m
    else
      IO.FS.createDirAll j.dir.parent.get!
    counts := counts.insert m deps.size
    if deps.isEmpty then ready := ready.push m
    for d in deps do users := users.alter d.mod (fun a => some ((a.getD #[]).push m))
  let start ← IO.monoMsNow
  let mut idle : List Slot ← (List.range (min workers counts.size)).mapM fun _ => IO.mkRef none
  let slots := idle
  let mut running : List (Task (Name × Slot × Except IO.Error Unit)) := []
  let mut failure := none
  repeat
    while !idle.isEmpty && failure.isNone do
      let some m := ready.back? | break
      ready := ready.pop
      let job := p.jobs[m]!
      let slot :: rest := idle | break
      idle := rest
      let work := if waitingHits.contains m then pure () else buildOne slot job
      running := (← BaseIO.asTask (do return (m, slot, ← work.toBaseIO)) .dedicated) :: running
    if h : running.length > 0 then
      let ((m, slot, result), rest) ← IO.waitAny' running h
      running := rest
      idle := slot :: idle
      match result with
      | .error e => failure := some e
      | .ok () =>
        for user in users[m]?.getD #[] do
          let n := counts[user]! - 1
          counts := counts.insert user n
          if n == 0 then ready := ready.push user
    else break
  for slot in slots do stop slot
  if let some e := failure then throw e
  log s!"skeleton cache: {hits} reused, {p.order.size - hits} built, {workers} workers, {(← IO.monoMsNow) - start} ms"

end LeanPerf.Build
