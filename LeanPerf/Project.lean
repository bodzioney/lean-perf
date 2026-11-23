import Lake.Toml.Load

open Lean System

namespace LeanPerf.Project

private partial def leanOptions (table : Lake.Toml.Table) (parent := Name.anonymous) :
    Array String := Id.run do
  let mut args := #[]
  for (key, value) in table.items do
    let name := parent ++ key
    match value with
    | .table _ t => args := args ++ leanOptions t name
    | .string _ s => args := args.push s!"-D{name}={s}"
    | v => args := args.push s!"-D{name}={v}"
  return args

def settings : IO (FilePath × Array String) := do settingsAt (← IO.currentDir)

where settingsAt (root : FilePath) : IO (FilePath × Array String) := do
  let config := root / "lakefile.toml"
  unless ← config.pathExists do return (root, #[])
  let ctx := Parser.mkInputContext (← IO.FS.readFile config) config.toString
  match ← (Lake.Toml.loadToml ctx).toBaseIO with
  | .error msgs => throw <| IO.userError (← msgs.toList.head!.toString)
  | .ok table =>
    let src := match table.find? `srcDir with | some (.string _ s) => root / s | _ => root
    let opts := match table.find? `leanOptions with | some (.table _ t) => leanOptions t | _ => #[]
    return (src, opts)

/-- Expand input directories once inside the process, including for projects larger than ARG_MAX. -/
def files (paths : Array FilePath) : IO (Array FilePath) := do
  let mut todo := paths
  let mut seen : Std.HashSet FilePath := {}
  let mut out := #[]
  while let some p := todo.back? do
    todo := todo.pop
    let stat ← p.symlinkMetadata
    if stat.type == .symlink then throw <| IO.userError s!"symlink input: {p}"
    let p ← IO.FS.realPath p
    if seen.contains p then continue
    seen := seen.insert p
    if stat.type == .dir then
      for e in ← p.readDir do
        if e.fileName.startsWith "." then continue
        let typ := (← e.path.symlinkMetadata).type
        if typ == .dir || (typ == .file && e.path.extension == some "lean") then
          todo := todo.push e.path
    else if stat.type == .file && p.extension == some "lean" then out := out.push p
    else throw <| IO.userError s!"expected a Lean file or directory: {p}"
  return out.qsort (·.toString < ·.toString)

def launch (args : List String) : IO UInt32 := do
  let pin : FilePath := "lean-toolchain"
  if ← pin.pathExists then
    let target := (← IO.FS.readFile pin).trimAscii
    unless target == s!"leanprover/lean4:v{Lean.versionString}".toSlice do
      throw <| IO.userError s!"target toolchain {target} differs from LeanPerf's Lean {Lean.versionString}"
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["--no-build", "env", (← IO.appPath).toString, "--configured"] ++ args.toArray }
  child.wait

end LeanPerf.Project
