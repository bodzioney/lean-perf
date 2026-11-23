import LeanPerf.Dedup
import LeanPerf.Cli

/-- One executable: the command line and language server, and the skeleton builder and elaborated
    passes that the command line runs under `lake env` in a target project. -/
unsafe def main (args : List String) : IO UInt32 :=
  match args with
  | "--project" :: _ | "--configured" :: _ | ["--worker-loop"] => LeanPerf.Dedup.run args
  | _ => LeanPerf.Cli.run args
