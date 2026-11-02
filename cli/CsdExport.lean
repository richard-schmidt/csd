import DDD.Examples.Exchange
import DDD.Examples.Problems

/-!
`csd-export`: writes the example workspace for the Julia side, and the context
map document of `DDD.Examples.Problems.brokenMap` for the test of
`csd-check --json`.

    lake env lean --run cli/CsdExport.lean [workspace] [broken-map]

The default paths are `julia/data/workspace.json` and `cli/test/broken-map.json`.
-/

def main (args : List String) : IO UInt32 := do
  let workspace := args.headD "julia/data/workspace.json"
  let broken := (args.drop 1).headD "cli/test/broken-map.json"
  IO.FS.writeFile workspace (DDD.Examples.Exchange.workspace.pretty ++ "\n")
  IO.println s!"csd-export: wrote {workspace}"
  IO.FS.writeFile broken (DDD.Examples.Problems.brokenMap.toJson.pretty ++ "\n")
  IO.println s!"csd-export: wrote {broken}"
  pure 0
