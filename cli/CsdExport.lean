import DDD.Examples.Exchange

/-!
`csd-export`: writes the example workspace for the Julia side.

    lake env lean --run cli/CsdExport.lean [path]

The default path is `julia/data/workspace.json`.
-/

def main (args : List String) : IO UInt32 := do
  let path := args.headD "julia/data/workspace.json"
  IO.FS.writeFile path (DDD.Examples.Exchange.workspace.pretty ++ "\n")
  IO.println s!"csd-export: wrote {path}"
  pure 0
