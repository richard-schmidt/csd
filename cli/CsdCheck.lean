import DDD.Report

/-!
`csd-check`: checks a certificate or a context map document.

    lake build csd-check
    lake exe csd-check [--json] file.json

The file is a certificate (`"kind": "certificate"`) or a context map document
(`"kind": "map"`). The claims of a context map document are that its list of
value types is sound, that each context is well formed and declares its value
types, and that each arrow is a valid translation (`DDD.MapDoc.certificate`).
The literals of the states of a certificate are read in normal form.

The executable `csd-check` (`lakefile.toml`) is this program compiled to native
code, with the modules it imports. Each claim is checked by its checker
(`DDD.Certificate.checkClaim`). A claim that passes holds, by
`DDD.Certificate.checkClaim_sound`; the evaluation trusts the Lean compiler and
runtime, as `native_decide` does. A failing claim is explained by its problems
(`DDD.Report`).

The output is one line per claim, followed for a failing claim by its problems.
With `--json` it is the report as JSON instead: `DDD.Certificate.report` for a
certificate, `DDD.MapDoc.report` for a context map document. The exit code is 0
when every claim passes, 1 when one fails, and 2 when the file cannot be read.

`lake env lean --run cli/CsdCheck.lean file.json` runs the same program in the
interpreter.
-/

open DDD Lean

/-- The certificate a document stands for, with the document when it is a map. -/
def load (j : Json) : Except String (Certificate × Option MapDoc) := do
  match ← j.getObjValAs? String "kind" with
  | "map" =>
    let M ← MapDoc.ofJson j
    pure (M.certificate, some M)
  | _ => pure (← Certificate.fromJson j, none)

def message (p : Json) : String := (p.getObjValAs? String "message").toOption.getD p.compress

def usage : IO UInt32 := do
  IO.eprintln "usage: csd-check [--json] file.json"
  pure 2

def main (args : List String) : IO UInt32 := do
  let some (json, path) := (match args with
      | ["--json", p] => some (true, p)
      | [p] => some (false, p)
      | _ => none) | usage
  let text ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok t => pure t
    | .error e =>
      IO.eprintln s!"csd-check: {path}: {e}"
      return 2
  match Json.parse text >>= load with
  | .error e =>
    IO.eprintln s!"csd-check: {path}: {e}"
    pure 2
  | .ok (c, map?) =>
    let rs := c.claims.map fun cl => (cl, c.result cl)
    let failed := (rs.filter fun r => !r.2.1).length
    if json then
      IO.println (match map? with
        | some M => M.report
        | none => c.report).pretty
    else
      IO.println s!"csd-check: {path}: {c.claims.length} claims from {c.producer}"
      IO.println "csd-check: checkers evaluated outside the kernel (trusts the Lean compiler)"
      for (cl, ok, ps) in rs do
        IO.println s!"{if ok then "ok    " else "FAILED"} {cl.describe}"
        for p in ps do
          IO.println s!"       {message p}"
      if failed == 0 then
        IO.println s!"csd-check: all {c.claims.length} claims hold"
      else
        IO.println s!"csd-check: {failed} of {c.claims.length} claims failed"
    pure (if failed == 0 then 0 else 1)
