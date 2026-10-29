import DDD.Certificate

/-!
`csd-check`: checks a certificate.

    lake env lean --run cli/CsdCheck.lean certificate.json

Each claim is checked by its checker (`DDD.Certificate.checkClaim`), evaluated by
the Lean interpreter. A claim that passes holds, by
`DDD.Certificate.checkClaim_sound`; the evaluation trusts the Lean compiler and
runtime, as `native_decide` does. The exit code is 0 when every claim passes,
1 when one fails, and 2 when the file cannot be read.
-/

open DDD Lean

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lake env lean --run cli/CsdCheck.lean certificate.json"
      pure 2
  let text ← IO.FS.readFile path
  match Json.parse text >>= Certificate.fromJson with
  | .error e =>
    IO.eprintln s!"csd-check: {path}: {e}"
    pure 2
  | .ok c =>
    IO.println s!"csd-check: {path}: {c.claims.length} claims from {c.producer}"
    IO.println "csd-check: checkers evaluated by the Lean interpreter (trusts the compiler)"
    let mut failed := 0
    for cl in c.claims do
      let ok := c.checkClaim cl
      IO.println s!"{if ok then "ok    " else "FAILED"} {cl.describe}"
      if !ok then
        failed := failed + 1
        if let .gluing k l r _ _ := cl then
          if let (some K, some L, some R) := (c.schema? k, c.schema? l, c.schema? r) then
            let clashes := Schema.gluingClashes K L R
            unless clashes.isEmpty do
              IO.println s!"       names shared outside the kernel: {clashes}"
    if failed == 0 then
      IO.println s!"csd-check: all {c.claims.length} claims hold"
      pure 0
    else
      IO.println s!"csd-check: {failed} of {c.claims.length} claims failed"
      pure 1
