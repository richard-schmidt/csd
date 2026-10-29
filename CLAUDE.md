# csd

Formal models of software and system architecture in Lean 4 and Mathlib. The
toolchain is pinned in `lean-toolchain`, Mathlib in `lakefile.toml`.

## Build

```sh
lake exe cache get
lake build
```

`lake build` builds the default targets: `Showcase`, `Sketches`, `Production`
and `DDD`. CI runs the same build on every push.

## Libraries

- `Showcase/`: finished modules, no `sorry`.
- `Sketches/`: drafts that build; `sorry` is allowed and stated in the README.
- `Production/`: code of the series "Composable production systems", no
  `sorry`.
- `DDD/`: bounded contexts as finitely presented categories; `sorry` is
  allowed.
- `cli/`: Lean programs of `DDD` (`csd-check`, `csd-export`), run with
  `lake env lean --run`; not built by `lake build`.
- `julia/`: the Julia side of `DDD` (Catlab), run in CI after the Lean build.
- `wip/` and `deprecated/` are not built.

Each module of `Showcase/` and `Sketches/` has its own namespace. `Production/`
and `DDD/` share a library namespace (`Production`, `DDD`); each module in
`DDD/Examples/` has its own. Libraries are built by glob, without a root file
importing all modules.

## Writing style

Comments, docstrings, READMEs and commit messages state what the code defines
and proves. No first person, no account of how the work was done, no filler or
emphasis, no emoji. Follow the tone of the existing `README.md`.

## Current work

The `DDD` library on branch `claude/ddd-design`. `DDD/README.md` holds the
plan, the decisions and the status; read it before working on `DDD`, and update
its Status section when a work item is complete.
