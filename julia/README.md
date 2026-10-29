# Julia side of the DDD library

Catlab computes; Lean checks. `src/CsdDDD.jl` reads and writes the exchange
format of `DDD/Json.lean` (`csd-ddd/1`):

- schemas as acsets on a schema of schemas, with equations, aggregates and
  value objects; gluing along a kernel is a pushout of acsets
  (`CsdDDD.glue`) and the union of the equations;
- finite states as columns per generator, as in `DDD/Data.lean`; restriction
  along a translation follows the image path of each generator
  (`CsdDDD.restrict`); homomorphisms are found by Catlab's search on the acsets
  of the states (`CsdDDD.homomorphism_search`);
- certificates of named schemas, named states and claims.

`run.jl` reads `data/workspace.json`, the example map written by
`cli/CsdExport.lean`, and writes `out/certificate.json`: well-formedness of the
contexts, validity of the translations, the gluing of Orders and Shipping along
the Customers kernel and of the failing scenario, sample states of Orders,
Shipping, the glued schema, Payments and the kernel, the restrictions that relate
them, and a homomorphism of Shipping states. `cli/CsdCheck.lean` checks it.

```sh
lake env lean --run cli/CsdExport.lean julia/data/workspace.json
julia --project=julia -e 'using Pkg; Pkg.instantiate()'
julia --project=julia julia/run.jl
julia --project=julia julia/test/runtests.jl
lake env lean --run cli/CsdCheck.lean julia/out/certificate.json
```

Catlab is pinned to 0.16.20 (`Project.toml`, `Manifest.toml`), on Julia 1.10.
