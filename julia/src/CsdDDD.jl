"""
    CsdDDD

The Julia side of the DDD library. Catlab and ACSets compute; Lean checks.

- Schemas are acsets on a schema of schemas (entity types, references,
  attributes, with their names), together with equations, aggregates and value
  objects. Gluing two schemas along a kernel is a pushout of acsets and the
  union of the equations.
- Finite states are columns per generator, in the order of their schema, as in
  `DDD/Data.lean`. Homomorphism search runs on their acsets.
- Restriction along a translation follows the image path of each generator.
- Everything is read from and written to the exchange format of
  `DDD/Json.lean` (`csd-ddd/1`).
"""
module CsdDDD

using Catlab
using JSON3

export FORMAT, DDDSchema, read_schema, write_schema, Translation, read_translation,
  write_translation, State, write_state, read_state, glue, restrict, check_state,
  homomorphism_search, Certificate, add_schema!, add_state!, add_claim!, write_certificate

const FORMAT = "csd-ddd/1"

# ---------------------------------------------------------------------------
# Schemas

@present SchSchema(FreeSchema) begin
  (Entity, Ref, Attr)::Ob
  ref_src::Hom(Ref, Entity)
  ref_tgt::Hom(Ref, Entity)
  attr_src::Hom(Attr, Entity)
  Name::AttrType
  entity_name::Attr(Entity, Name)
  ref_name::Attr(Ref, Name)
  attr_name::Attr(Attr, Name)
  attr_type::Attr(Attr, Name)
end

@acset_type SchemaGraph(SchSchema, index=[:ref_src, :attr_src])

"The entity types and generators of a schema, as an acset with names as attributes."
const SchemaAcset = SchemaGraph{String}

struct Equation
  src::String
  lhs::Vector{String}
  rhs::Vector{String}
end

struct Aggregate
  root::String
  members::Vector{Tuple{String,String}}   # (entity, owner reference)
end

"A schema: its acset of generators, and its equations, aggregates and value objects."
struct DDDSchema
  graph::SchemaAcset
  eqns::Vector{Equation}
  aggregates::Vector{Aggregate}
  valueObjects::Vector{String}
end

entities(S::DDDSchema) = collect(S.graph[:entity_name])
entity_index(S::DDDSchema, e) = findfirst(==(e), S.graph[:entity_name])

"References as (source, name, target), in order."
refs(S::DDDSchema) = [(S.graph[r, (:ref_src, :entity_name)], S.graph[r, :ref_name],
  S.graph[r, (:ref_tgt, :entity_name)]) for r in parts(S.graph, :Ref)]

"Attributes as (source, name, value type), in order."
attrs(S::DDDSchema) = [(S.graph[a, (:attr_src, :entity_name)], S.graph[a, :attr_name],
  S.graph[a, :attr_type]) for a in parts(S.graph, :Attr)]

# Value types are kept as strings: "int", ..., "bool", or "named:N".
vtype_from_json(j) = j isa AbstractString ? String(j) : "named:" * String(j["named"])
vtype_to_json(t) = startswith(t, "named:") ? Dict("named" => t[7:end]) : t

function split_gen(s)
  i = findfirst('.', s)
  i === nothing && error("generator name without an entity type: $s")
  (s[1:i-1], s[i+1:end])
end

gen_name(e, n) = "$e.$n"

getlist(j, key) = haskey(j, key) ? j[key] : []

function read_schema(j)
  G = SchemaAcset()
  for e in j["entities"]
    add_part!(G, :Entity, entity_name=String(e))
  end
  idx(e) = something(findfirst(==(e), G[:entity_name]), 0)
  for r in getlist(j, "references")
    (e, n) = split_gen(r["name"])
    add_part!(G, :Ref, ref_src=idx(e), ref_tgt=idx(String(r["target"])), ref_name=n)
  end
  for a in getlist(j, "attributes")
    (e, n) = split_gen(a["name"])
    add_part!(G, :Attr, attr_src=idx(e), attr_name=n, attr_type=vtype_from_json(a["type"]))
  end
  eqns = [Equation(String(q["source"]), String.(q["lhs"]), String.(q["rhs"]))
    for q in getlist(j, "equations")]
  aggs = [Aggregate(String(A["root"]),
      [(String(m["entity"]), String(m["owner"])) for m in getlist(A, "members")])
    for A in getlist(j, "aggregates")]
  DDDSchema(G, eqns, aggs, String.(getlist(j, "valueObjects")))
end

function write_schema(S::DDDSchema)
  Dict(
    "entities" => entities(S),
    "references" => [Dict("name" => gen_name(s, n), "target" => t) for (s, n, t) in refs(S)],
    "attributes" => [Dict("name" => gen_name(s, n), "type" => vtype_to_json(t))
      for (s, n, t) in attrs(S)],
    "equations" => [Dict("source" => q.src, "lhs" => q.lhs, "rhs" => q.rhs) for q in S.eqns],
    "aggregates" => [Dict("root" => A.root,
      "members" => [Dict("entity" => e, "owner" => o) for (e, o) in A.members])
      for A in S.aggregates],
    "valueObjects" => S.valueObjects)
end

# ---------------------------------------------------------------------------
# Gluing

"The inclusion of `K` in `B` by names, as a morphism of acsets."
function inclusion(K::DDDSchema, B::DDDSchema)
  ent = [something(entity_index(B, e), 0) for e in entities(K)]
  any(==(0), ent) && error("the kernel entity types are not all in the schema")
  bref = refs(B)
  rf = [something(findfirst(x -> x[1] == s && x[2] == n, bref), 0) for (s, n, _) in refs(K)]
  battr = attrs(B)
  af = [something(findfirst(x -> x[1] == s && x[2] == n, battr), 0) for (s, n, _) in attrs(K)]
  (any(==(0), rf) || any(==(0), af)) && error("the kernel generators are not all in the schema")
  f = ACSetTransformation(K.graph, B.graph, Entity=ent, Ref=rf, Attr=af)
  is_natural(f) || error("the kernel is not included with the same names")
  f
end

"The aggregates of a glued schema, as `Schema.glue` in Lean merges them."
function merge_aggregates(A1, A2)
  roots1 = [A.root for A in A1]
  merged = [Aggregate(A.root, vcat(A.members, [m for A′ in A2 if A′.root == A.root
    for m in A′.members if !(m in A.members)])) for A in A1]
  vcat(merged, [A for A in A2 if !(A.root in roots1)])
end

"""
    glue(K, L, R)

`L` and `R` glued along the kernel `K`: the pushout of their acsets along the
inclusions of `K`, the equations of both, and the merged aggregates and value
objects.
"""
function glue(K::DDDSchema, L::DDDSchema, R::DDDSchema)
  P = pushout(inclusion(K, L), inclusion(K, R))
  G = ob(P)
  vos = vcat(L.valueObjects, [v for v in R.valueObjects if !(v in L.valueObjects)])
  DDDSchema(G, vcat(L.eqns, R.eqns), merge_aggregates(L.aggregates, R.aggregates), vos)
end

# ---------------------------------------------------------------------------
# Translations

struct Translation
  entities::Vector{Tuple{String,String}}
  gens::Vector{Tuple{String,String,Vector{String}}}   # (source, name, path)
end

Translation() = Translation(Tuple{String,String}[], Tuple{String,String,Vector{String}}[])

read_translation(j) = Translation(
  [(String(p["source"]), String(p["target"])) for p in getlist(j, "entities")],
  [(split_gen(g["name"])..., String.(g["path"])) for g in getlist(j, "generators")])

write_translation(T::Translation) = Dict(
  "entities" => [Dict("source" => s, "target" => t) for (s, t) in T.entities],
  "generators" => [Dict("name" => gen_name(s, n), "path" => p) for (s, n, p) in T.gens])

ent(T::Translation, e) = (i = findfirst(x -> x[1] == e, T.entities); i === nothing ? e : T.entities[i][2])

function gen(T::Translation, e, n)
  i = findfirst(x -> x[1] == e && x[2] == n, T.gens)
  i === nothing ? [n] : T.gens[i][3]
end

# ---------------------------------------------------------------------------
# Finite states

"""
A finite state of a schema, as in `DDD/Data.lean`: a count per entity type, a
column per reference (targets, numbered from 1 here and from 0 in JSON), and a
column per attribute (values: `Int`, `String` or `Bool`).
"""
struct State
  sizes::Vector{Pair{String,Int}}
  refs::Vector{Pair{Tuple{String,String},Vector{Int}}}
  attrs::Vector{Pair{Tuple{String,String},Vector{Any}}}
end

Base.:(==)(X::State, Y::State) = X.sizes == Y.sizes && X.refs == Y.refs && X.attrs == Y.attrs

lookup(v, k) = (i = findfirst(p -> p.first == k, v); i === nothing ? nothing : v[i].second)
size_of(X::State, e) = something(lookup(X.sizes, e), 0)

write_state(X::State) = Dict(
  "entities" => [Dict("type" => e, "count" => n) for (e, n) in X.sizes],
  "references" => [Dict("name" => gen_name(k...), "column" => c .- 1) for (k, c) in X.refs],
  "attributes" => [Dict("name" => gen_name(k...), "column" => c) for (k, c) in X.attrs])

read_state(j) = State(
  [String(p["type"]) => Int(p["count"]) for p in getlist(j, "entities")],
  [split_gen(c["name"]) => Int.(c["column"]) .+ 1 for c in getlist(j, "references")],
  [split_gen(c["name"]) => Any[x isa AbstractString ? String(x) : x for x in c["column"]]
    for c in getlist(j, "attributes")])

"One step from entity `i` of type `e` along the generator named `n` of `S`."
function step(S::DDDSchema, X::State, (e, i)::Tuple{String,Int}, n)
  r = findfirst(x -> x[1] == e && x[2] == n, refs(S))
  if r !== nothing
    return (refs(S)[r][3], lookup(X.refs, (e, n))[i])
  end
  a = findfirst(x -> x[1] == e && x[2] == n, attrs(S))
  a === nothing && error("no generator $e.$n")
  lookup(X.attrs, (e, n))[i]
end

"Following a list of generator names from entity `i` of type `e`."
function eval_path(S::DDDSchema, X::State, x, names)
  for n in names
    x isa Tuple || error("a path continues after an attribute")
    x = step(S, X, x, n)
  end
  x
end

"""
    restrict(T, S, S′, X)

`Δ_T X` for a state `X` of `S′` and a translation `T` from `S` to `S′`, as
`FinState.restrict` computes it: the entities of `T e` for each entity type `e`
of `S`, and the column of each generator along its image path.
"""
function restrict(T::Translation, S::DDDSchema, S′::DDDSchema, X::State)
  sizes = [e => size_of(X, ent(T, e)) for e in entities(S)]
  rcols = [(s, n) => [eval_path(S′, X, (ent(T, s), i), gen(T, s, n))[2]
      for i in 1:size_of(X, ent(T, s))] for (s, n, _) in refs(S)]
  acols = [(s, n) => Any[eval_path(S′, X, (ent(T, s), i), gen(T, s, n))
      for i in 1:size_of(X, ent(T, s))] for (s, n, _) in attrs(S)]
  State(sizes, rcols, acols)
end

"The equations of `S` at every entity of `X`."
function check_state(S::DDDSchema, X::State)
  all(q -> all(i -> eval_path(S, X, (q.src, i), q.lhs) == eval_path(S, X, (q.src, i), q.rhs),
    1:size_of(X, q.src)), S.eqns)
end

# ---------------------------------------------------------------------------
# States as acsets, for homomorphism search

julia_type(t) = t == "int" ? Int : t == "bool" ? Bool : String
type_symbol(t) = Symbol(replace(t, ":" => "_"))

"The presentation of `S` as a Catlab schema."
function presentation(S::DDDSchema)
  pres = Presentation(FreeSchema)
  obs = Dict(e => Ob(FreeSchema, Symbol(e)) for e in entities(S))
  add_generators!(pres, [obs[e] for e in entities(S)])
  types = Dict{String,Any}()
  for (_, _, t) in attrs(S)
    haskey(types, t) && continue
    types[t] = AttrType(FreeSchema.AttrType, type_symbol(t))
    add_generator!(pres, types[t])
  end
  for (s, n, t) in refs(S)
    add_generator!(pres, Hom(Symbol(gen_name(s, n)), obs[s], obs[t]))
  end
  for (s, n, t) in attrs(S)
    add_generator!(pres, Attr(Symbol(gen_name(s, n)), obs[s], types[t]))
  end
  pres, Dict(type_symbol(t) => julia_type(t) for t in keys(types))
end

function to_acset(S::DDDSchema, X::State)
  pres, types = presentation(S)
  A = DynamicACSet("State", Catlab.Schema(pres); type_assignment=types)
  for e in entities(S)
    add_parts!(A, Symbol(e), size_of(X, e))
  end
  for (s, n, _) in refs(S)
    set_subpart!(A, :, Symbol(gen_name(s, n)), lookup(X.refs, (s, n)))
  end
  for (s, n, t) in attrs(S)
    set_subpart!(A, :, Symbol(gen_name(s, n)), convert(Vector{julia_type(t)},
      lookup(X.attrs, (s, n))))
  end
  A
end

"""
    homomorphism_search(S, X, Y)

A homomorphism of states from `X` to `Y`, found by Catlab, as a component per
entity type; `nothing` if there is none.
"""
function homomorphism_search(S::DDDSchema, X::State, Y::State)
  h = homomorphism(to_acset(S, X), to_acset(S, Y))
  h === nothing && return nothing
  [e => collect(h[Symbol(e)]) for e in entities(S)]
end

# ---------------------------------------------------------------------------
# Certificates

mutable struct Certificate
  producer::String
  schemas::Vector{Any}
  states::Vector{Any}
  claims::Vector{Any}
end

Certificate(producer) = Certificate(producer, [], [], [])

add_schema!(c::Certificate, name, S::DDDSchema) =
  push!(c.schemas, Dict("name" => name, "schema" => write_schema(S)))

add_state!(c::Certificate, name, schema, X::State) =
  push!(c.states, Dict("name" => name, "schema" => schema, "state" => write_state(X)))

add_claim!(c::Certificate, kind; kw...) =
  push!(c.claims, merge(Dict{String,Any}("claim" => kind), Dict(String(k) => v for (k, v) in kw)))

function write_certificate(path, c::Certificate)
  doc = Dict("format" => FORMAT, "kind" => "certificate", "producer" => c.producer,
    "schemas" => c.schemas, "states" => c.states, "claims" => c.claims)
  open(io -> JSON3.pretty(io, doc), path, "w")
end

end # module
