"""
    CsdDDD

The Julia side of the DDD library. Catlab and ACSets compute; Lean checks.

- Schemas are acsets on a schema of schemas (entity types, references,
  attributes, with their names), together with equations, aggregates, value
  objects, keys and subtypes. Gluing two schemas along a kernel is a pushout of
  acsets and the union of the equations, keys and subtypes.
- Finite states are columns per generator, in the order of their schema, as in
  `DDD/Data.lean`. Homomorphism search runs on their acsets.
- Restriction along a translation follows the image path of each generator.
- Conversions between value types (`conv`, `apply_lit`) act on literals in normal
  form as `TypeList.conv?` and `TypeList.applyLit` do in `DDD/ValueCat.lean`:
  built-ins, coercions between a named type and its base, `string`, tables,
  fields of records, `some` and lifts to optional types.
- Everything is read from and written to the exchange format of
  `DDD/Json.lean` (`csd-ddd/1`).
"""
module CsdDDD

using Catlab
using JSON3

export FORMAT, DDDSchema, read_schema, write_schema, Translation, read_translation,
  write_translation, State, write_state, read_state, glue, clashes, qualify, restrict,
  check_state,
  homomorphism_search, Certificate, add_schema!, add_state!, add_claim!, write_certificate,
  read_type, write_type, read_types, read_lit, conv, apply_lit

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

"""
A schema: its acset of generators, and its equations, aggregates, value objects,
keys (entity type, field names) and subtypes (entity type, is-a reference).
"""
struct DDDSchema
  graph::SchemaAcset
  eqns::Vector{Equation}
  aggregates::Vector{Aggregate}
  valueObjects::Vector{String}
  keys::Vector{Tuple{String,Vector{String}}}
  subtypes::Vector{Tuple{String,String}}
end

entities(S::DDDSchema) = collect(S.graph[:entity_name])
entity_index(S::DDDSchema, e) = findfirst(==(e), S.graph[:entity_name])

"References as (source, name, target), in order."
refs(S::DDDSchema) = [(S.graph[r, (:ref_src, :entity_name)], S.graph[r, :ref_name],
  S.graph[r, (:ref_tgt, :entity_name)]) for r in parts(S.graph, :Ref)]

"Attributes as (source, name, value type), in order."
attrs(S::DDDSchema) = [(S.graph[a, (:attr_src, :entity_name)], S.graph[a, :attr_name],
  S.graph[a, :attr_type]) for a in parts(S.graph, :Attr)]

# Value types are kept as strings: "int", ..., "duration", "named:N", or
# "optional:T" for the optional type of T.
vtype_from_json(j) = j isa AbstractString ? String(j) :
  haskey(j, "named") ? "named:" * String(j["named"]) : "optional:" * vtype_from_json(j["optional"])
vtype_to_json(t) = startswith(t, "named:") ? Dict("named" => t[7:end]) :
  startswith(t, "optional:") ? Dict("optional" => vtype_to_json(t[10:end])) : t

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
  ks = [(String(k["entity"]), String.(k["fields"])) for k in getlist(j, "keys")]
  sts = [(String(x["entity"]), String(x["reference"])) for x in getlist(j, "subtypes")]
  DDDSchema(G, eqns, aggs, String.(getlist(j, "valueObjects")), ks, sts)
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
    "valueObjects" => S.valueObjects,
    "keys" => [Dict("entity" => e, "fields" => fs) for (e, fs) in S.keys],
    "subtypes" => [Dict("entity" => e, "reference" => r) for (e, r) in S.subtypes])
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
inclusions of `K`, the equations of both, and the merged aggregates, value
objects, keys and subtypes, as `Schema.glue` in Lean merges them.
"""
function glue(K::DDDSchema, L::DDDSchema, R::DDDSchema)
  P = pushout(inclusion(K, L), inclusion(K, R))
  G = ob(P)
  both(a, b) = vcat(a, [x for x in b if !(x in a)])
  DDDSchema(G, vcat(L.eqns, R.eqns), merge_aggregates(L.aggregates, R.aggregates),
    both(L.valueObjects, R.valueObjects), both(L.keys, R.keys), both(L.subtypes, R.subtypes))
end

"""
    clashes(K, L, R)

The generators that `L` and `R` share outside the kernel `K`, as (entity type,
name). Entity types shared outside `K` are an error.
"""
function clashes(K::DDDSchema, L::DDDSchema, R::DDDSchema)
  ents = [e for e in entities(L) if e in entities(R) && !(e in entities(K))]
  isempty(ents) || error("entity types shared outside the kernel: $ents")
  gens(S) = vcat([(s, n) for (s, n, _) in refs(S)], [(s, n) for (s, n, _) in attrs(S)])
  [g for g in gens(L) if g in gens(R) && !(g in gens(K))]
end

"""
    qualify(S, ctx, names)

`S` with each generator in `names` renamed to `ctx.name`, so that the generator
`createdAt` of `Customer` in the context `Orders` becomes `Customer.Orders.createdAt`
in the exchange format; and the translation from `S` to the result.
"""
function qualify(S::DDDSchema, ctx, names)
  newname(e, n) = (e, n) in names ? "$ctx.$n" : n
  G = copy(S.graph)
  for r in parts(G, :Ref)
    set_subpart!(G, r, :ref_name, newname(G[r, (:ref_src, :entity_name)], G[r, :ref_name]))
  end
  for a in parts(G, :Attr)
    set_subpart!(G, a, :attr_name, newname(G[a, (:attr_src, :entity_name)], G[a, :attr_name]))
  end
  function rename_path(src, path)
    e, out = src, String[]
    for n in path
      push!(out, newname(e, n))
      i = findfirst(x -> x[1] == e && x[2] == n, refs(S))
      e = i === nothing ? "" : refs(S)[i][3]
    end
    out
  end
  eqns = [Equation(q.src, rename_path(q.src, q.lhs), rename_path(q.src, q.rhs)) for q in S.eqns]
  aggs = [Aggregate(A.root, [(m, newname(m, o)) for (m, o) in A.members]) for A in S.aggregates]
  ks = [(e, [newname(e, n) for n in fs]) for (e, fs) in S.keys]
  sts = [(e, newname(e, r)) for (e, r) in S.subtypes]
  T = Translation(Tuple{String,String}[], [(e, n, [newname(e, n)]) for (e, n) in names])
  (DDDSchema(G, eqns, aggs, S.valueObjects, ks, sts), T)
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
column per attribute (values: `Int`, `String`, `Bool`, or `nothing` for the
absent value of an optional type). Literals are kept as written; Lean puts them
in normal form when it reads a certificate.
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

julia_type(t) = t == "int" ? Int : t == "bool" ? Bool :
  startswith(t, "optional:") ? Union{Nothing,julia_type(t[10:end])} : String
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
# Conversions

"""
A value type as the exchange format writes it: a built-in by its name (`"int"`),
`("named", n)`, or `("optional", t)`.
"""
read_type(j) = j isa AbstractString ? String(j) :
  haskey(j, "named") ? ("named", String(j["named"])) : ("optional", read_type(j["optional"]))

write_type(t) = t isa String ? t :
  t[1] == "named" ? Dict("named" => t[2]) : Dict("optional" => write_type(t[2]))

type_text(t) = t isa String ? t : t[1] == "named" ? t[2] : "optional " * type_text(t[2])
is_plain(t) = !(t isa Tuple && t[1] == "optional")

"A table between finite types: its name, source, target and rows."
struct Table
  name::String
  source::Any
  target::Any
  rows::Vector{Tuple{String,String}}
end

"""
The list of value types: the declarations by name (`(:enum, values)`,
`(:over, base)` or `(:record, fields)`) and the tables.
"""
struct TypeList
  decls::Vector{Pair{String,Any}}
  tables::Vector{Table}
end

function read_types(j)
  decls = Pair{String,Any}[]
  tables = Table[]
  for d in j
    name = String(d["name"])
    if haskey(d, "from")
      push!(tables, Table(name, read_type(d["from"]), read_type(d["to"]),
        [(String(r[1]), String(r[2])) for r in d["rows"]]))
    elseif haskey(d, "values")
      push!(decls, name => (:enum, String.(d["values"])))
    elseif haskey(d, "base")
      push!(decls, name => (:over, read_type(d["base"])))
    else
      push!(decls, name => (:record, [String(f["name"]) => read_type(f["type"]) for f in d["fields"]]))
    end
  end
  TypeList(decls, tables)
end

declaration(L::TypeList, n) = lookup(L.decls, n)
base(L::TypeList, n) = (d = declaration(L, n); d !== nothing && d[1] == :over ? d[2] : nothing)

const BUILTIN_CONVERSIONS = Dict(("timestamp", "datetime") => "datetime",
  ("timestamp", "date") => "date", ("timestamp", "time") => "time",
  ("datetime", "date") => "date", ("datetime", "time") => "time", ("int", "decimal") => "decimal")

"The coercion named `n` out of `v`: to the base of a named type, or to a named type over `v`."
function coerce(L::TypeList, v, n)
  if v isa Tuple && v[1] == "named"
    b = base(L, v[2])
    b !== nothing && n == type_text(b) ? b : nothing
  elseif v isa String
    b = base(L, n)
    b !== nothing && b == v ? ("named", n) : nothing
  else
    nothing
  end
end

table(L::TypeList, v, n) = (i = findfirst(t -> t.name == n && t.source == v, L.tables);
  i === nothing ? nothing : L.tables[i])

function field(L::TypeList, v, n)
  v isa Tuple && v[1] == "named" || return nothing
  d = declaration(L, v[2])
  d !== nothing && d[1] == :record ? lookup(d[2], n) : nothing
end

"The target of the conversion named `n` out of the plain type `v`, or `nothing`."
function plain_conv(L::TypeList, v, n)
  n == "some" && return ("optional", v)
  n == "string" && return v == "string" ? nothing : "string"
  w = get(BUILTIN_CONVERSIONS, (v, n), nothing)
  w !== nothing && return w
  w = coerce(L, v, n)
  w !== nothing && return w
  t = table(L, v, n)
  t !== nothing && return t.target
  field(L, v, n)
end

"The target of the conversion named `n` out of `v`: at an optional type, a lift."
function conv(L::TypeList, v, n)
  if !is_plain(v)
    u = v[2]
    is_plain(u) || return nothing
    w = plain_conv(L, u, n)
    w !== nothing && is_plain(w) ? ("optional", w) : nothing
  else
    plain_conv(L, v, n)
  end
end

"""
A literal as JSON3 reads it: `String`, `Int`, `Bool`, `nothing`, or a record as a
`Dict` of its fields.
"""
read_lit(x::AbstractDict) = Dict{String,Any}(String(k) => read_lit(v) for (k, v) in x)
read_lit(x::AbstractString) = String(x)
read_lit(x) = x

"A literal in normal form as text, as `Lit.str`: records with their fields sorted."
lit_text(x::AbstractString) = x
lit_text(x::Bool) = x ? "true" : "false"
lit_text(x::Integer) = string(x)
lit_text(::Nothing) = "null"
lit_text(x::AbstractDict) = "{" * join(["$k: $(lit_text(x[k]))" for k in sort(collect(keys(x)))], ", ") * "}"

"The conversion named `n` out of the plain type `v`, on a literal in normal form."
function plain_conv_lit(L::TypeList, v, n, x)
  n == "some" && return x
  n == "string" && return lit_text(x)
  if haskey(BUILTIN_CONVERSIONS, (v, n))
    v == "int" && return string(x)
    v == "timestamp" && n == "datetime" && return x[1:end-1]
    (n == "date") && return first(x, 10)
    v == "timestamp" && n == "time" && return x[12:end-1]
    v == "datetime" && n == "time" && return x[12:end]
  end
  coerce(L, v, n) !== nothing && return x
  t = table(L, v, n)
  if t !== nothing
    key = x isa Bool ? lit_text(x) : x
    i = findfirst(r -> r[1] == key, t.rows)
    i === nothing && error("the table $n has no row for $(lit_text(x))")
    y = t.rows[i][2]
    return t.target == "bool" ? y == "true" : y
  end
  x isa AbstractDict && haskey(x, n) && return x[n]
  error("there is no conversion $n out of $(type_text(v)) for $(lit_text(x))")
end

"The conversion named `n` out of `v`, on a literal in normal form; a lift keeps `nothing`."
conv_lit(L::TypeList, v, n, x) = !is_plain(v) ? (x === nothing ? nothing :
  plain_conv_lit(L, v[2], n, x)) : plain_conv_lit(L, v, n, x)

"A path of conversions out of `v`, applied to a literal in normal form."
function apply_lit(L::TypeList, v, path, x)
  for n in path
    w = conv(L, v, n)
    w === nothing && error("there is no conversion $n out of $(type_text(v))")
    x = conv_lit(L, v, n, x)
    v = w
  end
  x
end

# ---------------------------------------------------------------------------
# Certificates

mutable struct Certificate
  producer::String
  valueTypes::Vector{Any}
  schemas::Vector{Any}
  states::Vector{Any}
  claims::Vector{Any}
end

Certificate(producer) = Certificate(producer, [], [], [], [])

add_schema!(c::Certificate, name, S::DDDSchema) =
  push!(c.schemas, Dict("name" => name, "schema" => write_schema(S)))

add_state!(c::Certificate, name, schema, X::State) =
  push!(c.states, Dict("name" => name, "schema" => schema, "state" => write_state(X)))

add_claim!(c::Certificate, kind; kw...) =
  push!(c.claims, merge(Dict{String,Any}("claim" => kind), Dict(String(k) => v for (k, v) in kw)))

function write_certificate(path, c::Certificate)
  doc = Dict("format" => FORMAT, "kind" => "certificate", "producer" => c.producer,
    "valueTypes" => c.valueTypes, "schemas" => c.schemas, "states" => c.states,
    "claims" => c.claims)
  open(io -> JSON3.pretty(io, doc), path, "w")
end

end # module
