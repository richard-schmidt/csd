# Reproduces the phase 3 results on the example map and writes a certificate for
# Lean to check.
#
#     julia --project=julia julia/run.jl [workspace.json] [certificate.json]
#
# Input: the workspace written by cli/CsdExport.lean. Output: a certificate that
# cli/CsdCheck.lean checks.

include(joinpath(@__DIR__, "src", "CsdDDD.jl"))
using .CsdDDD
using JSON3

const IN = get(ARGS, 1, joinpath(@__DIR__, "data", "workspace.json"))
const OUT = get(ARGS, 2, joinpath(@__DIR__, "out", "certificate.json"))

ws = JSON3.read(read(IN, String))
ws["format"] == FORMAT || error("unsupported format $(ws["format"])")
map = ws["map"]

cert = Certificate("csd-julia 0.1, Catlab $(pkgversion(CsdDDD.Catlab))")

# Contexts and arrows of the map.
schemas = Dict{String,DDDSchema}()
for c in map["contexts"]
  S = read_schema(c["schema"])
  schemas[String(c["name"])] = S
  add_schema!(cert, String(c["name"]), S)
  add_claim!(cert, "wellFormed"; schema=String(c["name"]))
end
translations = Dict{String,Translation}()
for a in map["arrows"]
  T = read_translation(a["translation"])
  translations[String(a["name"])] = T
  add_claim!(cert, "translation"; source=String(a["source"]), target=String(a["target"]),
    translation=write_translation(T))
end

expected(kernel) = begin
  i = findfirst(e -> e["kernel"] == kernel, get(ws, "expectations", []))
  i === nothing ? nothing : Bool.(ws["expectations"][i]["fullyFaithful"])
end

# Strict integration: the targets of the two arrows out of each kernel, glued.
glued_names = Dict{String,String}()
for c in map["contexts"]
  get(c, "kernel", false) || continue
  k = String(c["name"])
  outs = [String(a["target"]) for a in map["arrows"] if a["source"] == k]
  length(outs) == 2 || error("kernel $k has $(length(outs)) arrows; two are glued")
  (l, r) = outs
  G = glue(schemas[k], schemas[l], schemas[r])
  g = "$l+$r"
  schemas[g] = G
  glued_names[k] = g
  add_schema!(cert, g, G)
  add_claim!(cert, "wellFormed"; schema=g)
  ff = expected(k)
  if ff === nothing
    add_claim!(cert, "gluing"; kernel=k, left=l, right=r, glued=g)
  else
    add_claim!(cert, "gluing"; kernel=k, left=l, right=r, glued=g, fullyFaithful=ff)
  end
end

# Scenarios outside the map.
for s in get(ws, "scenarios", [])
  name = String(s["name"])
  K, L, R = read_schema(s["kernel"]), read_schema(s["left"]), read_schema(s["right"])
  G = glue(K, L, R)
  for (suffix, S) in (("kernel", K), ("left", L), ("right", R), ("glued", G))
    add_schema!(cert, "$name/$suffix", S)
  end
  add_claim!(cert, "gluing"; kernel="$name/kernel", left="$name/left", right="$name/right",
    glued="$name/glued", fullyFaithful=Bool.(s["fullyFaithful"]))
end

# ---------------------------------------------------------------------------
# Sample states, in the order of their schemas.

function make_state(S, sizes, refcols, attrcols)
  State([e => sizes[e] for e in CsdDDD.entities(S)],
    [(s, n) => refcols[(s, n)] for (s, n, _) in CsdDDD.refs(S)],
    [(s, n) => Any[x for x in attrcols[(s, n)]] for (s, n, _) in CsdDDD.attrs(S)])
end

const ORDER_IDS = ["7c9e6679-7425-40de-944b-e07fc1f90ae7", "9b2f0c43-1d2e-4f5a-8b6c-3d4e5f6a7b8c"]

customers_refs = Dict(("Customer", "address") => [1, 2])
customers_attrs = Dict(("Customer", "name") => ["Ada", "Grace"],
  ("Address", "street") => ["Bahnhofstrasse 1", "Marktgasse 5"],
  ("Address", "city") => ["Bern", "Basel"])

XO = make_state(schemas["Orders"],
  Dict("Customer" => 2, "Address" => 2, "Order" => 2, "OrderLine" => 3, "Product" => 2),
  merge(customers_refs, Dict(
    ("Order", "customer") => [1, 2], ("Order", "billTo") => [1, 2], ("Order", "shipTo") => [2, 2],
    ("OrderLine", "order") => [1, 1, 2], ("OrderLine", "product") => [1, 2, 1])),
  merge(customers_attrs, Dict(
    ("Order", "id") => ORDER_IDS, ("Order", "placedOn") => ["2026-10-01", "2026-10-02"],
    ("Order", "status") => ["placed", "shipped"],
    ("OrderLine", "quantity") => [2, 1, 4], ("OrderLine", "unitPrice") => ["12.50", "8.00", "12.50"],
    ("OrderLine", "sku") => ["V-100", "V-200", "V-100"],
    ("Product", "sku") => ["V-100", "V-200"], ("Product", "name") => ["Mug", "Plate"],
    ("Product", "listPrice") => ["12.50", "8.00"])))

shipping_state(nship) = make_state(schemas["Shipping"],
  Dict("Customer" => 2, "Address" => 2, "Shipment" => nship, "Item" => nship + 1, "Carrier" => 1),
  merge(customers_refs, Dict(
    ("Shipment", "customer") => [1, 2][1:nship], ("Shipment", "destination") => [2, 2][1:nship],
    ("Shipment", "carrier") => fill(1, nship), ("Item", "shipment") => [1, 1, 2][1:nship+1])),
  merge(customers_attrs, Dict(
    ("Shipment", "orderId") => ORDER_IDS[1:nship],
    ("Shipment", "shippedOn") => ["2026-10-03", "2026-10-04"][1:nship],
    ("Shipment", "trackingCode") => ["CH-0001", "CH-0002"][1:nship],
    ("Shipment", "signatureRequired") => [false, true][1:nship],
    ("Item", "quantity") => [2, 1, 4][1:nship+1],
    ("Item", "declaredValue") => ["25.00", "8.00", "50.00"][1:nship+1],
    ("Item", "sku") => ["V-100", "V-200", "V-100"][1:nship+1],
    ("Item", "description") => ["Mug", "Plate", "Mug"][1:nship+1],
    ("Carrier", "name") => ["Swiss Post"])))

XS = shipping_state(1)
XS2 = shipping_state(2)

# The glued state: the generators of Orders from XO, the others from XS.
G = schemas["Orders+Shipping"]
L = schemas["Orders"]
lrefs = [(s, n) for (s, n, _) in CsdDDD.refs(L)]
lattrs = [(s, n) for (s, n, _) in CsdDDD.attrs(L)]
pick(X1, X2, key, inleft) = CsdDDD.lookup(inleft ? X1 : X2, key)
XG = State(
  [e => (e in CsdDDD.entities(L) ? CsdDDD.size_of(XO, e) : CsdDDD.size_of(XS, e))
    for e in CsdDDD.entities(G)],
  [(s, n) => pick(XO.refs, XS.refs, (s, n), (s, n) in lrefs) for (s, n, _) in CsdDDD.refs(G)],
  [(s, n) => pick(XO.attrs, XS.attrs, (s, n), (s, n) in lattrs) for (s, n, _) in CsdDDD.attrs(G)])

XP = make_state(schemas["Payments"],
  Dict("Payer" => 1, "Address" => 1, "Invoice" => 1, "InvoiceLine" => 2, "Payment" => 1,
    "Refund" => 1),
  Dict(("Payer", "address") => [1], ("Invoice", "payer") => [1], ("Invoice", "shipTo") => [1],
    ("InvoiceLine", "invoice") => [1, 1], ("Payment", "invoice") => [1],
    ("Refund", "payment") => [1], ("Refund", "invoice") => [1]),
  Dict(("Payer", "name") => ["Ada"], ("Address", "street") => ["Bahnhofstrasse 1"],
    ("Address", "city") => ["Bern"], ("Invoice", "orderId") => ORDER_IDS[1:1],
    ("Invoice", "orderedOn") => ["2026-10-01"], ("InvoiceLine", "quantity") => [2, 1],
    ("InvoiceLine", "unitPrice") => ["12.50", "8.00"],
    ("InvoiceLine", "description") => ["Mug", "Plate"], ("Payment", "amount") => ["33.00"],
    ("Payment", "paidOn") => ["2026-10-01"], ("Payment", "method") => ["card"],
    ("Refund", "amount") => ["8.00"], ("Refund", "issuedOn") => ["2026-10-05"]))

states = [("XO", "Orders", XO), ("XS", "Shipping", XS), ("XS2", "Shipping", XS2),
  ("XG", "Orders+Shipping", XG), ("XP", "Payments", XP)]
for (x, s, X) in states
  check_state(schemas[s], X) || error("$x violates an equation of $s")
end

# Restrictions: data gluing, and the anti-corruption layer into Payments.
empty = Translation()
XK = restrict(empty, schemas["Customers"], schemas["Orders"], XO)
restrict(empty, schemas["Customers"], schemas["Shipping"], XS) == XK ||
  error("XO and XS disagree on the kernel")
restrict(empty, L, G, XG) == XO || error("XG does not restrict to XO")
restrict(empty, schemas["Shipping"], G, XG) == XS || error("XG does not restrict to XS")
XPL = restrict(translations["ordersPL_payments"], schemas["OrdersPL"], schemas["Payments"], XP)
push!(states, ("XK", "Customers", XK), ("XPL", "OrdersPL", XPL))

for (x, s, X) in states
  add_state!(cert, x, s, X)
  add_claim!(cert, "state"; state=x)
end
restriction(s, t, T, x, y) = add_claim!(cert, "restriction"; source=s, target=t,
  translation=write_translation(T), state=x, result=y)
restriction("Orders", "Orders+Shipping", empty, "XG", "XO")
restriction("Shipping", "Orders+Shipping", empty, "XG", "XS")
restriction("Customers", "Orders", empty, "XO", "XK")
restriction("Customers", "Shipping", empty, "XS", "XK")
restriction("OrdersPL", "Payments", translations["ordersPL_payments"], "XP", "XPL")

# Homomorphism search: XS into XS2.
h = homomorphism_search(schemas["Shipping"], XS, XS2)
h === nothing && error("no homomorphism XS → XS2")
add_claim!(cert, "homomorphism"; from="XS", to="XS2", homomorphism=Dict("components" =>
  [Dict("type" => e, "column" => c .- 1) for (e, c) in h]))

mkpath(dirname(OUT))
write_certificate(OUT, cert)
println("csd-julia: wrote $OUT with $(length(cert.claims)) claims")
