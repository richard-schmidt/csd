# Round trips of the exchange format on the Julia side.
#
#     julia --project=julia julia/test/runtests.jl

include(joinpath(@__DIR__, "..", "src", "CsdDDD.jl"))
using .CsdDDD
using JSON3
using Test

plain(x::JSON3.Object) = Dict(String(k) => plain(v) for (k, v) in x)
plain(x::JSON3.Array) = [plain(v) for v in x]
plain(x::AbstractDict) = Dict(String(k) => plain(v) for (k, v) in x)
plain(x::AbstractVector) = [plain(v) for v in x]
plain(x) = x

roundtrip(write, read, j) = plain(JSON3.read(JSON3.write(write(read(j)))))

ws = JSON3.read(read(joinpath(@__DIR__, "..", "data", "workspace.json"), String))

@testset "schemas" begin
  for c in ws["map"]["contexts"]
    @test roundtrip(write_schema, read_schema, c["schema"]) == plain(c["schema"])
  end
end

@testset "translations" begin
  for a in ws["map"]["arrows"]
    @test roundtrip(write_translation, read_translation, a["translation"]) ==
      plain(a["translation"])
  end
end

@testset "samples" begin
  for x in get(ws, "samples", [])
    @test roundtrip(write_schema, read_schema, x["schema"]) == plain(x["schema"])
    @test roundtrip(write_state, read_state, x["state"]) == plain(x["state"])
  end
end

@testset "keys" begin
  ctx = Dict(String(c["name"]) => read_schema(c["schema"]) for c in ws["map"]["contexts"])
  G = glue(ctx["Customers"], ctx["Orders"], ctx["Shipping"])
  @test G.keys == ctx["Orders"].keys
  @test ("OrderLine", ["order", "product"]) in G.keys
  sales = read_schema(only(x for x in ws["samples"] if x["name"] == "Sales")["schema"])
  @test ("BusinessCustomer", "customer") in sales.subtypes
end

@testset "conversions" begin
  L = read_types(ws["map"]["valueTypes"])
  instant, status = ("named", "Instant"), ("named", "OrderStatus")
  @test conv(L, instant, "timestamp") == "timestamp"
  @test conv(L, instant, "date") === nothing
  @test conv(L, ("optional", ("named", "Money")), "decimal") == ("optional", "decimal")
  @test apply_lit(L, instant, ["timestamp", "date"], "2026-11-04T08:30:00Z") == "2026-11-04"
  @test apply_lit(L, instant, ["timestamp", "time"], "2026-11-04T08:30:00Z") == "08:30:00"
  @test apply_lit(L, status, ["phase", "isOpen"], "shipped") == false
  @test apply_lit(L, status, ["active", "string"], "paid") == "true"
  @test apply_lit(L, ("optional", ("named", "Money")), ["decimal", "string"], nothing) === nothing
  addr = Dict{String,Any}("street" => "Bahnhofstrasse 1", "city" => "Bern", "zip" => nothing)
  @test apply_lit(L, ("named", "PostalAddress"), ["city"], addr) == "Bern"
  @test apply_lit(L, ("named", "PostalAddress"), ["string"], addr) ==
    "{city: Bern, street: Bahnhofstrasse 1, zip: null}"
  @test_throws ErrorException apply_lit(L, "int", ["date"], 3)
end

@testset "states" begin
  cert = JSON3.read(read(joinpath(@__DIR__, "..", "out", "certificate.json"), String))
  for x in cert["states"]
    @test roundtrip(write_state, read_state, x["state"]) == plain(x["state"])
  end
end
