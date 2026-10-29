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

@testset "states" begin
  cert = JSON3.read(read(joinpath(@__DIR__, "..", "out", "certificate.json"), String))
  for x in cert["states"]
    @test roundtrip(write_state, read_state, x["state"]) == plain(x["state"])
  end
end
