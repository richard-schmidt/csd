import DDD.Data
import Lean.Data.Json

/-!
# The exchange format

JSON for the deep data, shared with the Julia side. Every document carries the
format identifier `formatVersion`.

- Value types: `"int"`, `"decimal"`, `"string"`, `"date"`, `"uuid"`, `"bool"`, and
  `{"named": n}`.
- Generators are named `Entity.name`; the entity type is the part before the
  first dot, so entity type names contain no dot.
- A schema: `entities`, `references` (`name`, `target`), `attributes` (`name`,
  `type`), `equations` (`source`, `lhs`, `rhs`), `aggregates` (`root`, `members`
  with `entity` and `owner`), `valueObjects`. Lists keep their order.
- A translation: `entities` (`source`, `target`) and `generators` (`name`, `path`).
- A context map (`MapDoc`): `contexts` (`name`, `schema`, `kernel`), `arrows`
  (`name`, `source`, `target`, `translation`), and `routeEquations` (`lhs`, `rhs`,
  lists of arrow names).
- A finite state, relative to its schema: `entities` (`type`, `count`),
  `references` and `attributes` (`name`, `column`). Entities are numbered from 0.
  Attribute values are literals (`Lit`): JSON integers, strings and booleans.
- A homomorphism of finite states: `components` (`type`, `column`).

`Schema.fromJson (Schema.toJson S) = .ok S` for every schema whose entity type
names contain no dot, and likewise for the other kinds; `Examples/Json.lean`
tests the round trips on the examples.
-/

namespace DDD

open Lean

/-- The format identifier of the documents. -/
def formatVersion : String := "csd-ddd/1"

/-! ## Value types and literals -/

def ValueType.toJson : ValueType → Json
  | .int => .str "int"
  | .decimal => .str "decimal"
  | .string => .str "string"
  | .date => .str "date"
  | .uuid => .str "uuid"
  | .bool => .str "bool"
  | .named n => Json.mkObj [("named", .str n)]

def ValueType.fromJson : Json → Except String ValueType
  | .str "int" => pure .int
  | .str "decimal" => pure .decimal
  | .str "string" => pure .string
  | .str "date" => pure .date
  | .str "uuid" => pure .uuid
  | .str "bool" => pure .bool
  | .str s => throw s!"unknown value type {s}"
  | j => .named <$> j.getObjValAs? String "named"

instance : ToJson ValueType := ⟨ValueType.toJson⟩
instance : FromJson ValueType := ⟨ValueType.fromJson⟩

/-- A literal value: the values of finite states in the exchange format. Decimals,
dates, UUIDs and named values are written as text. -/
inductive Lit where
  | int (i : Int)
  | text (s : String)
  | bool (b : Bool)
deriving DecidableEq, Repr

/-- The literals that a value type admits. -/
def Lit.fits : Lit → ValueType → Bool
  | .int _, .int => true
  | .bool _, .bool => true
  | .text _, .int => false
  | .text _, .bool => false
  | .text _, _ => true
  | _, _ => false

instance : ToJson Lit where
  toJson
    | .int i => toJson i
    | .text s => .str s
    | .bool b => .bool b

instance : FromJson Lit where
  fromJson?
    | .str s => pure (.text s)
    | .bool b => pure (.bool b)
    | j => .int <$> j.getInt?

/-! ## Names -/

/-- The name of a generator in the exchange format. -/
def genName (e n : String) : String := e ++ "." ++ n

/-- The entity type and the name of a generator. -/
def splitGen (s : String) : Except String (String × String) :=
  match s.splitOn "." with
  | e :: n :: rest => pure (e, ".".intercalate (n :: rest))
  | _ => throw s!"generator name without an entity type: {s}"

/-! ## Schemas -/

def Schema.toJson (S : Schema) : Json := Json.mkObj [
  ("entities", Lean.toJson S.entities),
  ("references", Json.arr (S.refs.map fun r =>
    Json.mkObj [("name", .str (genName r.src r.name)), ("target", .str r.tgt)]).toArray),
  ("attributes", Json.arr (S.attrs.map fun a =>
    Json.mkObj [("name", .str (genName a.src a.name)), ("type", Lean.toJson a.tgt)]).toArray),
  ("equations", Json.arr (S.eqns.map fun q =>
    Json.mkObj [("source", .str q.src), ("lhs", Lean.toJson q.lhs),
      ("rhs", Lean.toJson q.rhs)]).toArray),
  ("aggregates", Json.arr (S.aggregates.map fun A =>
    Json.mkObj [("root", .str A.root), ("members", Json.arr (A.members.map fun m =>
      Json.mkObj [("entity", .str m.entity), ("owner", .str m.owner)]).toArray)]).toArray),
  ("valueObjects", Lean.toJson S.valueObjects)]

/-- An optional list field: absent means empty. -/
def getList (j : Json) (key : String) : Except String (List Json) :=
  match j.getObjVal? key with
  | .ok v => do let a ← v.getArr?; pure a.toList
  | .error _ => pure []

def Schema.fromJson (j : Json) : Except String Schema := do
  let entities ← j.getObjValAs? (List String) "entities"
  let refs ← (← getList j "references").mapM fun r => do
    let (src, name) ← splitGen (← r.getObjValAs? String "name")
    let tgt ← r.getObjValAs? String "target"
    pure ({ name, src, tgt } : Ref)
  let attrs ← (← getList j "attributes").mapM fun a => do
    let (src, name) ← splitGen (← a.getObjValAs? String "name")
    let tgt ← a.getObjValAs? ValueType "type"
    pure ({ name, src, tgt } : Attr)
  let eqns ← (← getList j "equations").mapM fun q => do
    let src ← q.getObjValAs? String "source"
    let lhs ← q.getObjValAs? (List String) "lhs"
    let rhs ← q.getObjValAs? (List String) "rhs"
    pure ({ src, lhs, rhs } : Equation)
  let aggregates ← (← getList j "aggregates").mapM fun A => do
    let members ← (← getList A "members").mapM fun m => do
      let entity ← m.getObjValAs? String "entity"
      let owner ← m.getObjValAs? String "owner"
      pure ({ entity, owner } : Member)
    let root ← A.getObjValAs? String "root"
    pure ({ root, members } : Aggregate)
  let valueObjects ← (← getList j "valueObjects").mapM fun v => v.getStr?
  pure { entities, refs, attrs, eqns, aggregates, valueObjects }

instance : ToJson Schema := ⟨Schema.toJson⟩
instance : FromJson Schema := ⟨Schema.fromJson⟩

/-! ## Translations -/

def Translation.toJson (T : Translation) : Json := Json.mkObj [
  ("entities", Json.arr (T.entities.map fun p =>
    Json.mkObj [("source", .str p.1), ("target", .str p.2)]).toArray),
  ("generators", Json.arr (T.gens.map fun g =>
    Json.mkObj [("name", .str (genName g.src g.name)), ("path", Lean.toJson g.path)]).toArray)]

def Translation.fromJson (j : Json) : Except String Translation := do
  let entities ← (← getList j "entities").mapM fun p => do
    pure (← p.getObjValAs? String "source", ← p.getObjValAs? String "target")
  let gens ← (← getList j "generators").mapM fun g => do
    let (src, name) ← splitGen (← g.getObjValAs? String "name")
    let path ← g.getObjValAs? (List String) "path"
    pure ({ src, name, path } : GenImage)
  pure { entities, gens }

instance : ToJson Translation := ⟨Translation.toJson⟩
instance : FromJson Translation := ⟨Translation.fromJson⟩

/-! ## Context maps -/

/-- A context map as data: contexts with their schemas and kernel flags, named
arrows with their translations, and equations between routes, as lists of arrow
names. -/
structure MapDoc where
  contexts : List (String × Schema × Bool)
  arrows : List (String × String × String × Translation)
  routeEqns : List (List String × List String) := []
deriving DecidableEq

def MapDoc.toJson (M : MapDoc) : Json := Json.mkObj [
  ("format", .str formatVersion), ("kind", .str "map"),
  ("contexts", Json.arr (M.contexts.map fun c =>
    Json.mkObj [("name", .str c.1), ("schema", c.2.1.toJson), ("kernel", .bool c.2.2)]).toArray),
  ("arrows", Json.arr (M.arrows.map fun a =>
    Json.mkObj [("name", .str a.1), ("source", .str a.2.1), ("target", .str a.2.2.1),
      ("translation", a.2.2.2.toJson)]).toArray),
  ("routeEquations", Json.arr (M.routeEqns.map fun e =>
    Json.mkObj [("lhs", Lean.toJson e.1), ("rhs", Lean.toJson e.2)]).toArray)]

def MapDoc.fromJson (j : Json) : Except String MapDoc := do
  let contexts ← (← getList j "contexts").mapM fun c => do
    pure (← c.getObjValAs? String "name", ← Schema.fromJson (← c.getObjVal? "schema"),
      (c.getObjValAs? Bool "kernel").toOption.getD false)
  let arrows ← (← getList j "arrows").mapM fun a => do
    pure (← a.getObjValAs? String "name", ← a.getObjValAs? String "source",
      ← a.getObjValAs? String "target", ← Translation.fromJson (← a.getObjVal? "translation"))
  let routeEqns ← (← getList j "routeEquations").mapM fun e => do
    pure (← e.getObjValAs? (List String) "lhs", ← e.getObjValAs? (List String) "rhs")
  pure { contexts, arrows, routeEqns }

/-! ## Finite states and homomorphisms -/

/-- The literals of the exchange format, at every value type. -/
abbrev LitK : ValueType → Type := fun _ => Lit

def FinState.toJson (X : FinState LitK) : Json := Json.mkObj [
  ("entities", Json.arr (X.sizes.map fun p =>
    Json.mkObj [("type", .str p.1), ("count", Lean.toJson p.2)]).toArray),
  ("references", Json.arr (X.refs.map fun c =>
    Json.mkObj [("name", .str (genName c.1.1 c.1.2)), ("column", Lean.toJson c.2)]).toArray),
  ("attributes", Json.arr (X.attrs.map fun c =>
    Json.mkObj [("name", .str (genName c.1.1 c.1.2)),
      ("column", Json.arr (c.2.map fun x => Lean.toJson x.2).toArray)]).toArray)]

/-- A finite state of `S`, read from JSON; each attribute value is given the value
type that `S` declares for its attribute. -/
def FinState.fromJson (S : Schema) (j : Json) : Except String (FinState LitK) := do
  let sizes ← (← getList j "entities").mapM fun p => do
    pure (← p.getObjValAs? String "type", ← p.getObjValAs? Nat "count")
  let refs ← (← getList j "references").mapM fun c => do
    pure (← splitGen (← c.getObjValAs? String "name"), ← c.getObjValAs? (List Nat) "column")
  let attrs ← (← getList j "attributes").mapM fun c => do
    let (e, n) ← splitGen (← c.getObjValAs? String "name")
    let some a := S.attr? e n | throw s!"no attribute {genName e n} in the schema"
    let col ← (← getList c "column").mapM fun x => do
      let l : Lit ← fromJson? x
      pure (⟨a.tgt, l⟩ : Σ v, LitK v)
    pure ((e, n), col)
  pure { sizes, refs, attrs }

/-- Every attribute value of `X` is a literal of its value type. -/
def FinState.litsFit (X : FinState LitK) : Bool :=
  X.attrs.all fun c => c.2.all fun x => x.2.fits x.1

def FinHom.toJson (h : FinHom) : Json := Json.mkObj [
  ("components", Json.arr (h.comps.map fun c =>
    Json.mkObj [("type", .str c.1), ("column", Lean.toJson c.2)]).toArray)]

def FinHom.fromJson (j : Json) : Except String FinHom := do
  let comps ← (← getList j "components").mapM fun c => do
    pure (← c.getObjValAs? String "type", ← c.getObjValAs? (List Nat) "column")
  pure { comps }

end DDD
