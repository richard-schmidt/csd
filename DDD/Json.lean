import DDD.Data
import DDD.Literals
import Lean.Data.Json

/-!
# The exchange format

JSON for the deep data, shared with the Julia side. Every document carries the
format identifier `formatVersion`.

- Value types: `"int"`, `"decimal"`, `"string"`, `"date"`, `"uuid"`, `"bool"`,
  `"datetime"`, `"timestamp"`, `"time"`, `"duration"`, `{"named": n}` and
  `{"optional": t}`.
- The list of value types (`TypeList`): `name`, with `values` for an
  enumeration or `base` for a named type over a built-in.
- Generators are named `Entity.name`; the entity type is the part before the
  first dot, so entity type names contain no dot.
- A schema: `entities`, `references` (`name`, `target`), `attributes` (`name`,
  `type`), `equations` (`source`, `lhs`, `rhs`), `aggregates` (`root`, `members`
  with `entity` and `owner`), `valueObjects`, `keys` (`entity`, `fields`, the
  names of generators out of the entity type) and `subtypes` (`entity`,
  `reference`, the name of the is-a reference). Lists keep their order.
- A translation: `entities` (`source`, `target`) and `generators` (`name`, `path`).
- A context map (`MapDoc`): `valueTypes`, `contexts` (`name`, `schema`,
  `kernel`), `arrows` (`name`, `source`, `target`, `translation`), and
  `routeEquations` (`lhs`, `rhs`, lists of arrow names).
- A finite state, relative to its schema: `entities` (`type`, `count`),
  `references` and `attributes` (`name`, `column`). Entities are numbered from 0.
  Attribute values are literals (`Lit`): JSON integers, strings, booleans and
  `null`; a JSON number that is not an integer is read as its decimal text.
  `FinState.fromJson` keeps the literals as written; `FinState.normalize` puts
  them in normal form (`DDD.Literals`), and the readers of certificates and of
  context map documents apply it.
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
  | .datetime => .str "datetime"
  | .timestamp => .str "timestamp"
  | .time => .str "time"
  | .duration => .str "duration"
  | .named n => Json.mkObj [("named", .str n)]
  | .optional v => Json.mkObj [("optional", v.toJson)]

partial def ValueType.fromJson : Json → Except String ValueType
  | .str "int" => pure .int
  | .str "decimal" => pure .decimal
  | .str "string" => pure .string
  | .str "date" => pure .date
  | .str "uuid" => pure .uuid
  | .str "bool" => pure .bool
  | .str "datetime" => pure .datetime
  | .str "timestamp" => pure .timestamp
  | .str "time" => pure .time
  | .str "duration" => pure .duration
  | .str s => throw s!"unknown value type {s}"
  | j => match j.getObjVal? "named", j.getObjVal? "optional" with
    | .ok n, _ => .named <$> n.getStr?
    | _, .ok t => .optional <$> ValueType.fromJson t
    | _, _ => throw s!"unknown value type {j.compress}"

instance : ToJson ValueType := ⟨ValueType.toJson⟩
instance : FromJson ValueType := ⟨ValueType.fromJson⟩

instance : ToJson Lit where
  toJson
    | .int i => toJson i
    | .text s => .str s
    | .bool b => .bool b
    | .null => .null

instance : FromJson Lit where
  fromJson?
    | .str s => pure (.text s)
    | .bool b => pure (.bool b)
    | .null => pure .null
    | .num n => pure (if n.exponent == 0 then .int n.mantissa else .text (toString n))
    | j => throw s!"not a literal: {j.compress}"

def TypeList.toJson (L : TypeList) : Json := Json.arr (L.decls.map fun d =>
  match d.2 with
  | .enum vs => Json.mkObj [("name", .str d.1), ("values", Lean.toJson vs)]
  | .over b => Json.mkObj [("name", .str d.1), ("base", b.toJson)]).toArray

def TypeList.fromJson (j : Json) : Except String TypeList := do
  let a ← j.getArr?
  let decls ← a.toList.mapM fun d => do
    let name ← d.getObjValAs? String "name"
    match d.getObjValAs? (List String) "values", d.getObjVal? "base" with
    | .ok vs, _ => pure (name, TypeDecl.enum vs)
    | _, .ok b => pure (name, TypeDecl.over (← ValueType.fromJson b))
    | _, _ => throw s!"the value type {name} has neither values nor a base"
  pure { decls }

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
  ("valueObjects", Lean.toJson S.valueObjects),
  ("keys", Json.arr (S.keys.map fun k =>
    Json.mkObj [("entity", .str k.entity), ("fields", Lean.toJson k.fields)]).toArray),
  ("subtypes", Json.arr (S.subtypes.map fun s =>
    Json.mkObj [("entity", .str s.entity), ("reference", .str s.ref)]).toArray)]

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
  let keys ← (← getList j "keys").mapM fun k => do
    let entity ← k.getObjValAs? String "entity"
    let fields ← k.getObjValAs? (List String) "fields"
    pure ({ entity, fields } : Key)
  let subtypes ← (← getList j "subtypes").mapM fun s => do
    let entity ← s.getObjValAs? String "entity"
    let ref ← s.getObjValAs? String "reference"
    pure ({ entity, ref } : IsA)
  pure { entities, refs, attrs, eqns, aggregates, valueObjects, keys, subtypes }

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

/-- A context map as data: the list of value types, contexts with their schemas
and kernel flags, named arrows with their translations, and equations between
routes, as lists of arrow names. -/
structure MapDoc where
  valueTypes : TypeList := {}
  contexts : List (String × Schema × Bool)
  arrows : List (String × String × String × Translation)
  routeEqns : List (List String × List String) := []
deriving DecidableEq

def MapDoc.toJson (M : MapDoc) : Json := Json.mkObj [
  ("format", .str formatVersion), ("kind", .str "map"),
  ("valueTypes", M.valueTypes.toJson),
  ("contexts", Json.arr (M.contexts.map fun c =>
    Json.mkObj [("name", .str c.1), ("schema", c.2.1.toJson), ("kernel", .bool c.2.2)]).toArray),
  ("arrows", Json.arr (M.arrows.map fun a =>
    Json.mkObj [("name", .str a.1), ("source", .str a.2.1), ("target", .str a.2.2.1),
      ("translation", a.2.2.2.toJson)]).toArray),
  ("routeEquations", Json.arr (M.routeEqns.map fun e =>
    Json.mkObj [("lhs", Lean.toJson e.1), ("rhs", Lean.toJson e.2)]).toArray)]

def MapDoc.fromJson (j : Json) : Except String MapDoc := do
  let valueTypes ← match j.getObjVal? "valueTypes" with
    | .ok v => TypeList.fromJson v
    | .error _ => pure {}
  let contexts ← (← getList j "contexts").mapM fun c => do
    pure (← c.getObjValAs? String "name", ← Schema.fromJson (← c.getObjVal? "schema"),
      (c.getObjValAs? Bool "kernel").toOption.getD false)
  let arrows ← (← getList j "arrows").mapM fun a => do
    pure (← a.getObjValAs? String "name", ← a.getObjValAs? String "source",
      ← a.getObjValAs? String "target", ← Translation.fromJson (← a.getObjVal? "translation"))
  let routeEqns ← (← getList j "routeEquations").mapM fun e => do
    pure (← e.getObjValAs? (List String) "lhs", ← e.getObjValAs? (List String) "rhs")
  pure { valueTypes, contexts, arrows, routeEqns }

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

/-- `X` with each literal in normal form for its value type, where it has one; a
literal that is not a value of its type is kept as written. -/
def FinState.normalize (L : TypeList) (X : FinState LitK) : FinState LitK :=
  { X with attrs := X.attrs.map fun c => (c.1, c.2.map fun x =>
      ⟨x.1, (L.normalize x.1 x.2).toOption.getD x.2⟩) }

/-- Every attribute value of `X` is a literal of its value type, in normal form. -/
def FinState.litsFit (L : TypeList) (X : FinState LitK) : Bool :=
  X.attrs.all fun c => c.2.all fun x => match L.normalize x.1 x.2 with
    | .ok l => l == x.2
    | .error _ => false

/-- A literal that is not a value of its type, or not in normal form: the
attribute, the number of the entity, the literal, its value type, and why. -/
structure LitProblem where
  attr : String × String
  entity : Nat
  lit : Lit
  type : ValueType
  message : String

/-- The literals of `X` that are not values of their types in normal form. -/
def FinState.litProblems (L : TypeList) (X : FinState LitK) : List LitProblem :=
  X.attrs.flatMap fun c => ((List.range c.2.length).zip c.2).filterMap fun (i, x) =>
    match L.normalize x.1 x.2 with
    | .ok l => if l == x.2 then none
      else some ⟨c.1, i, x.2, x.1,
        s!"{x.2.render} is not in normal form; it is written {l.render}"⟩
    | .error e => some ⟨c.1, i, x.2, x.1, e⟩

def FinHom.toJson (h : FinHom) : Json := Json.mkObj [
  ("components", Json.arr (h.comps.map fun c =>
    Json.mkObj [("type", .str c.1), ("column", Lean.toJson c.2)]).toArray)]

def FinHom.fromJson (j : Json) : Except String FinHom := do
  let comps ← (← getList j "components").mapM fun c => do
    pure (← c.getObjValAs? String "type", ← c.getObjValAs? (List Nat) "column")
  pure { comps }

end DDD
