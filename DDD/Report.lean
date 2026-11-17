import DDD.Certificate
import DDD.Problems

/-!
# Reports

A report says, for each claim of a certificate, whether its check passes and,
when it fails, which problems explain the failure. Whether a claim holds is
decided by `Certificate.checkClaim` alone, which is sound
(`Certificate.checkClaim_sound`). The problems explain a failure:

- well-formedness: the problems of the schema (`Schema.problems`), none exactly
  when the check passes;
- acyclicity: those, and a path longer than the number of entity types;
- translation: the problems of the target schema and of the translation with
  conversions (`Translation.vproblems`), none exactly when the check passes;
- keys kept: each key of the source that the translation does not keep
  (`Translation.keysNotKept`, problem `keyNotKept`), none exactly when the check
  passes;
- the list of value types: its problems (`TypeList.problems`), none exactly
  when it is sound;
- declared value types: the attributes whose value types the list does not admit
  (`Schema.typeProblems`), none exactly when the check passes;
- state: the parts of the check that fail, and each literal that is not a value
  of its type in normal form, with the reason;
- gluing, restriction, homomorphism: the parts of the check that fail, with
  the problems of the schemas and translations involved and the names that two
  schemas share outside a kernel;
- agreement: those parts, and each entity type and generator of the shared
  schema on which the two restrictions differ (problem `disagree`);
- conformance: those parts, and components that are not a homomorphism between
  the two restrictions;
- normal form: the problems of the schemas and of the translation, the entity
  types the translation does not keep apart (`entitiesMerged`), and the problems
  of the definitional extension;
- event type: a name that is an entity type (`eventName`), a reference to an
  entity type the schema does not have (`eventTarget`), a value type that is not
  admitted, and the problems of the event schema;
- occurrence: those, the parts of the check that fail, a field without a value or
  with a value of another type (`occurrenceField`), and a reference to an entity
  that the view does not have (`danglingReference`);
- path equality: the problems of the schema, a path that does not exist, two
  paths that do not end at the same object, and normal forms that differ;
- conversion: a path of conversions that does not exist, a literal that is not
  in normal form, and the result of `TypeList.applyLit` when it differs or fails.

A failing claim with no explanation reports that its check fails.

A context map document (`MapDoc`) is checked through the certificate of its
claims (`MapDoc.certificate`): its list of value types is sound, each context is
well formed and declares its value types, and each arrow is a translation from
the schema of its source to the schema of its target, valid with conversions,
that keeps the keys of its source (problem `keyNotKept`). The conditions on the
map as a whole, and `MapDoc.report`, are in `MapCheck.lean`.

Every problem is a JSON object with a `kind`, the names it concerns, and a
`message`. `Certificate.report` and `MapDoc.report` are the output of
`csd-check --json`.
-/

namespace DDD

open Lean

/-! ## Problems as JSON -/

def Ob.toJson : Ob → Json
  | .entity e => Json.mkObj [("entity", .str e)]
  | .value v => Json.mkObj [("value", Lean.toJson v)]

def Equation.toJson (q : Equation) : Json :=
  Json.mkObj [("source", .str q.src), ("lhs", Lean.toJson q.lhs), ("rhs", Lean.toJson q.rhs)]

def endJson : Option Ob → Json
  | some o => o.toJson
  | none => .null

/-- A problem: its kind, the names it concerns, and a sentence. -/
def problemJson (kind : String) (fields : List (String × Json)) (message : String) : Json :=
  Json.mkObj ([("kind", .str kind)] ++ fields ++ [("message", .str message)])

namespace Schema.Problem

/-- The names a problem concerns. Generators are named `Entity.name`, as in the
exchange format. -/
def fields : Problem → List (String × Json)
  | .duplicateEntity e => [("entity", .str e)]
  | .duplicateGenerator e n => [("entity", .str e), ("generator", .str s!"{e}.{n}")]
  | .refSource r | .refTarget r =>
    [("generator", .str s!"{r.src}.{r.name}"), ("source", .str r.src), ("target", .str r.tgt)]
  | .attrSource a =>
    [("generator", .str s!"{a.src}.{a.name}"), ("source", .str a.src),
      ("type", Lean.toJson a.tgt)]
  | .eqnSource q => [("equation", q.toJson)]
  | .eqnNotParallel q l r =>
    [("equation", q.toJson), ("lhsEnd", endJson l), ("rhsEnd", endJson r)]
  | .aggregateEntity root e => [("aggregate", .str root), ("entity", .str e)]
  | .aggregateOverlap e => [("entity", .str e)]
  | .missingOwner root m | .ownerCycle root m =>
    [("aggregate", .str root), ("entity", .str m.entity),
      ("generator", .str s!"{m.entity}.{m.owner}")]
  | .boundary r root =>
    [("generator", .str s!"{r.src}.{r.name}"), ("source", .str r.src), ("target", .str r.tgt),
      ("aggregate", .str root)]
  | .valueObjectEntity e | .valueObjectFields e => [("entity", .str e)]
  | .keyEntity k => [("entity", .str k.entity), ("key", Lean.toJson k.fields)]
  | .keyEmpty e => [("entity", .str e)]
  | .keyField k n =>
    [("entity", .str k.entity), ("key", Lean.toJson k.fields),
      ("generator", .str s!"{k.entity}.{n}")]
  | .subtypeEntity e => [("entity", .str e)]
  | .subtypeRef s => [("entity", .str s.entity), ("generator", .str s!"{s.entity}.{s.ref}")]

/-- A problem of the schema named `schema`. -/
def toJson (schema : String) (p : Problem) : Json :=
  problemJson p.kind ([("schema", .str schema)] ++ p.fields) p.describe

end Schema.Problem

namespace Translation.Problem

def fields : Problem → List (String × Json)
  | .entity e image => [("entity", .str e), ("image", .str image)]
  | .ref r path expected ends =>
    [("generator", .str s!"{r.src}.{r.name}"), ("path", Lean.toJson path),
      ("expected", expected.toJson), ("ends", endJson ends)]
  | .attr a path ends =>
    [("generator", .str s!"{a.src}.{a.name}"), ("path", Lean.toJson path),
      ("expected", (Ob.value a.tgt).toJson), ("ends", endJson ends)]
  | .eqnSource q image => [("equation", q.toJson), ("image", .str image)]
  | .eqn q l r =>
    [("equation", q.toJson), ("lhsImage", Lean.toJson l), ("rhsImage", Lean.toJson r)]

/-- A problem of the translation from the schema named `source` to the schema named
`target`. -/
def toJson (source target : String) (p : Problem) : Json :=
  problemJson p.kind ([("source", .str source), ("target", .str target)] ++ p.fields) p.describe

end Translation.Problem

/-- A problem of the list of value types. -/
def TypeList.Problem.toJson (p : TypeList.Problem) : Json :=
  problemJson p.kind (match p with
    | .duplicateType n | .builtinName n | .emptyEnum n | .emptyRecord n => [("type", .str n)]
    | .duplicateValue n v => [("type", .str n), ("value", .str v)]
    | .baseNotBuiltin n b => [("type", .str n), ("base", Lean.toJson b)]
    | .duplicateField n f | .reservedField n f => [("type", .str n), ("field", .str f)]
    | .fieldType n f t => [("type", .str n), ("field", .str f), ("fieldType", Lean.toJson t)]
    | .duplicateTable t | .tableName t => [("table", .str t)]
    | .tableSource t v | .tableTarget t v => [("table", .str t), ("type", Lean.toJson v)]
    | .rowTwice t x | .rowSource t x | .rowTarget t x | .rowMissing t x =>
      [("table", .str t), ("value", .str x)]) p.describe

/-- A value type of an attribute of the schema named `schema` that the list does not
admit. -/
def Schema.TypeProblem.toJson (schema : String) (p : Schema.TypeProblem) : Json :=
  problemJson p.kind ([("schema", .str schema)] ++ match p with
    | .undeclared a n => [("generator", .str s!"{a.src}.{a.name}"), ("source", .str a.src),
        ("type", Lean.toJson a.tgt), ("name", .str n)]
    | .nestedOptional a => [("generator", .str s!"{a.src}.{a.name}"), ("source", .str a.src),
        ("type", Lean.toJson a.tgt)]) p.describe

/-- A literal of the state named `state` that is not a value of its type in normal
form. -/
def LitProblem.toJson (state : String) (p : LitProblem) : Json :=
  problemJson "literal" [("state", .str state), ("generator", .str s!"{p.attr.1}.{p.attr.2}"),
    ("entity", (p.entity : Nat)), ("value", Lean.toJson p.lit), ("type", Lean.toJson p.type)]
    s!"{p.attr.1}.{p.attr.2} of entity {p.entity}: {p.message}"

/-- A path out of an entity type of `S` with more generators than `S` has entity
types, if there is one; such a path runs through a cycle. -/
def Schema.longPath? (S : Schema) : Option (String × List String) :=
  S.entities.findSome? fun e =>
    ((S.paths (.entity e) (S.entities.length + 1)).find? fun l =>
      S.entities.length < l.length).map (e, ·)

/-! ## Claims -/

/-- The names a claim is about, as in the certificate format. -/
def Claim.refFields : Claim → List (String × Json)
  | .wellFormed s => [("claim", .str "wellFormed"), ("schema", .str s)]
  | .acyclic s => [("claim", .str "acyclic"), ("schema", .str s)]
  | .translation s t _ => [("claim", .str "translation"), ("source", .str s), ("target", .str t)]
  | .keysKept s t _ => [("claim", .str "keysKept"), ("source", .str s), ("target", .str t)]
  | .gluing k l r g _ => [("claim", .str "gluing"), ("kernel", .str k), ("left", .str l),
      ("right", .str r), ("glued", .str g)]
  | .state x => [("claim", .str "state"), ("state", .str x)]
  | .valueTypes => [("claim", .str "valueTypes")]
  | .declared s => [("claim", .str "declared"), ("schema", .str s)]
  | .restriction s t _ x y => [("claim", .str "restriction"), ("source", .str s),
      ("target", .str t), ("state", .str x), ("result", .str y)]
  | .agreement p l r _ _ x y => [("claim", .str "agreement"), ("shared", .str p),
      ("left", .str l), ("right", .str r), ("leftState", .str x), ("rightState", .str y)]
  | .conformance p l r _ _ x y _ => [("claim", .str "conformance"), ("shared", .str p),
      ("left", .str l), ("right", .str r), ("leftState", .str x), ("rightState", .str y)]
  | .normalForm s t _ => [("claim", .str "normalForm"), ("source", .str s), ("target", .str t)]
  | .eventType s ev => [("claim", .str "eventType"), ("schema", .str s), ("event", .str ev.name)]
  | .occurrence p s _ ev x _ => [("claim", .str "occurrence"), ("shared", .str p),
      ("context", .str s), ("event", .str ev.name), ("state", .str x)]
  | .homomorphism x y _ => [("claim", .str "homomorphism"), ("from", .str x), ("to", .str y)]
  | .pathEquality s o l r => [("claim", .str "pathEquality"), ("schema", .str s),
      ("from", o.toJson), ("lhs", Lean.toJson l), ("rhs", Lean.toJson r)]
  | .conversion v l x _ => [("claim", .str "conversion"), ("type", Lean.toJson v),
      ("path", Lean.toJson l), ("value", Lean.toJson x)]

namespace Certificate

variable (c : Certificate)

def unknown (what name : String) : Json :=
  problemJson s!"unknown{what.capitalize}" [(what, .str name)] s!"there is no {what} named {name}"

/-- The problems of a named schema, or that it is missing. -/
def schemaProblems (n : String) : List Json :=
  match c.schema? n with
  | some S => S.problems.map (Schema.Problem.toJson n)
  | none => [unknown "schema" n]

/-- The parts of a check that fail, each with its kind and sentence. -/
def failing (parts : List (Bool × String × String)) : List Json :=
  parts.filterMap fun (ok, kind, message) => if ok then none else some (problemJson kind [] message)

/-- The problems of the inclusion of `n` into `m` by the empty translation. -/
def inclusionProblems (n m : String) (S S' : Schema) : List Json :=
  ((({} : Translation).problems S S' S'.pathEq).map (Translation.Problem.toJson n m))

/-- The problems of an event type over the schema named `s`: a name that is an entity
type of the schema, references to entity types the schema does not have, value
types the list does not admit, and the problems of the event schema that are not
problems of the schema, among them a reference to a member of an aggregate. A target
that is not an entity type is reported once, as `eventTarget`. -/
def eventProblems (s : String) (P : Schema) (ev : EventType) : List Json :=
  (if P.entities.contains ev.name then
    [problemJson "eventName" [("schema", .str s), ("event", .str ev.name)]
      s!"{ev.name} is an entity type of {s}, so it cannot name an event type over it"]
  else []) ++
  (ev.refs.filter fun r => !P.entities.contains r.2).map (fun r =>
    problemJson "eventTarget" [("schema", .str s), ("event", .str ev.name),
      ("field", .str r.1), ("target", .str r.2)]
      s!"the reference {r.1} of the event type {ev.name} goes to {r.2}, which is not an entity \
        type of {s}") ++
  (ev.attrs.filter fun a => !c.valueTypes.admits a.2).map (fun a =>
    problemJson "undeclaredValueType" [("schema", .str s), ("event", .str ev.name),
      ("field", .str a.1), ("type", Lean.toJson a.2)]
      s!"the list of value types does not admit {a.2.text}, the type of {a.1} of the event type \
        {ev.name}") ++
  (if P.entities.contains ev.name then [] else
    ((ev.over P).problems.filter fun p => !P.problems.contains p && !p matches .refTarget _).map
      (Schema.Problem.toJson s!"{ev.name} over {s}"))

/-- The fields of an occurrence that keep it from being one over the state `V` of
the published language: a reference or an attribute without a value, a reference to
an entity that `V` does not have, a value of another type, and a name that is no
field of the event type. -/
def occurrenceProblems (ev : EventType) (V : FinState LitK) (occ : Occurrence LitK) : List Json :=
  ev.refs.filterMap (fun r => match occ.refs.lookup r.1 with
    | none => some (problemJson "occurrenceField" [("event", .str ev.name), ("field", .str r.1)]
        s!"the occurrence of {ev.name} has no entity for {r.1}")
    | some i => if i < V.size r.2 then none else
        some (problemJson "danglingReference" [("event", .str ev.name), ("field", .str r.1),
          ("entity", (i : Nat)), ("target", .str r.2), ("count", (V.size r.2 : Nat))]
          s!"{r.1} of the occurrence of {ev.name} names the entity {i} of {r.2}, and there are \
            {V.size r.2}")) ++
  ev.attrs.filterMap (fun a => match occ.attrs.lookup a.1 with
    | none => some (problemJson "occurrenceField" [("event", .str ev.name), ("field", .str a.1)]
        s!"the occurrence of {ev.name} has no value for {a.1}")
    | some x => if x.1 == a.2 then none else
        some (problemJson "occurrenceField" [("event", .str ev.name), ("field", .str a.1)]
          s!"the value of {a.1} of the occurrence of {ev.name} is not of type {a.2.text}")) ++
  ((occ.refs.map (·.1) ++ occ.attrs.map (·.1)).filter fun f =>
    !(ev.refs.map (·.1) ++ ev.attrs.map (·.1)).contains f).map (fun f =>
      problemJson "occurrenceField" [("event", .str ev.name), ("field", .str f)]
        s!"{f} is not a field of the event type {ev.name}") ++
  (occ.attrs.filterMap fun a => match c.valueTypes.normalize a.2.1 a.2.2 with
    | .ok l => if l == a.2.2 then none else
        some (problemJson "literal" [("event", .str ev.name), ("field", .str a.1)]
          s!"{Lit.render a.2.2} is not in normal form; it is written {l.render}")
    | .error e => some (problemJson "literal" [("event", .str ev.name), ("field", .str a.1)]
        s!"{a.1}: {e}"))

/-- The problems that explain a failing claim. -/
def explain : Claim → List Json
  | .wellFormed s => c.schemaProblems s
  | .acyclic s => match c.schema? s with
    | some S => c.schemaProblems s ++
      if S.checkAcyclic then [] else match S.longPath? with
        | some (e, l) => [problemJson "cycle" [("schema", .str s), ("entity", .str e),
            ("path", Lean.toJson l)]
            s!"the path {pathText l} out of {e} has more generators than {s} has entity types, \
              so it runs through a cycle"]
        | none => [problemJson "cycle" [("schema", .str s)] s!"{s} has a cycle"]
    | none => [unknown "schema" s]
  | .translation s t T => match c.schema? s, c.schema? t with
    | some S, some S' =>
      c.schemaProblems t ++ (T.vproblems c.valueTypes S S' (S'.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson s t)
    | _, _ => (if (c.schema? s).isNone then [unknown "schema" s] else []) ++
      (if (c.schema? t).isNone then [unknown "schema" t] else [])
  | .keysKept s t T => match c.schema? s, c.schema? t with
    | some S, some S' => (T.keysNotKept S S').map fun k => problemJson "keyNotKept"
        [("entity", .str k.entity), ("key", Lean.toJson k.fields), ("image", .str (T.ent k.entity))]
        s!"the key {keyText k.fields} of {k.entity} in {s} is not kept in {t}: no field goes to \
          the empty path, and {T.ent k.entity} has no key whose fields are images of its fields"
    | _, _ => (if (c.schema? s).isNone then [unknown "schema" s] else []) ++
      (if (c.schema? t).isNone then [unknown "schema" t] else [])
  | .gluing k l r g ff => match c.schema? k, c.schema? l, c.schema? r, c.schema? g with
    | some K, some L, some R, some G =>
      let glued := Schema.glue L R
      c.schemaProblems k ++ c.schemaProblems l ++ c.schemaProblems r ++ c.schemaProblems g ++
        glued.problems.map (Schema.Problem.toJson s!"{l} + {r}") ++
        inclusionProblems k l K L ++ inclusionProblems k r K R ++
        (Schema.gluingClashes K L R).map (fun n => problemJson "clash"
          [("name", .str n), ("left", .str l), ("right", .str r), ("kernel", .str k)]
          s!"{l} and {r} both have {n}, which is not in the kernel {k}") ++
        failing [(glued.checkSameUpToOrder G, "gluedDiffers",
          s!"{g} does not list the same entity types, generators, equations, aggregates, \
            value objects, keys and subtypes as the gluing of {l} and {r}")] ++
        inclusionProblems l g L G ++ inclusionProblems r g R G ++
        match ff with
        | none => []
        | some (b₁, b₂) => failing [
            (L.checkAcyclic, "notAcyclic", s!"{l} is not acyclic"),
            (R.checkAcyclic, "notAcyclic", s!"{r} is not acyclic"),
            (G.checkAcyclic, "notAcyclic", s!"{g} is not acyclic"),
            (({} : Translation).checkFullyFaithful L G == b₁, "fullyFaithful",
              s!"the strict non-interference check of {l} gives {!b₁}, not {b₁}"),
            (({} : Translation).checkFullyFaithful R G == b₂, "fullyFaithful",
              s!"the strict non-interference check of {r} gives {!b₂}, not {b₂}")]
    | _, _, _, _ => [k, l, r, g].filterMap fun n =>
      if (c.schema? n).isNone then some (unknown "schema" n) else none
  | .state x => match c.state? x with
    | some (s, X) => match c.schema? s with
      | some S => c.schemaProblems s ++ failing [
          (X.check S, "stateCheck", s!"{x} does not pass the check of {s}")] ++
          (if X.check S then (X.keyViolations S).map fun (k, i, j) => problemJson "key"
            [("state", .str x), ("entity", .str k.entity), ("key", Lean.toJson k.fields),
              ("entities", Lean.toJson [i, j])]
            s!"the entities {i} and {j} of {k.entity} in {x} agree on the key \
              {keyText k.fields}"
          else []) ++
          (X.litProblems c.valueTypes).map (LitProblem.toJson x)
      | none => [unknown "schema" s]
    | none => [unknown "state" x]
  | .valueTypes => c.valueTypes.problems.map TypeList.Problem.toJson
  | .declared s => match c.schema? s with
    | some S => (S.typeProblems c.valueTypes).map (Schema.TypeProblem.toJson s)
    | none => [unknown "schema" s]
  | .restriction s t T x y => match c.schema? s, c.schema? t, c.state? x, c.state? y with
    | some S, some S', some (sx, X), some (sy, Y) =>
      failing [(sx == t, "stateSchema", s!"{x} is a state of {sx}, not of {t}"),
        (sy == s, "stateSchema", s!"{y} is a state of {sy}, not of {s}")] ++
      c.schemaProblems s ++ c.schemaProblems t ++
      (T.vproblems c.valueTypes S S' (S'.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson s t) ++
      failing [(X.check S', "stateCheck", s!"{x} does not pass the check of {t}"),
        (c.valueTypes.checkSound, "valueTypesUnsound", "the list of value types is not sound"),
        (X.litsFit c.valueTypes, "literals",
          s!"the literals of {x} are not values of their types in normal form"),
        (decide (Y = X.vrestrictLit c.valueTypes T S S'), "restriction",
          s!"{y} is not the restriction of {x} along {s} → {t}")]
    | _, _, _, _ => (if (c.schema? s).isNone then [unknown "schema" s] else []) ++
      (if (c.schema? t).isNone then [unknown "schema" t] else []) ++
      (if (c.state? x).isNone then [unknown "state" x] else []) ++
      (if (c.state? y).isNone then [unknown "state" y] else [])
  | .agreement p l r T₁ T₂ x y =>
    match c.schema? p, c.schema? l, c.schema? r, c.state? x, c.state? y with
    | some P, some S₁, some S₂, some (sx, X), some (sy, Y) =>
      let A := X.vrestrictLit c.valueTypes T₁ P S₁
      let B := Y.vrestrictLit c.valueTypes T₂ P S₂
      failing [(sx == l, "stateSchema", s!"{x} is a state of {sx}, not of {l}"),
        (sy == r, "stateSchema", s!"{y} is a state of {sy}, not of {r}")] ++
      c.schemaProblems p ++ c.schemaProblems l ++ c.schemaProblems r ++
      (T₁.vproblems c.valueTypes P S₁ (S₁.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson p l) ++
      (T₂.vproblems c.valueTypes P S₂ (S₂.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson p r) ++
      failing [(X.check S₁, "stateCheck", s!"{x} does not pass the check of {l}"),
        (Y.check S₂, "stateCheck", s!"{y} does not pass the check of {r}"),
        (c.valueTypes.checkSound, "valueTypesUnsound", "the list of value types is not sound"),
        (X.litsFit c.valueTypes, "literals",
          s!"the literals of {x} are not values of their types in normal form"),
        (Y.litsFit c.valueTypes, "literals",
          s!"the literals of {y} are not values of their types in normal form")] ++
      (P.entities.filter fun e => A.size e != B.size e).map (fun e =>
        problemJson "disagree" [("shared", .str p), ("entity", .str e)]
          s!"{x} gives {p} {A.size e} entities of {e} and {y} gives it {B.size e}") ++
      (P.refs.filter fun g => A.refCol g.src g.name != B.refCol g.src g.name).map (fun g =>
        problemJson "disagree" [("shared", .str p), ("generator", .str s!"{g.src}.{g.name}")]
          s!"{x} and {y} give {p} different values of {g.src}.{g.name}") ++
      (P.attrs.filter fun g => A.attrCol g.src g.name != B.attrCol g.src g.name).map (fun g =>
        problemJson "disagree" [("shared", .str p), ("generator", .str s!"{g.src}.{g.name}")]
          s!"{x} and {y} give {p} different values of {g.src}.{g.name}")
    | _, _, _, _, _ => ([p, l, r].filterMap fun n =>
        if (c.schema? n).isNone then some (unknown "schema" n) else none) ++
      ([x, y].filterMap fun n => if (c.state? n).isNone then some (unknown "state" n) else none)
  | .conformance p l r T₁ T₂ x y h =>
    match c.schema? p, c.schema? l, c.schema? r, c.state? x, c.state? y with
    | some P, some S₁, some S₂, some (sx, X), some (sy, Y) =>
      failing [(sx == l, "stateSchema", s!"{x} is a state of {sx}, not of {l}"),
        (sy == r, "stateSchema", s!"{y} is a state of {sy}, not of {r}")] ++
      c.schemaProblems p ++ c.schemaProblems l ++ c.schemaProblems r ++
      (T₁.vproblems c.valueTypes P S₁ (S₁.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson p l) ++
      (T₂.vproblems c.valueTypes P S₂ (S₂.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson p r) ++
      failing [(X.check S₁, "stateCheck", s!"{x} does not pass the check of {l}"),
        (Y.check S₂, "stateCheck", s!"{y} does not pass the check of {r}"),
        (c.valueTypes.checkSound, "valueTypesUnsound", "the list of value types is not sound"),
        (X.litsFit c.valueTypes, "literals",
          s!"the literals of {x} are not values of their types in normal form"),
        (Y.litsFit c.valueTypes, "literals",
          s!"the literals of {y} are not values of their types in normal form"),
        (h.check P (Y.vrestrictLit c.valueTypes T₂ P S₂) (X.vrestrictLit c.valueTypes T₁ P S₁),
          "homomorphism", s!"the components do not form a homomorphism from the restriction \
            of {y} to the restriction of {x} on {p}")]
    | _, _, _, _, _ => ([p, l, r].filterMap fun n =>
        if (c.schema? n).isNone then some (unknown "schema" n) else none) ++
      ([x, y].filterMap fun n => if (c.state? n).isNone then some (unknown "state" n) else none)
  | .normalForm s t T => match c.schema? s, c.schema? t with
    | some S, some S' =>
      c.schemaProblems s ++ c.schemaProblems t ++
      (T.problems S S' S'.pathEq).map (Translation.Problem.toJson s t) ++
      (S.entities.filter fun e => (S.entities.filter fun e' => T.ent e' == T.ent e).length > 1).map
        (fun e => problemJson "entitiesMerged" [("entity", .str e), ("image", .str (T.ent e))]
          s!"{e} and another entity type of {s} both go to {T.ent e} in {t}") ++
      (T.ext S S').problems.map (Schema.Problem.toJson s!"the extension of {t} along {s} → {t}")
    | _, _ => (if (c.schema? s).isNone then [unknown "schema" s] else []) ++
      (if (c.schema? t).isNone then [unknown "schema" t] else [])
  | .eventType s ev => match c.schema? s with
    | some P => c.schemaProblems s ++ c.eventProblems s P ev
    | none => [unknown "schema" s]
  | .occurrence p s T ev x occ => match c.schema? p, c.schema? s, c.state? x with
    | some P, some S, some (sx, X) =>
      failing [(sx == s, "stateSchema", s!"{x} is a state of {sx}, not of {s}")] ++
      c.schemaProblems p ++ c.schemaProblems s ++
      (T.vproblems c.valueTypes P S (S.pathEqV c.valueTypes)).map
        (Translation.Problem.toJson p s) ++
      failing [(X.check S, "stateCheck", s!"{x} does not pass the check of {s}"),
        (c.valueTypes.checkSound, "valueTypesUnsound", "the list of value types is not sound"),
        (X.litsFit c.valueTypes, "literals",
          s!"the literals of {x} are not values of their types in normal form")] ++
      c.eventProblems p P ev ++
      c.occurrenceProblems ev (X.vrestrictLit c.valueTypes T P S) occ
    | _, _, _ => ([p, s].filterMap fun n =>
        if (c.schema? n).isNone then some (unknown "schema" n) else none) ++
      (if (c.state? x).isNone then [unknown "state" x] else [])
  | .homomorphism x y h => match c.state? x, c.state? y with
    | some (sx, X), some (sy, Y) =>
      failing [(sx == sy, "stateSchema", s!"{x} is a state of {sx} and {y} a state of {sy}")] ++
      match c.schema? sx with
      | some S => c.schemaProblems sx ++ failing [
          (X.check S, "stateCheck", s!"{x} does not pass the check of {sx}"),
          (Y.check S, "stateCheck", s!"{y} does not pass the check of {sx}"),
          (h.check S X Y, "homomorphism", s!"the components do not form a homomorphism {x} → {y}")]
      | none => [unknown "schema" sx]
    | _, _ => (if (c.state? x).isNone then [unknown "state" x] else []) ++
      (if (c.state? y).isNone then [unknown "state" y] else [])
  | .pathEquality s o l r => match c.schema? s with
    | some S =>
      let L := c.valueTypes
      c.schemaProblems s ++ failing [
        (decide (S.IsOb o), "unknownObject", s!"{o.text} is not an object of {s}"),
        ((S.vtgt? L o l).isSome, "noPath", s!"there is no path {pathText l} out of {o.text}"),
        ((S.vtgt? L o r).isSome, "noPath", s!"there is no path {pathText r} out of {o.text}"),
        (S.vtgt? L o l == S.vtgt? L o r, "notParallel",
          s!"the paths {pathText l} and {pathText r} out of {o.text} end at different objects"),
        (S.pathEqV L o l r, "pathsDiffer",
          s!"the paths {pathText l} and {pathText r} out of {o.text} have different normal forms")]
    | none => [unknown "schema" s]
  | .conversion v l x y =>
    let L := c.valueTypes
    failing [((L.convTgt? v l).isSome, "noConversion",
        s!"there is no path of conversions {pathText l} out of {v.text}"),
      ((L.normalize v x).toOption == some x, "notNormal",
        s!"{x.render} is not a value of {v.text} in normal form")] ++
    match L.applyLit v l x with
    | .ok z => failing [(z == y, "conversionResult",
        s!"{pathText l} sends {x.render} to {z.render}, not to {y.render}")]
    | .error e => [problemJson "conversionFails" [] e]

/-- Whether a claim holds, and its problems when it fails: those of `explain`, or
the failure of its check when `explain` finds none. -/
def result (cl : Claim) : Bool × List Json :=
  if c.checkClaim cl then (true, [])
  else match c.explain cl with
    | [] => (false, [problemJson "check" [] s!"the check of the claim fails: {cl.describe}"])
    | ps => (false, ps)

/-- The report of a certificate. -/
def report : Json :=
  let rs := c.claims.map fun cl => (cl, c.result cl)
  let claims := rs.map fun (cl, ok, ps) => Json.mkObj (cl.refFields ++
    [("description", .str cl.describe), ("ok", .bool ok), ("problems", Json.arr ps.toArray)])
  Json.mkObj [("format", .str formatVersion), ("kind", .str "report"),
    ("producer", .str c.producer), ("claims", Json.arr claims.toArray),
    ("failed", ((rs.filter fun r => !r.2.1).length : Nat))]

end Certificate

/-! ## Context map documents -/

namespace MapDoc

variable (M : MapDoc)

/-- The schema of the context named `n`, if there is one. -/
def schema? (n : String) : Option Schema := (M.contexts.lookup n).map (·.1)

/-- The certificate of a context map document: its list of value types, its
contexts as schemas, and the claims that the list is sound, that each context is
well formed and declares its value types, that each arrow is a valid translation
and keeps keys, and that each event type is one over its context: the list first,
then the contexts, the arrows and the event types, in their order. -/
def certificate : Certificate where
  producer := "map"
  valueTypes := M.valueTypes
  schemas := M.contexts.map fun ctx => (ctx.1, ctx.2.1)
  states := []
  claims := [.valueTypes] ++ M.contexts.flatMap (fun ctx => [.wellFormed ctx.1, .declared ctx.1]) ++
    M.arrows.flatMap (fun a =>
      [.translation a.2.1 a.2.2.1 a.2.2.2, .keysKept a.2.1 a.2.2.1 a.2.2.2]) ++
    M.events.map fun e => .eventType e.1 e.2

/-- A context map document, read from JSON with its format and kind checked. -/
def ofJson (j : Json) : Except String MapDoc := do
  let fmt ← j.getObjValAs? String "format"
  unless readableFormats.contains fmt do throw s!"unsupported format {fmt}"
  let kind ← j.getObjValAs? String "kind"
  unless kind == "map" do throw s!"expected a map, found {kind}"
  MapDoc.fromJson j

end MapDoc

end DDD
