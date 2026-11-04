import DDD.Translation
import DDD.Literals
import Mathlib.Data.List.Dedup

/-!
# Problems

The checks of well-formedness and of translations answer with a `Bool`. The
problem lists give their failures one by one, with the names they concern, for
reports and editors.

- `Schema.problems S`: the failures of the conditions of `Schema.WellFormed`, one
  per entity type, generator, equation, aggregate or value object at fault, in
  the order of the conditions. There are none exactly when the check passes
  (`Schema.problems_eq_nil_iff`), so exactly when `S` is well formed
  (`Schema.problems_eq_nil_iff_wellFormed`).
- `Translation.problems T S S' peq`: the failures of the conditions of
  `Translation.Valid`, with `peq` deciding path equality in `S'`. There are none
  exactly when `checkValid` passes (`Translation.problems_eq_nil_iff`).
- `Schema.typeProblems L S`: the attributes of `S` whose value types the list of
  value types `L` does not admit, an undeclared name or an optional of an
  optional; none exactly when `L` admits every value type of `S`
  (`Schema.typeProblems_eq_nil_iff`).
- `describe` states a problem as a sentence and `kind` names its condition;
  `DDD.Report` gives problems as JSON.
-/

namespace DDD

/-! ## Text -/

/-- A path as text: its names joined by dots, `id` for the empty path. -/
def pathText : List String → String
  | [] => "id"
  | ns => ".".intercalate ns

def Ob.text : Ob → String
  | .entity e => e
  | .value v => v.text

def Equation.text (q : Equation) : String := s!"{q.src}: {pathText q.lhs} = {pathText q.rhs}"

/-- The fields of a key as text: `{a, b}`. -/
def keyText (fs : List String) : String := "{" ++ ", ".intercalate fs ++ "}"

/-- Where a path ends, as text. -/
def endText : Option Ob → String
  | some o => s!"ends at {o.text}"
  | none => "is not a path"

/-! ## Schemas -/

namespace Schema

/-- A failure of a condition of `WellFormed`, with the names it concerns. -/
inductive Problem where
  /-- The entity type `e` is declared more than once. -/
  | duplicateEntity (e : String)
  /-- Two generators out of the entity type `e` are named `n`. -/
  | duplicateGenerator (e n : String)
  /-- The source of the reference `r` is not a declared entity type. -/
  | refSource (r : Ref)
  /-- The target of the reference `r` is not a declared entity type. -/
  | refTarget (r : Ref)
  /-- The source of the attribute `a` is not a declared entity type. -/
  | attrSource (a : Attr)
  /-- The source of the equation `q` is not a declared entity type. -/
  | eqnSource (q : Equation)
  /-- The sides of the equation `q` end at `lhs` and `rhs`, which are not the same
  object (`none`: the side is not a path). -/
  | eqnNotParallel (q : Equation) (lhs rhs : Option Ob)
  /-- The aggregate with root `root` lists `e`, which is not a declared entity type. -/
  | aggregateEntity (root e : String)
  /-- The entity type `e` belongs to two aggregates, or twice to one. -/
  | aggregateOverlap (e : String)
  /-- The member `m` of the aggregate with root `root` has no ownership reference
  to an entity type of the aggregate. -/
  | missingOwner (root : String) (m : Member)
  /-- Following the ownership references from the member `m` of the aggregate with
  root `root` does not reach the root. -/
  | ownerCycle (root : String) (m : Member)
  /-- The reference `r` targets a member of the aggregate with root `root` from
  outside the aggregate. -/
  | boundary (r : Ref) (root : String)
  /-- The value object `e` is not a declared entity type. -/
  | valueObjectEntity (e : String)
  /-- The value object `e` has no field. -/
  | valueObjectFields (e : String)
  /-- The key `k` is on an entity type that is not declared. -/
  | keyEntity (k : Key)
  /-- A key of the entity type `e` has no field. -/
  | keyEmpty (e : String)
  /-- The key `k` names `n`, which is not a generator out of its entity type. -/
  | keyField (k : Key) (n : String)
  /-- The subtype `e` is not a declared entity type. -/
  | subtypeEntity (e : String)
  /-- The subtype `s` has no is-a reference of its name. -/
  | subtypeRef (s : IsA)
deriving DecidableEq, Repr

variable (S : Schema)

/-- Entity types declared more than once. -/
def entityProblems : List Problem := (dups S.entities).map .duplicateEntity

/-- Generator names used twice out of one entity type. -/
def generatorProblems : List Problem :=
  S.entities.dedup.flatMap fun e => (dups (S.outNames e)).map (.duplicateGenerator e)

/-- References between undeclared entity types. -/
def refProblems : List Problem :=
  S.refs.flatMap fun r =>
    (if r.src ∈ S.entities then [] else [.refSource r]) ++
      (if r.tgt ∈ S.entities then [] else [.refTarget r])

/-- Attributes out of undeclared entity types. -/
def attrProblems : List Problem :=
  S.attrs.filterMap fun a => if a.src ∈ S.entities then none else some (.attrSource a)

/-- Equations out of undeclared entity types, or between paths that are not
parallel. -/
def eqnProblems : List Problem :=
  S.eqns.filterMap fun q =>
    if q.src ∈ S.entities then
      if S.parallel q then none
      else some (.eqnNotParallel q (S.tgt? (.entity q.src) q.lhs) (S.tgt? (.entity q.src) q.rhs))
    else some (.eqnSource q)

/-- Entity types of aggregates that are not declared. -/
def aggregateProblems : List Problem :=
  S.aggregates.flatMap fun A =>
    (A.entities.filter fun e => e ∉ S.entities).map (.aggregateEntity A.root)

/-- Entity types in two aggregates, or twice in one. -/
def overlapProblems : List Problem :=
  (dups (S.aggregates.flatMap Aggregate.entities)).map .aggregateOverlap

/-- Members without an ownership reference to an entity type of their aggregate,
and members from which the ownership references do not reach the root. -/
def ownerProblems : List Problem :=
  S.aggregates.flatMap fun A => A.members.filterMap fun m =>
    if A.entities.any fun t => decide ((⟨m.owner, m.entity, t⟩ : Ref) ∈ S.refs) then
      if S.ownerIter A A.members.length m.entity = some A.root then none
      else some (.ownerCycle A.root m)
    else some (.missingOwner A.root m)

/-- References from outside an aggregate to a member of it. -/
def boundaryProblems : List Problem :=
  S.refs.flatMap fun r =>
    (S.aggregates.filter fun A =>
      r.tgt ∈ A.members.map (·.entity) ∧ r.src ∉ A.entities).map fun A => .boundary r A.root

/-- Value objects that are not declared, or have no field. -/
def valueObjectProblems : List Problem :=
  S.valueObjects.filterMap fun e =>
    if e ∈ S.entities then
      if S.outNames e ≠ [] then none else some (.valueObjectFields e)
    else some (.valueObjectEntity e)

/-- Keys on undeclared entity types, keys without fields, and fields of keys that
are not generators out of their entity type. -/
def keyProblems : List Problem :=
  S.keys.flatMap fun k =>
    if k.entity ∈ S.entities then
      if k.fields = [] then [.keyEmpty k.entity]
      else (k.fields.filter fun n => n ∉ S.outNames k.entity).map (.keyField k)
    else [.keyEntity k]

/-- Subtypes that are not declared, or have no is-a reference of their name. -/
def subtypeProblems : List Problem :=
  S.subtypes.filterMap fun s =>
    if s.entity ∈ S.entities then
      if S.refs.any fun r => r.src == s.entity && r.name == s.ref then none
      else some (.subtypeRef s)
    else some (.subtypeEntity s.entity)

/-- The failures of the conditions of `WellFormed`, in their order. -/
def problems : List Problem :=
  S.entityProblems ++ S.generatorProblems ++ S.refProblems ++ S.attrProblems ++
    S.eqnProblems ++ S.aggregateProblems ++ S.overlapProblems ++ S.ownerProblems ++
    S.boundaryProblems ++ S.valueObjectProblems ++ S.keyProblems ++ S.subtypeProblems

theorem entityProblems_eq_nil : S.entityProblems = [] ↔ decide S.entities.Nodup = true := by
  simp [entityProblems, dups_eq_nil_iff]

theorem generatorProblems_eq_nil : S.generatorProblems = [] ↔
    (S.entities.all fun e => decide (S.outNames e).Nodup) = true := by
  simp [generatorProblems, dups_eq_nil_iff, List.mem_dedup]

theorem refProblems_eq_nil : S.refProblems = [] ↔
    (S.refs.all fun r => decide (r.src ∈ S.entities) && decide (r.tgt ∈ S.entities)) = true := by
  simp only [refProblems, List.flatMap_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun r _ => ?_
  by_cases hs : r.src ∈ S.entities <;> by_cases ht : r.tgt ∈ S.entities <;> simp [hs, ht]

theorem attrProblems_eq_nil : S.attrProblems = [] ↔
    (S.attrs.all fun a => decide (a.src ∈ S.entities)) = true := by
  simp only [attrProblems, List.filterMap_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun a _ => ?_
  by_cases hs : a.src ∈ S.entities <;> simp [hs]

theorem eqnProblems_eq_nil : S.eqnProblems = [] ↔
    (S.eqns.all fun q => decide (q.src ∈ S.entities) && S.parallel q) = true := by
  simp only [eqnProblems, List.filterMap_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun q _ => ?_
  by_cases hs : q.src ∈ S.entities <;> by_cases hp : S.parallel q = true <;> simp [hs, hp]

theorem aggregateProblems_eq_nil : S.aggregateProblems = [] ↔
    (S.aggregates.all fun A => A.entities.all fun e => decide (e ∈ S.entities)) = true := by
  simp [aggregateProblems]

theorem overlapProblems_eq_nil : S.overlapProblems = [] ↔
    decide (S.aggregates.flatMap Aggregate.entities).Nodup = true := by
  simp [overlapProblems, dups_eq_nil_iff]

theorem ownerProblems_eq_nil : S.ownerProblems = [] ↔
    (S.aggregates.all fun A => A.members.all fun m =>
      (A.entities.any fun t => decide ((⟨m.owner, m.entity, t⟩ : Ref) ∈ S.refs)) &&
        decide (S.ownerIter A A.members.length m.entity = some A.root)) = true := by
  simp only [ownerProblems, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff,
    List.all_eq_true, Bool.and_eq_true]
  refine forall₂_congr fun A _ => forall₂_congr fun m _ => ?_
  by_cases ho : (A.entities.any fun t => decide ((⟨m.owner, m.entity, t⟩ : Ref) ∈ S.refs)) = true
    <;> by_cases ht : S.ownerIter A A.members.length m.entity = some A.root <;>
    simp only [ho, ht, if_true, if_false] <;> simp_all

theorem boundaryProblems_eq_nil : S.boundaryProblems = [] ↔
    (S.refs.all fun r => S.aggregates.all fun A =>
      !decide (r.tgt ∈ A.members.map (·.entity)) || decide (r.src ∈ A.entities)) = true := by
  simp only [boundaryProblems, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun r _ => forall₂_congr fun A _ => ?_
  by_cases hm : r.tgt ∈ A.members.map (·.entity) <;>
    by_cases hs : r.src ∈ A.entities <;> simp only [hm, hs] <;> simp

theorem valueObjectProblems_eq_nil : S.valueObjectProblems = [] ↔
    (S.valueObjects.all fun e => decide (e ∈ S.entities) && decide (S.outNames e ≠ [])) =
      true := by
  simp only [valueObjectProblems, List.filterMap_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun e _ => ?_
  by_cases hs : e ∈ S.entities <;> by_cases ha : S.outNames e ≠ [] <;>
    simp only [hs, ha, if_true, if_false] <;> simp_all

theorem keyProblems_eq_nil : S.keyProblems = [] ↔
    (S.keys.all fun k => decide (k.entity ∈ S.entities) &&
      (decide (k.fields ≠ []) && k.fields.all fun n => decide (n ∈ S.outNames k.entity))) =
      true := by
  simp only [keyProblems, List.flatMap_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun k _ => ?_
  by_cases hs : k.entity ∈ S.entities <;> by_cases hf : k.fields = [] <;>
    simp [hs, hf, List.filter_eq_nil_iff]

theorem subtypeProblems_eq_nil : S.subtypeProblems = [] ↔
    (S.subtypes.all fun s => decide (s.entity ∈ S.entities) &&
      S.refs.any fun r => r.src == s.entity && r.name == s.ref) = true := by
  simp only [subtypeProblems, List.filterMap_eq_nil_iff, List.all_eq_true]
  refine forall₂_congr fun s _ => ?_
  by_cases hs : s.entity ∈ S.entities <;>
    by_cases hr : (S.refs.any fun r => r.src == s.entity && r.name == s.ref) = true <;>
    simp only [hs, hr, if_true, if_false] <;> simp_all

/-- A schema has no problem exactly when it passes the well-formedness check. -/
theorem problems_eq_nil_iff : S.problems = [] ↔ S.checkWellFormed = true := by
  simp only [problems, checkWellFormed, List.append_eq_nil_iff, Bool.and_eq_true,
    entityProblems_eq_nil, generatorProblems_eq_nil, refProblems_eq_nil, attrProblems_eq_nil,
    eqnProblems_eq_nil, aggregateProblems_eq_nil, overlapProblems_eq_nil, ownerProblems_eq_nil,
    boundaryProblems_eq_nil, valueObjectProblems_eq_nil, keyProblems_eq_nil,
    subtypeProblems_eq_nil, and_assoc]

theorem problems_eq_nil_iff_wellFormed : S.problems = [] ↔ S.WellFormed :=
  S.problems_eq_nil_iff.trans S.checkWellFormed_iff

namespace Problem

/-- A problem as a sentence. -/
def describe : Problem → String
  | .duplicateEntity e => s!"the entity type {e} is declared more than once"
  | .duplicateGenerator e n => s!"two generators out of {e} are named {n}"
  | .refSource r =>
    s!"the reference {r.src}.{r.name} starts at {r.src}, which is not a declared entity type"
  | .refTarget r =>
    s!"the reference {r.src}.{r.name} targets {r.tgt}, which is not a declared entity type"
  | .attrSource a =>
    s!"the attribute {a.src}.{a.name} starts at {a.src}, which is not a declared entity type"
  | .eqnSource q =>
    s!"the equation {q.text} starts at {q.src}, which is not a declared entity type"
  | .eqnNotParallel q l r =>
    s!"the sides of the equation {q.text} do not end at the same object: the left side \
      {endText l}, the right side {endText r}"
  | .aggregateEntity root e =>
    s!"the aggregate of {root} lists {e}, which is not a declared entity type"
  | .aggregateOverlap e => s!"{e} belongs to two aggregates, or twice to one"
  | .missingOwner root m =>
    s!"the member {m.entity} of the aggregate of {root} has no reference \
      {m.entity}.{m.owner} to {root} or to another member of the aggregate"
  | .ownerCycle root m =>
    s!"following the ownership references from {m.entity} does not reach {root}, the root \
      of its aggregate"
  | .boundary r root =>
    s!"the reference {r.src}.{r.name} targets {r.tgt}, a member of the aggregate of {root}, \
      from outside it; references from outside an aggregate target its root"
  | .valueObjectEntity e => s!"the value object {e} is not a declared entity type"
  | .valueObjectFields e => s!"the value object {e} has no field"
  | .keyEntity k => s!"a key is declared on {k.entity}, which is not a declared entity type"
  | .keyEmpty e => s!"a key of {e} has no field"
  | .keyField k n =>
    s!"the key {keyText k.fields} of {k.entity} names {n}, which is not a reference or an \
      attribute of {k.entity}"
  | .subtypeEntity e => s!"the subtype {e} is not a declared entity type"
  | .subtypeRef s =>
    s!"the subtype {s.entity} has no reference {s.entity}.{s.ref} to its supertype"

def kind : Problem → String
  | .duplicateEntity .. => "duplicateEntity"
  | .duplicateGenerator .. => "duplicateGenerator"
  | .refSource .. => "referenceSource"
  | .refTarget .. => "referenceTarget"
  | .attrSource .. => "attributeSource"
  | .eqnSource .. => "equationSource"
  | .eqnNotParallel .. => "equationNotParallel"
  | .aggregateEntity .. => "aggregateEntity"
  | .aggregateOverlap .. => "aggregateOverlap"
  | .missingOwner .. => "missingOwner"
  | .ownerCycle .. => "ownerCycle"
  | .boundary .. => "aggregateBoundary"
  | .valueObjectEntity .. => "valueObjectEntity"
  | .valueObjectFields .. => "valueObjectFields"
  | .keyEntity .. => "keyEntity"
  | .keyEmpty .. => "keyEmpty"
  | .keyField .. => "keyField"
  | .subtypeEntity .. => "subtypeEntity"
  | .subtypeRef .. => "subtypeReference"

end Problem

end Schema

/-! ## Translations -/

namespace Translation

/-- A failure of a condition of `Valid`, with the names it concerns. -/
inductive Problem where
  /-- The entity type `e` goes to `image`, which is not an entity type of the target. -/
  | entity (e image : String)
  /-- The reference `r` goes to `path`, which ends at `ends` in the target instead
  of at `expected`, the image of the target of `r` (`none`: not a path). -/
  | ref (r : Ref) (path : List String) (expected : Ob) (ends : Option Ob)
  /-- The attribute `a` goes to `path`, which ends at `ends` instead of at its
  value type. -/
  | attr (a : Attr) (path : List String) (ends : Option Ob)
  /-- The source of the equation `q` goes to `image`, which is not an entity type of
  the target. -/
  | eqnSource (q : Equation) (image : String)
  /-- The equation `q` goes to `lhs = rhs`, which path equality in the target does
  not show. -/
  | eqn (q : Equation) (lhs rhs : List String)
deriving DecidableEq, Repr

variable (T : Translation) (S S' : Schema) (peq : Ob → List String → List String → Bool)

/-- The failures of the conditions of `Valid`, in their order. -/
def problems : List Problem :=
  (S.entities.filterMap fun e =>
    if T.ent e ∈ S'.entities then none else some (.entity e (T.ent e))) ++
  (S.refs.filterMap fun r =>
    if S'.tgt? (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name) =
        some (T.ob (.entity r.tgt)) then none
    else some (.ref r (T.gen (.entity r.src) r.name) (T.ob (.entity r.tgt))
      (S'.tgt? (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name)))) ++
  (S.attrs.filterMap fun a =>
    if S'.tgt? (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name) = some (.value a.tgt) then
      none
    else some (.attr a (T.gen (.entity a.src) a.name)
      (S'.tgt? (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name)))) ++
  (S.eqns.filterMap fun q =>
    if T.ent q.src ∈ S'.entities then
      if peq (.entity (T.ent q.src)) (T.mapPath S (.entity q.src) q.lhs)
          (T.mapPath S (.entity q.src) q.rhs) then none
      else some (.eqn q (T.mapPath S (.entity q.src) q.lhs) (T.mapPath S (.entity q.src) q.rhs))
    else some (.eqnSource q (T.ent q.src)))

/-- A translation has no problem exactly when it passes the validity check. -/
theorem problems_eq_nil_iff : T.problems S S' peq = [] ↔ T.checkValid S S' peq = true := by
  simp only [problems, checkValid, List.append_eq_nil_iff, Bool.and_eq_true, List.all_eq_true,
    List.filterMap_eq_nil_iff, decide_eq_true_eq]
  refine and_congr (and_congr (and_congr ?_ ?_) ?_) ?_
  · refine forall₂_congr fun e _ => ?_
    by_cases h : T.ent e ∈ S'.entities <;> simp [h]
  · refine forall₂_congr fun r _ => ?_
    split <;> simp_all
  · refine forall₂_congr fun a _ => ?_
    split <;> simp_all
  · refine forall₂_congr fun q _ => ?_
    by_cases hs : T.ent q.src ∈ S'.entities <;>
      by_cases hp : peq (.entity (T.ent q.src)) (T.mapPath S (.entity q.src) q.lhs)
        (T.mapPath S (.entity q.src) q.rhs) = true <;> simp [hs, hp]

namespace Problem

/-- The image of a generator that does not end where it should, as a sentence. -/
def imageText (gen : String) (path : List String) (expected : Ob) : Option Ob → String
  | some o => s!"{gen} goes to the path {pathText path}, which ends at {o.text} instead of at \
      {expected.text}"
  | none => s!"{gen} goes to {pathText path}, which is not a path of the target; it should end \
      at {expected.text}"

/-- A problem as a sentence. -/
def describe : Problem → String
  | .entity e image => s!"{e} goes to {image}, which is not an entity type of the target"
  | .ref r path expected ends =>
    imageText s!"the reference {r.src}.{r.name}" path expected ends
  | .attr a path ends => imageText s!"the attribute {a.src}.{a.name}" path (.value a.tgt) ends
  | .eqnSource q image =>
    s!"the source of the equation {q.text} goes to {image}, which is not an entity type of \
      the target"
  | .eqn q l r =>
    s!"the equation {q.text} goes to {pathText l} = {pathText r}, which path equality in the \
      target does not show"

def kind : Problem → String
  | .entity .. => "entityImage"
  | .ref .. => "referenceImage"
  | .attr .. => "attributeImage"
  | .eqnSource .. => "equationSourceImage"
  | .eqn .. => "equationImage"

end Problem

end Translation

/-! ## Value types of attributes -/

namespace Schema

/-- An attribute whose value type the list of value types does not admit. -/
inductive TypeProblem where
  /-- The value type of the attribute `a` names `n`, which the list does not
  declare. -/
  | undeclared (a : Attr) (n : String)
  /-- The value type of the attribute `a` is optional twice. -/
  | nestedOptional (a : Attr)
deriving DecidableEq, Repr

variable (L : TypeList) (S : Schema)

/-- The attributes of `S` whose value types `L` does not admit, in their order. -/
def typeProblems : List TypeProblem :=
  S.attrs.flatMap fun a =>
    (match L.undeclared? a.tgt with
      | some n => [.undeclared a n]
      | none => []) ++
    (if a.tgt.nested then [.nestedOptional a] else [])

theorem typeProblems_eq_nil_iff :
    S.typeProblems L = [] ↔ ∀ a ∈ S.attrs, L.admits a.tgt = true := by
  simp only [typeProblems, List.flatMap_eq_nil_iff, List.append_eq_nil_iff]
  refine forall₂_congr fun a _ => ?_
  rw [L.admits_iff]
  cases h₁ : L.undeclared? a.tgt <;> cases h₂ : a.tgt.nested <;> simp

namespace TypeProblem

def describe : TypeProblem → String
  | .undeclared a n =>
    s!"the attribute {a.src}.{a.name} has the value type {a.tgt.text}, and {n} is not \
      declared in the list of value types"
  | .nestedOptional a =>
    s!"the attribute {a.src}.{a.name} has the value type {a.tgt.text}; a value type is \
      optional at most once"

def kind : TypeProblem → String
  | .undeclared .. => "undeclaredValueType"
  | .nestedOptional .. => "nestedOptional"

end TypeProblem

end Schema

end DDD
