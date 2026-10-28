import DDD.Values
import Mathlib.Data.List.Nodup

/-!
# Schemas

The deep presentation of a schema, one per bounded context, and its
well-formedness check. A schema lists

- entity types, by name;
- references `r : e ⟶ e'` between entity types, with parallel references allowed;
- attributes `a : e ⟶ v` from an entity type to a value type;
- equations between parallel paths, possibly ending in an attribute;
- aggregates: a root entity type, and members, each with an ownership reference
  to the root.

References and attributes are the generators. A generator is identified by its
source entity type and its name, so two entity types may each have a generator
called `name`. A path is a source object and a list of generator names;
`Schema.tgt?` computes its target. `DDD.Semantics` builds the category the schema
presents.

`Schema.checkWellFormed` decides `Schema.WellFormed` (`checkWellFormed_iff`):
unique names, references between declared entity types, equations between
parallel paths, and aggregate annotations that are consistent and respected by
every reference from outside an aggregate.
-/

namespace DDD

/-- An object of a schema: an entity type, by name, or a value type. -/
inductive Ob where
  | entity (name : String)
  | value (v : ValueType)
deriving DecidableEq, Repr

/-- A reference `name : src ⟶ tgt` between entity types. -/
structure Ref where
  name : String
  src : String
  tgt : String
deriving DecidableEq, Repr

/-- An attribute `name : src ⟶ tgt` from an entity type to a value type. -/
structure Attr where
  name : String
  src : String
  tgt : ValueType
deriving DecidableEq, Repr

/-- The equation `lhs = rhs` between two paths out of the entity type `src`. -/
structure Equation where
  src : String
  lhs : List String
  rhs : List String
deriving DecidableEq, Repr

/-- A member of an aggregate: an entity type and the name of its ownership
reference to the root. -/
structure Member where
  entity : String
  owner : String
deriving DecidableEq, Repr

/-- An aggregate: a root entity type and its members. -/
structure Aggregate where
  root : String
  members : List Member
deriving DecidableEq, Repr

/-- The entity types of an aggregate: the root, then the members. -/
def Aggregate.entities (A : Aggregate) : List String :=
  A.root :: A.members.map (·.entity)

/-- The presentation of a schema. -/
structure Schema where
  entities : List String
  refs : List Ref := []
  attrs : List Attr := []
  eqns : List Equation := []
  aggregates : List Aggregate := []
deriving DecidableEq, Repr

namespace Schema

variable (S : Schema)

/-- The reference named `n` out of the entity type `e`, if there is one. -/
def ref? (e n : String) : Option Ref := S.refs.find? fun r => r.src == e && r.name == n

/-- The attribute named `n` out of the entity type `e`, if there is one. -/
def attr? (e n : String) : Option Attr := S.attrs.find? fun a => a.src == e && a.name == n

/-- The target of the generator named `n` out of `o`, if there is one. References
are searched before attributes. Value types have no outgoing generators. -/
def step? : Ob → String → Option Ob
  | .value _, _ => none
  | .entity e, n =>
    match S.ref? e n with
    | some r => some (.entity r.tgt)
    | none => (S.attr? e n).map fun a => .value a.tgt

/-- The target of the path `ns` out of `o`, if each name in turn names a generator. -/
def tgt? : Ob → List String → Option Ob
  | o, [] => some o
  | o, n :: ns => (S.step? o n).bind fun o' => tgt? o' ns

@[simp] theorem tgt?_nil (o : Ob) : S.tgt? o [] = some o := rfl

@[simp] theorem tgt?_cons (o : Ob) (n : String) (ns : List String) :
    S.tgt? o (n :: ns) = (S.step? o n).bind fun o' => S.tgt? o' ns := rfl

theorem tgt?_append (o : Ob) (ns ms : List String) :
    S.tgt? o (ns ++ ms) = (S.tgt? o ns).bind fun o' => S.tgt? o' ms := by
  induction ns generalizing o with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.cons_append, tgt?_cons, ih]
    cases S.step? o n <;> rfl

/-- The names of the generators out of the entity type `e`. -/
def outNames (e : String) : List String :=
  (S.refs.filter (·.src == e)).map (·.name) ++ (S.attrs.filter (·.src == e)).map (·.name)

/-- The two sides of an equation have a target, and the same one. -/
def Parallel (q : Equation) : Prop :=
  ∃ o, S.tgt? (.entity q.src) q.lhs = some o ∧ S.tgt? (.entity q.src) q.rhs = some o

/-- Well-formedness of a schema. -/
structure WellFormed : Prop where
  /-- Entity types have distinct names. -/
  entities_nodup : S.entities.Nodup
  /-- The generators out of an entity type have distinct names. -/
  names_nodup : ∀ e ∈ S.entities, (S.outNames e).Nodup
  /-- References run between declared entity types. -/
  ref_src : ∀ r ∈ S.refs, r.src ∈ S.entities
  ref_tgt : ∀ r ∈ S.refs, r.tgt ∈ S.entities
  /-- Attributes start at declared entity types. -/
  attr_src : ∀ a ∈ S.attrs, a.src ∈ S.entities
  /-- Equations start at declared entity types and relate parallel paths. -/
  eqn_src : ∀ q ∈ S.eqns, q.src ∈ S.entities
  eqn_parallel : ∀ q ∈ S.eqns, S.Parallel q
  /-- Aggregates consist of declared entity types. -/
  agg_entities : ∀ A ∈ S.aggregates, ∀ e ∈ A.entities, e ∈ S.entities
  /-- No entity type belongs to two aggregates, or twice to one. -/
  agg_disjoint : (S.aggregates.flatMap Aggregate.entities).Nodup
  /-- Each member has its ownership reference to the root. -/
  agg_owner : ∀ A ∈ S.aggregates, ∀ m ∈ A.members, ⟨m.owner, m.entity, A.root⟩ ∈ S.refs
  /-- A reference to a member of an aggregate starts inside that aggregate: from
  outside, references target the root only. -/
  agg_boundary : ∀ r ∈ S.refs, ∀ A ∈ S.aggregates,
    r.tgt ∈ A.members.map (·.entity) → r.src ∈ A.entities

/-- The check for `Parallel`. -/
def parallel (q : Equation) : Bool :=
  match S.tgt? (.entity q.src) q.lhs with
  | some o => S.tgt? (.entity q.src) q.rhs == some o
  | none => false

theorem parallel_iff (q : Equation) : S.parallel q = true ↔ S.Parallel q := by
  unfold parallel Parallel
  cases S.tgt? (.entity q.src) q.lhs <;> simp

/-- The well-formedness check. -/
def checkWellFormed : Bool :=
  decide S.entities.Nodup &&
  S.entities.all (fun e => decide (S.outNames e).Nodup) &&
  S.refs.all (fun r => decide (r.src ∈ S.entities) && decide (r.tgt ∈ S.entities)) &&
  S.attrs.all (fun a => decide (a.src ∈ S.entities)) &&
  S.eqns.all (fun q => decide (q.src ∈ S.entities) && S.parallel q) &&
  S.aggregates.all (fun A => A.entities.all fun e => decide (e ∈ S.entities)) &&
  decide (S.aggregates.flatMap Aggregate.entities).Nodup &&
  S.aggregates.all (fun A => A.members.all fun m =>
    decide (⟨m.owner, m.entity, A.root⟩ ∈ S.refs)) &&
  S.refs.all (fun r => S.aggregates.all fun A =>
    !decide (r.tgt ∈ A.members.map (·.entity)) || decide (r.src ∈ A.entities))

theorem checkWellFormed_iff : S.checkWellFormed = true ↔ S.WellFormed := by
  simp only [checkWellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    parallel_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩, h₉⟩
    exact ⟨h₁, h₂, fun r hr => (h₃ r hr).1, fun r hr => (h₃ r hr).2, h₄,
      fun q hq => (h₅ q hq).1, fun q hq => (h₅ q hq).2, h₆, h₇, h₈,
      fun r hr A hA hm => (h₉ r hr A hA).resolve_left (not_not.mpr hm)⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h.entities_nodup, h.names_nodup⟩,
      fun r hr => ⟨h.ref_src r hr, h.ref_tgt r hr⟩⟩, h.attr_src⟩,
      fun q hq => ⟨h.eqn_src q hq, h.eqn_parallel q hq⟩⟩, h.agg_entities⟩, h.agg_disjoint⟩,
      h.agg_owner⟩, fun r hr A hA => or_iff_not_imp_left.mpr fun hm =>
        h.agg_boundary r hr A hA (not_not.mp hm)⟩

instance : Decidable S.WellFormed := decidable_of_iff _ S.checkWellFormed_iff

theorem tgt?_singleton (o : Ob) (n : String) : S.tgt? o [n] = S.step? o n := by
  simp only [tgt?_cons, tgt?_nil]
  cases S.step? o n <;> rfl

variable {S}

/-- In a well-formed schema, a listed reference is the generator its source and
name find. -/
theorem step?_of_mem_refs (hS : S.WellFormed) {r : Ref} (hr : r ∈ S.refs) :
    S.step? (.entity r.src) r.name = some (.entity r.tgt) := by
  have hsome : (S.ref? r.src r.name).isSome := by
    unfold ref?
    rw [List.find?_isSome]
    exact ⟨r, hr, by simp⟩
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hr'
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hnd := hS.names_nodup r.src (hS.ref_src r hr)
  unfold outNames at hnd
  have h₁ := (List.nodup_append.mp hnd).1
  have : r' = r := List.inj_on_of_nodup_map h₁
    (List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hr', by simp [hp.1]⟩)
    (List.mem_filter.mpr ⟨hr, by simp⟩) hp.2
  simp [step?, hr', this]

/-- In a well-formed schema, a listed attribute is the generator its source and
name find. -/
theorem step?_of_mem_attrs (hS : S.WellFormed) {a : Attr} (ha : a ∈ S.attrs) :
    S.step? (.entity a.src) a.name = some (.value a.tgt) := by
  have hnd := hS.names_nodup a.src (hS.attr_src a ha)
  unfold outNames at hnd
  obtain ⟨-, h₂, hdisj⟩ := List.nodup_append.mp hnd
  have hnone : S.ref? a.src a.name = none := by
    unfold ref?
    rw [List.find?_eq_none]
    intro r hr hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hdisj r.name (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [hp.1]⟩, rfl⟩)
      a.name (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp⟩, rfl⟩) hp.2
  have hsome : (S.attr? a.src a.name).isSome := by
    unfold attr?
    rw [List.find?_isSome]
    exact ⟨a, ha, by simp⟩
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some ha'
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have : a' = a := List.inj_on_of_nodup_map h₂
    (List.mem_filter.mpr ⟨List.mem_of_find?_eq_some ha', by simp [hp.1]⟩)
    (List.mem_filter.mpr ⟨ha, by simp⟩) hp.2
  simp [step?, hnone, ha', this]

end Schema

end DDD
