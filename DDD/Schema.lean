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
  to the root or to another member, so that the ownership references form a tree;
- value objects: entity types identified by all their fields, attributes and
  references;
- keys: an entity type and some of its fields, which together identify its
  entities;
- subtypes: an entity type with an is-a reference to its supertype, which is a
  key on its own.

References and attributes are the generators. A generator is identified by its
source entity type and its name, so two entity types may each have a generator
called `name`. A path is a source object and a list of generator names;
`Schema.tgt?` computes its target. `DDD.Semantics` builds the category the schema
presents.

`Schema.checkWellFormed` decides `Schema.WellFormed` (`checkWellFormed_iff`):
unique names, references between declared entity types, equations between
parallel paths, aggregate annotations that are consistent and respected by
every reference from outside an aggregate, ownership references that reach the
root without a cycle, value objects that are declared and have a field, keys
of declared entity types whose fields are their generators, and subtypes with
their is-a reference.

`Schema.allKeys`: the declared keys, the key of all fields of each value object,
and the is-a reference of each subtype. A state satisfies them when two entities
that agree on the fields of a key are equal (`Schema.State.Keys`, `DDD.Data`).

`Schema.RootsOnly P S`, decided by `checkRootsOnly`: no entity type of `P` is a
member of an aggregate of `S`, the condition on a published language `P` of `S`.
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
reference, to the root or to another member. -/
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

/-- A key: an entity type and names of its fields, references and attributes.
Two entities that agree on every field of a key are equal. -/
structure Key where
  entity : String
  fields : List String
deriving DecidableEq, Repr

/-- A subtype: an entity type and the name of its is-a reference to its
supertype. The is-a reference is a key on its own, so a subtype is a subobject
of its supertype, and the fields of the supertype are reached through it. -/
structure IsA where
  entity : String
  ref : String
deriving DecidableEq, Repr

/-- The presentation of a schema. -/
structure Schema where
  entities : List String
  refs : List Ref := []
  attrs : List Attr := []
  eqns : List Equation := []
  aggregates : List Aggregate := []
  valueObjects : List String := []
  keys : List Key := []
  subtypes : List IsA := []
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

/-- The owner of the entity type `e` in the aggregate `A`: the target of the
ownership reference of the member `e`, if `e` is a member and the reference
exists. -/
def ownerStep (A : Aggregate) (e : String) : Option String :=
  (A.members.find? (·.entity == e)).bind fun m => (S.ref? m.entity m.owner).map (·.tgt)

/-- Following ownership references at most `k` times from `e`, stopping at the
root of `A`. -/
def ownerIter (A : Aggregate) : Nat → String → Option String
  | 0, e => some e
  | k + 1, e => if e = A.root then some e else (S.ownerStep A e).bind (ownerIter A k)

/-- The ownership references depend on the references only. -/
theorem ownerIter_of_refs {S' : Schema} (h : S.refs = S'.refs) (A : Aggregate) :
    ∀ (k : Nat) (e : String), S.ownerIter A k e = S'.ownerIter A k e
  | 0, _ => rfl
  | k + 1, e => by
    have hs : S.ownerStep A e = S'.ownerStep A e := by simp only [ownerStep, ref?, h]
    have ih : S.ownerIter A k = S'.ownerIter A k := funext (ownerIter_of_refs h A k)
    simp only [ownerIter, hs, ih]

/-- The keys of `S`: the declared keys, the key of all fields of each value object,
and the is-a reference of each subtype. -/
def allKeys : List Key :=
  S.keys ++ S.valueObjects.map (fun e => ⟨e, S.outNames e⟩) ++
    S.subtypes.map fun s => ⟨s.entity, [s.ref]⟩

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
  /-- The ownership reference of each member targets an entity type of its
  aggregate. -/
  agg_owner : ∀ A ∈ S.aggregates, ∀ m ∈ A.members,
    ∃ t ∈ A.entities, (⟨m.owner, m.entity, t⟩ : Ref) ∈ S.refs
  /-- Following ownership references from each member reaches the root, in at
  most as many steps as there are members: the ownership references form a tree. -/
  agg_tree : ∀ A ∈ S.aggregates, ∀ m ∈ A.members,
    S.ownerIter A A.members.length m.entity = some A.root
  /-- A reference to a member of an aggregate starts inside that aggregate: from
  outside, references target the root only. -/
  agg_boundary : ∀ r ∈ S.refs, ∀ A ∈ S.aggregates,
    r.tgt ∈ A.members.map (·.entity) → r.src ∈ A.entities
  /-- Value objects are declared entity types with at least one field. -/
  vo_entities : ∀ e ∈ S.valueObjects, e ∈ S.entities
  vo_fields : ∀ e ∈ S.valueObjects, S.outNames e ≠ []
  /-- Keys are on declared entity types, have a field, and name generators out of
  their entity type. -/
  key_entities : ∀ k ∈ S.keys, k.entity ∈ S.entities
  key_nonempty : ∀ k ∈ S.keys, k.fields ≠ []
  key_fields : ∀ k ∈ S.keys, ∀ n ∈ k.fields, n ∈ S.outNames k.entity
  /-- Subtypes are declared entity types with their is-a reference. -/
  isa_entities : ∀ s ∈ S.subtypes, s.entity ∈ S.entities
  isa_ref : ∀ s ∈ S.subtypes, ∃ r ∈ S.refs, r.src = s.entity ∧ r.name = s.ref

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
  (S.entities.all (fun e => decide (S.outNames e).Nodup) &&
  (S.refs.all (fun r => decide (r.src ∈ S.entities) && decide (r.tgt ∈ S.entities)) &&
  (S.attrs.all (fun a => decide (a.src ∈ S.entities)) &&
  (S.eqns.all (fun q => decide (q.src ∈ S.entities) && S.parallel q) &&
  (S.aggregates.all (fun A => A.entities.all fun e => decide (e ∈ S.entities)) &&
  (decide (S.aggregates.flatMap Aggregate.entities).Nodup &&
  (S.aggregates.all (fun A => A.members.all fun m =>
    (A.entities.any fun t => decide ((⟨m.owner, m.entity, t⟩ : Ref) ∈ S.refs)) &&
      decide (S.ownerIter A A.members.length m.entity = some A.root)) &&
  (S.refs.all (fun r => S.aggregates.all fun A =>
    !decide (r.tgt ∈ A.members.map (·.entity)) || decide (r.src ∈ A.entities)) &&
  (S.valueObjects.all (fun e => decide (e ∈ S.entities) && decide (S.outNames e ≠ [])) &&
  (S.keys.all (fun k => decide (k.entity ∈ S.entities) &&
    (decide (k.fields ≠ []) && k.fields.all fun n => decide (n ∈ S.outNames k.entity))) &&
  S.subtypes.all fun s => decide (s.entity ∈ S.entities) &&
    S.refs.any fun r => r.src == s.entity && r.name == s.ref))))))))))

theorem checkWellFormed_iff : S.checkWellFormed = true ↔ S.WellFormed := by
  simp only [checkWellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    parallel_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩
    exact ⟨h₁, h₂, fun r hr => (h₃ r hr).1, fun r hr => (h₃ r hr).2, h₄,
      fun q hq => (h₅ q hq).1, fun q hq => (h₅ q hq).2, h₆, h₇,
      fun A hA m hm => (h₈ A hA m hm).1, fun A hA m hm => (h₈ A hA m hm).2,
      fun r hr A hA hm => (h₉ r hr A hA).resolve_left (not_not.mpr hm),
      fun e he => (h₁₀ e he).1, fun e he => (h₁₀ e he).2,
      fun k hk => (h₁₁ k hk).1, fun k hk => (h₁₁ k hk).2.1, fun k hk => (h₁₁ k hk).2.2,
      fun s hs => (h₁₂ s hs).1, fun s hs => (h₁₂ s hs).2⟩
  · intro h
    exact ⟨h.entities_nodup, h.names_nodup, fun r hr => ⟨h.ref_src r hr, h.ref_tgt r hr⟩,
      h.attr_src, fun q hq => ⟨h.eqn_src q hq, h.eqn_parallel q hq⟩, h.agg_entities,
      h.agg_disjoint, fun A hA m hm => ⟨h.agg_owner A hA m hm, h.agg_tree A hA m hm⟩,
      fun r hr A hA => or_iff_not_imp_left.mpr fun hm =>
        h.agg_boundary r hr A hA (not_not.mp hm),
      fun e he => ⟨h.vo_entities e he, h.vo_fields e he⟩,
      fun k hk => ⟨h.key_entities k hk, h.key_nonempty k hk, h.key_fields k hk⟩,
      fun s hs => ⟨h.isa_entities s hs, h.isa_ref s hs⟩⟩

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

/-! ## Published languages -/

/-- `P` contains roots of `S` only: no entity type of `P` is a member of an
aggregate of `S`. A published language included in its owner `S` satisfies it, so
references into it from other contexts target roots. -/
def RootsOnly (P S : Schema) : Prop :=
  ∀ e ∈ P.entities, ∀ A ∈ S.aggregates, e ∉ A.members.map (·.entity)

/-- The check for `RootsOnly`. -/
def checkRootsOnly (P S : Schema) : Bool :=
  P.entities.all fun e => S.aggregates.all fun A => !decide (e ∈ A.members.map (·.entity))

theorem checkRootsOnly_iff (P S : Schema) : P.checkRootsOnly S = true ↔ P.RootsOnly S := by
  simp only [checkRootsOnly, RootsOnly, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]

instance (P S : Schema) : Decidable (P.RootsOnly S) := decidable_of_iff _ (P.checkRootsOnly_iff S)

end Schema

end DDD
