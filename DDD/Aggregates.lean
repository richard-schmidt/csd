import DDD.Union
import DDD.States
import Mathlib.Data.List.Dedup

/-!
# Aggregates

The aggregate is the unit of consistency of a step: one step changes one
aggregate and keeps its own rules; the rules across aggregates are found from the
schema and kept between steps.

- `Schema.allAggregates`: the aggregates of a schema, then each entity type that
  belongs to no aggregate as an aggregate of its own. Every entity type belongs
  to exactly one of them (`exists_aggregate`, `eq_of_mem_entities`).
- `Schema.aggregateSchema S A`: the entity types of `A` with their references and
  attributes, the entity types outside `A` that its references reach, as
  identities with no generators (`identities`), and the equations of `S` whose
  two sides are paths of it. It is well-formed when `S` is
  (`aggregateSchema_wellFormed`).
- `Schema.crossAggregateEqns`: the equations of `S` internal to no aggregate, the
  rules across aggregates. `internalSchema` is `S` with the other equations
  only.
- The covering theorem of `Union.lean` applies: the aggregate schemas cover the
  internal schema (`aggregateCover`).

Consistency of a context, for attributed states:

- `familyEquiv`: a state of the internal schema is a family of states of the
  aggregate schemas that agree on what they share, the identities and the
  values (`Compatible`).
- `crossEquiv`: a state of `S` is a state of the internal schema in which the
  equations across aggregates hold (`Satisfies`).

So a state of the context is a family of aggregate states that agree on the
identities and satisfy the equations across aggregates.
-/

namespace DDD

open CategoryTheory

namespace Schema

variable (S : Schema)

/-- The entity types of `S` that belong to no aggregate. -/
def looseEntities : List String :=
  S.entities.filter fun e => e ∉ S.aggregates.flatMap Aggregate.entities

/-- The aggregates of `S`, then each entity type that belongs to no aggregate as an
aggregate of its own, with no members. -/
def allAggregates : List Aggregate :=
  S.aggregates ++ S.looseEntities.map fun e => ⟨e, []⟩

variable (A : Aggregate)

/-- The references out of the entity types of `A`. -/
def aggRefs : List Ref := S.refs.filter fun r => r.src ∈ A.entities

/-- The attributes of the entity types of `A`. -/
def aggAttrs : List Attr := S.attrs.filter fun a => a.src ∈ A.entities

/-- The identities of `A`: the entity types outside `A` that its references
reach. -/
def identities : List String :=
  (((S.aggRefs A).map (·.tgt)).filter fun e => e ∉ A.entities).dedup

/-- The aggregate schema of `A`, without equations. -/
def aggregateBase : Schema where
  entities := A.entities ++ S.identities A
  refs := S.aggRefs A
  attrs := S.aggAttrs A
  aggregates := [A]
  valueObjects := S.valueObjects.filter fun e => e ∈ A.entities

/-- The equation `q` is internal to `A`: it starts in `A`, and its two sides are
paths of the aggregate schema of `A`. -/
def internal (q : Equation) : Bool :=
  decide (q.src ∈ A.entities) && ((S.aggregateBase A).tgt? (.entity q.src) q.lhs).isSome &&
    ((S.aggregateBase A).tgt? (.entity q.src) q.rhs).isSome

/-- The aggregate schema of `A`: the entity types of `A` with their references and
attributes, its identities as entity types with no generators, and the equations
of `S` internal to `A`. -/
def aggregateSchema : Schema :=
  { S.aggregateBase A with eqns := S.eqns.filter (S.internal A) }

/-- The equations of `S` internal to some aggregate. -/
def internalEqns : List Equation :=
  S.eqns.filter fun q => S.allAggregates.any fun A => S.internal A q

/-- The equations of `S` internal to no aggregate: the rules across aggregates. -/
def crossAggregateEqns : List Equation :=
  S.eqns.filter fun q => !S.allAggregates.any fun A => S.internal A q

/-- `S` with the equations internal to some aggregate, and no other. -/
def internalSchema : Schema := { S with eqns := S.internalEqns }

/-! ## Every entity type in exactly one aggregate -/

variable {S A}

theorem mem_allAggregates :
    A ∈ S.allAggregates ↔
      A ∈ S.aggregates ∨ ∃ e ∈ S.looseEntities, A = ⟨e, []⟩ := by
  simp only [allAggregates, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, rfl⟩

theorem flatMap_allAggregates :
    S.allAggregates.flatMap Aggregate.entities =
      S.aggregates.flatMap Aggregate.entities ++ S.looseEntities := by
  simp only [allAggregates, List.flatMap_append, List.flatMap_map, Aggregate.entities,
    List.map_nil]
  congr 1
  induction S.looseEntities with
  | nil => rfl
  | cons e l ih => simp [ih]

/-- No entity type belongs to two aggregates of `allAggregates`. -/
theorem nodup_allAggregates (hS : S.WellFormed) :
    (S.allAggregates.flatMap Aggregate.entities).Nodup := by
  rw [flatMap_allAggregates, List.nodup_append]
  refine ⟨hS.agg_disjoint, hS.entities_nodup.filter _, fun a ha b hb hab => ?_⟩
  subst hab
  simp only [looseEntities, List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 ha

theorem nodup_entities_of_mem (hS : S.WellFormed) (hA : A ∈ S.allAggregates) :
    A.entities.Nodup :=
  (List.nodup_flatMap.mp (nodup_allAggregates hS)).1 A hA

/-- An entity type belongs to at most one aggregate of `allAggregates`. -/
theorem eq_of_mem_entities (hS : S.WellFormed) {A A' : Aggregate} (hA : A ∈ S.allAggregates)
    (hA' : A' ∈ S.allAggregates) {e : String} (he : e ∈ A.entities) (he' : e ∈ A'.entities) :
    A = A' := by
  by_contra hne
  have hp := (List.nodup_flatMap.mp (nodup_allAggregates hS)).2
  exact hp.forall (fun _ _ h => h.symm) hA hA' hne he he'

/-- Every entity type belongs to an aggregate of `allAggregates`. -/
theorem exists_aggregate {e : String} (he : e ∈ S.entities) :
    ∃ A ∈ S.allAggregates, e ∈ A.entities := by
  by_cases h : e ∈ S.aggregates.flatMap Aggregate.entities
  · obtain ⟨A, hA, heA⟩ := List.mem_flatMap.mp h
    exact ⟨A, List.mem_append_left _ hA, heA⟩
  · refine ⟨⟨e, []⟩, mem_allAggregates.mpr (Or.inr ⟨e, ?_, rfl⟩), List.mem_cons_self⟩
    exact List.mem_filter.mpr ⟨he, decide_eq_true h⟩

theorem entities_of_mem (hS : S.WellFormed) (hA : A ∈ S.allAggregates) :
    ∀ e ∈ A.entities, e ∈ S.entities := by
  rcases mem_allAggregates.mp hA with h | ⟨e, he, rfl⟩
  · exact hS.agg_entities A h
  · intro e' he'
    obtain rfl : e' = e := List.mem_singleton.mp he'
    exact (List.mem_filter.mp he).1

theorem owner_of_mem (hS : S.WellFormed) (hA : A ∈ S.allAggregates) :
    ∀ m ∈ A.members, (⟨m.owner, m.entity, A.root⟩ : Ref) ∈ S.refs := by
  rcases mem_allAggregates.mp hA with h | ⟨e, -, rfl⟩
  · exact hS.agg_owner A h
  · intro m hm
    exact absurd hm List.not_mem_nil

/-! ## Aggregate schemas -/

variable (S A)

@[simp] theorem aggregateSchema_entities :
    (S.aggregateSchema A).entities = A.entities ++ S.identities A := rfl

@[simp] theorem aggregateSchema_refs : (S.aggregateSchema A).refs = S.aggRefs A := rfl

@[simp] theorem aggregateSchema_attrs : (S.aggregateSchema A).attrs = S.aggAttrs A := rfl

theorem step?_aggregateSchema (o : Ob) (n : String) :
    (S.aggregateSchema A).step? o n = (S.aggregateBase A).step? o n := by
  cases o <;> rfl

theorem tgt?_aggregateSchema (o : Ob) (l : List String) :
    (S.aggregateSchema A).tgt? o l = (S.aggregateBase A).tgt? o l := by
  induction l generalizing o with
  | nil => rfl
  | cons n ns ih => simp only [tgt?_cons, step?_aggregateSchema, ih]

theorem step?_internalSchema (o : Ob) (n : String) : S.internalSchema.step? o n = S.step? o n := by
  cases o <;> rfl

theorem tgt?_internalSchema (o : Ob) (l : List String) :
    S.internalSchema.tgt? o l = S.tgt? o l := by
  induction l generalizing o with
  | nil => rfl
  | cons n ns ih => simp only [tgt?_cons, step?_internalSchema, ih]

variable {S A}

theorem ref?_aggregate {e n : String} (he : e ∈ A.entities) :
    (S.aggregateSchema A).ref? e n = S.ref? e n := by
  simp only [ref?, aggregateSchema_refs, aggRefs, List.find?_filter]
  congr 1
  funext r
  by_cases h : r.src = e
  · subst h
    cases h' : (r.name == n) <;> simp_all
  · simp [h]

theorem attr?_aggregate {e n : String} (he : e ∈ A.entities) :
    (S.aggregateSchema A).attr? e n = S.attr? e n := by
  simp only [attr?, aggregateSchema_attrs, aggAttrs, List.find?_filter]
  congr 1
  funext a
  by_cases h : a.src = e
  · subst h
    cases h' : (a.name == n) <;> simp_all
  · simp [h]

/-- Out of an entity type of `A`, the aggregate schema has the generators of `S`. -/
theorem step?_aggregate {e : String} (he : e ∈ A.entities) (n : String) :
    (S.aggregateSchema A).step? (.entity e) n = S.step? (.entity e) n := by
  simp only [step?, ref?_aggregate he, attr?_aggregate he]

/-- Out of an identity, the aggregate schema has no generator. -/
theorem step?_aggregate_of_not_mem {e : String} (he : e ∉ A.entities) (n : String) :
    (S.aggregateSchema A).step? (.entity e) n = none := by
  have hr : (S.aggregateSchema A).ref? e n = none := by
    simp only [ref?, aggregateSchema_refs, aggRefs, List.find?_eq_none, List.mem_filter,
      decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_and]
    rintro r ⟨-, hr⟩ rfl
    exact absurd hr he
  have ha : (S.aggregateSchema A).attr? e n = none := by
    simp only [attr?, aggregateSchema_attrs, aggAttrs, List.find?_eq_none, List.mem_filter,
      decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_and]
    rintro a ⟨-, ha⟩ rfl
    exact absurd ha he
  simp [step?, hr, ha]

/-- A generator of the aggregate schema starts in `A` and is a generator of `S`. -/
theorem step?_of_aggregate {o x : Ob} {n : String} (h : (S.aggregateSchema A).step? o n = some x) :
    (∃ e, o = .entity e ∧ e ∈ A.entities) ∧ S.step? o n = some x := by
  cases o with
  | value => simp [step?] at h
  | entity e =>
    by_cases he : e ∈ A.entities
    · exact ⟨⟨e, rfl, he⟩, (step?_aggregate he n).symm.trans h⟩
    · rw [step?_aggregate_of_not_mem he] at h
      exact absurd h (by simp)

/-- A path of the aggregate schema is a path of `S`. -/
theorem tgt?_of_aggregate : ∀ {o x : Ob} {l : List String},
    (S.aggregateSchema A).tgt? o l = some x → S.tgt? o l = some x
  | _, _, [], h => h
  | o, x, n :: ns, h => by
    cases hs : (S.aggregateSchema A).step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [tgt?_cons, hs, Option.bind_some] at h
      simp only [tgt?_cons, (step?_of_aggregate hs).2, Option.bind_some]
      exact tgt?_of_aggregate h

theorem mem_identities {e : String} :
    e ∈ S.identities A ↔
      e ∉ A.entities ∧ ∃ r ∈ S.refs, r.src ∈ A.entities ∧ r.tgt = e := by
  simp only [identities, List.mem_dedup, List.mem_filter, List.mem_map, aggRefs,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨r, ⟨hr, hs⟩, rfl⟩, he⟩
    exact ⟨he, r, hr, hs, rfl⟩
  · rintro ⟨he, r, hr, hs, rfl⟩
    exact ⟨⟨r, ⟨hr, hs⟩, rfl⟩, he⟩

/-- The generator names of the aggregate schema out of `e` are among those of `S`. -/
theorem outNames_aggregate_sublist (e : String) :
    List.Sublist ((S.aggregateSchema A).outNames e) (S.outNames e) :=
  List.Sublist.append ((List.filter_sublist.filter _).map _)
    ((List.filter_sublist.filter _).map _)

/-- The aggregate schema of an aggregate of a well-formed schema is well-formed. -/
theorem aggregateSchema_wellFormed (hS : S.WellFormed) (hA : A ∈ S.allAggregates) :
    (S.aggregateSchema A).WellFormed where
  entities_nodup := by
    rw [aggregateSchema_entities, List.nodup_append]
    refine ⟨nodup_entities_of_mem hS hA, List.nodup_dedup _, fun a ha b hb hab => ?_⟩
    subst hab
    exact (mem_identities.mp hb).1 ha
  names_nodup e he := by
    have heS : e ∈ S.entities := by
      rcases List.mem_append.mp he with h | h
      · exact entities_of_mem hS hA e h
      · obtain ⟨-, r, hr, -, rfl⟩ := mem_identities.mp h
        exact hS.ref_tgt r hr
    exact (hS.names_nodup e heS).sublist (outNames_aggregate_sublist e)
  ref_src r hr := by
    simp only [aggregateSchema_refs, aggRefs, List.mem_filter, decide_eq_true_eq] at hr
    exact List.mem_append_left _ hr.2
  ref_tgt r hr := by
    simp only [aggregateSchema_refs, aggRefs, List.mem_filter, decide_eq_true_eq] at hr
    by_cases h : r.tgt ∈ A.entities
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (mem_identities.mpr ⟨h, r, hr.1, hr.2, rfl⟩)
  attr_src a ha := by
    simp only [aggregateSchema_attrs, aggAttrs, List.mem_filter, decide_eq_true_eq] at ha
    exact List.mem_append_left _ ha.2
  eqn_src q hq := by
    simp only [aggregateSchema, List.mem_filter, internal, Bool.and_eq_true,
      decide_eq_true_eq] at hq
    exact List.mem_append_left _ hq.2.1.1
  eqn_parallel q hq := by
    simp only [aggregateSchema, List.mem_filter, internal, Bool.and_eq_true,
      decide_eq_true_eq] at hq
    obtain ⟨hq, ⟨-, hl⟩, hr⟩ := hq
    rw [← tgt?_aggregateSchema] at hl hr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hr
    obtain ⟨o, hlo, hro⟩ := hS.eqn_parallel q hq
    have hx' := tgt?_of_aggregate (S := S) (A := A) hx
    have hy' := tgt?_of_aggregate (S := S) (A := A) hy
    obtain rfl : x = o := Option.some.inj (hx'.symm.trans hlo)
    obtain rfl : y = x := Option.some.inj (hy'.symm.trans hro)
    exact ⟨y, hx, hy⟩
  agg_entities A' hA' e he := by
    obtain rfl : A' = A := List.mem_singleton.mp hA'
    exact List.mem_append_left _ he
  agg_disjoint := by
    simpa [aggregateSchema, aggregateBase] using nodup_entities_of_mem hS hA
  agg_owner A' hA' m hm := by
    obtain rfl : A' = A := List.mem_singleton.mp hA'
    simp only [aggregateSchema_refs, aggRefs, List.mem_filter, decide_eq_true_eq]
    exact ⟨owner_of_mem hS hA m hm, List.mem_cons_of_mem _ (List.mem_map_of_mem hm)⟩
  agg_boundary r hr A' hA' _ := by
    obtain rfl : A' = A := List.mem_singleton.mp hA'
    simp only [aggregateSchema_refs, aggRefs, List.mem_filter, decide_eq_true_eq] at hr
    exact hr.2
  vo_entities e he := by
    simp only [aggregateSchema, aggregateBase, List.mem_filter, decide_eq_true_eq] at he
    exact List.mem_append_left _ he.2
  vo_attrs e he := by
    simp only [aggregateSchema, aggregateBase, List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨a, ha, hae⟩ := hS.vo_attrs e he.1
    exact ⟨a, List.mem_filter.mpr ⟨ha, decide_eq_true (hae ▸ he.2)⟩, hae⟩

/-! ## The internal schema -/

theorem mem_internalEqns {q : Equation} :
    q ∈ S.internalEqns ↔ q ∈ S.eqns ∧ ∃ A ∈ S.allAggregates, S.internal A q = true := by
  simp [internalEqns, List.mem_filter, List.any_eq_true]

theorem mem_crossAggregateEqns {q : Equation} :
    q ∈ S.crossAggregateEqns ↔
      q ∈ S.eqns ∧ ∀ A ∈ S.allAggregates, S.internal A q = false := by
  simp [crossAggregateEqns, List.mem_filter, List.any_eq_false]

/-- An equation of `S` is internal to an aggregate or crosses aggregates. -/
theorem mem_internalEqns_or_cross {q : Equation} (hq : q ∈ S.eqns) :
    q ∈ S.internalEqns ∨ q ∈ S.crossAggregateEqns := by
  by_cases h : ∃ A ∈ S.allAggregates, S.internal A q = true
  · exact Or.inl (mem_internalEqns.mpr ⟨hq, h⟩)
  · push_neg at h
    exact Or.inr (mem_crossAggregateEqns.mpr ⟨hq, fun A hA => by simpa using h A hA⟩)

theorem internalSchema_wellFormed (hS : S.WellFormed) : S.internalSchema.WellFormed :=
  { hS with
    eqn_src := fun q hq => hS.eqn_src q (mem_internalEqns.mp hq).1
    eqn_parallel := fun q hq => by
      obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q (mem_internalEqns.mp hq).1
      exact ⟨o, (tgt?_internalSchema S _ _).trans hl, (tgt?_internalSchema S _ _).trans hr⟩ }

/-- The internal schema is included in `S`. -/
theorem internal_valid (hS : S.WellFormed) : ({} : Translation).Valid S.internalSchema S where
  entity _ he := he
  ref r hr := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    exact step?_of_mem_refs hS hr
  attr a ha := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    exact step?_of_mem_attrs hS ha
  eqn q hq := by
    have hq' := (mem_internalEqns.mp hq).1
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq'
    rw [← tgt?_internalSchema] at hl hr
    rw [Translation.mapPath_empty hl, Translation.mapPath_empty hr]
    exact ⟨hS.eqn_src q hq', pathEq_of_mem_eqns hS hq'⟩

/-- The aggregate schema of `A` is included in the internal schema. -/
theorem aggregate_valid (hS : S.WellFormed) (hA : A ∈ S.allAggregates) :
    ({} : Translation).Valid (S.aggregateSchema A) S.internalSchema where
  entity e he := by
    rcases List.mem_append.mp he with h | h
    · exact entities_of_mem hS hA e h
    · obtain ⟨-, r, hr, -, rfl⟩ := mem_identities.mp h
      exact hS.ref_tgt r hr
  ref r hr := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    simp only [aggregateSchema_refs, aggRefs, List.mem_filter] at hr
    exact step?_of_mem_refs (internalSchema_wellFormed hS) hr.1
  attr a ha := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    simp only [aggregateSchema_attrs, aggAttrs, List.mem_filter] at ha
    exact step?_of_mem_attrs (internalSchema_wellFormed hS) ha.1
  eqn q hq := by
    have hwf := aggregateSchema_wellFormed hS hA
    obtain ⟨o, hl, hr⟩ := hwf.eqn_parallel q hq
    rw [Translation.mapPath_empty hl, Translation.mapPath_empty hr]
    have hq' : q ∈ S.internalSchema.eqns := by
      simp only [aggregateSchema, List.mem_filter] at hq
      exact mem_internalEqns.mpr ⟨hq.1, A, hA, hq.2⟩
    exact ⟨(internalSchema_wellFormed hS).eqn_src q hq',
      pathEq_of_mem_eqns (internalSchema_wellFormed hS) hq'⟩

/-- The aggregates, as an index type. -/
abbrev Aggs (S : Schema) : Type := { A : Aggregate // A ∈ S.allAggregates }

/-- The aggregate schemas cover the internal schema. -/
theorem aggregateCover (hS : S.WellFormed) (hne : S.entities ≠ []) :
    Cover S.internalSchema (fun A : S.Aggs => S.aggregateSchema A.1) where
  wf := internalSchema_wellFormed hS
  wf_part A := aggregateSchema_wellFormed hS A.2
  sub A := aggregate_valid hS A.2
  ob o ho := by
    cases o with
    | entity e =>
      obtain ⟨A, hA, he⟩ := exists_aggregate (S := S) ho
      exact ⟨⟨A, hA⟩, List.mem_append_left _ he⟩
    | value =>
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨A, hA, -⟩ := exists_aggregate (S := S) he
      exact ⟨⟨A, hA⟩, trivial⟩
  gen {o x n} h := by
    obtain ⟨e, rfl, -⟩ := exists_gen_of_step? h
    have he : e ∈ S.entities := isOb_src_of_step? (internalSchema_wellFormed hS) h
    obtain ⟨A, hA, heA⟩ := exists_aggregate (S := S) he
    exact ⟨⟨A, hA⟩,
      (step?_aggregate heA n).trans ((step?_internalSchema S _ _).symm.trans h)⟩
  eqn q hq := by
    obtain ⟨hq, A, hA, hi⟩ := mem_internalEqns.mp hq
    exact ⟨⟨A, hA⟩, List.mem_filter.mpr ⟨hq, hi⟩⟩

/-- A path has the same names in `S` and in its internal schema. -/
theorem names_internalSchema {a : S.Obj} :
    ∀ {b : S.Obj} (p : Quiver.Path a b), @names S.internalSchema a b p = @names S a b p
  | _, .nil => rfl
  | _, .cons p e => congrArg (· ++ [e.1]) (names_internalSchema p)

/-! ## Restrictions of one functor agree -/

/-- The restrictions of one functor out of `G` to the parts of a cover agree. -/
theorem Cover.agree_restrict {G : Schema} {ι : Type*} {B : ι → Schema} (hC : Cover G B)
    {X : Type*} [Category X] (F : G.cat ⥤ X) : Agree B fun i => hC.leg i ⋙ F where
  ob i j o hi hj := by
    simp only [Cover.leg, Functor.comp_obj, Translation.functor_obj, Translation.obj_empty]
  gen i j a b n hai hbi haj hbj hi hj := by
    have hG : G.step? a n = some b := step?_of_sub (hC.sub i) hi
    have ha : G.IsOb a := isOb_src_of_step? hC.wf hG
    have hb : G.IsOb b := isOb_of_step? hC.wf hG
    simp only [Cover.leg, Functor.comp_map]
    rw [Translation.functor_empty_genMor hC.wf (hC.sub i) n hi ha hb hG,
      Translation.functor_empty_genMor hC.wf (hC.sub j) n hj ha hb hG]

/-! ## States of the internal schema as families of aggregate states -/

section States

variable {K : ValueType → Type}

/-- A family of states of the aggregate schemas is compatible when the states agree
where the aggregate schemas overlap, on the identities and the values, and their
bijections to `K` agree on each value type. -/
structure Compatible (X : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K) : Prop where
  agree : Agree (fun A : S.Aggs => S.aggregateSchema A.1) fun A => (X A).F
  values : ∀ (A A' : S.Aggs) (v : ValueType)
    (x : (X A).F.obj ((S.aggregateSchema A.1).obj ⟨.value v, trivial⟩)),
    (X A').values v (cast (agree.ob A A' (.value v) trivial trivial) x) = (X A).values v x

variable (hS : S.WellFormed) (hne : S.entities ≠ [])

/-- The restrictions of a state of the internal schema to the aggregate schemas. -/
def parts (Y : S.internalSchema.State K) : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K :=
  fun A => Translation.restrictState (internalSchema_wellFormed hS) (aggregate_valid hS A.2) Y

include hne in
/-- The restrictions of a state of the internal schema are compatible. -/
theorem compatible_parts (Y : S.internalSchema.State K) : Compatible (parts hS Y) where
  agree := (aggregateCover hS hne).agree_restrict Y.F
  values _ _ _ _ := rfl

/-- The state of the internal schema glued from a compatible family. -/
noncomputable def glueParts (X : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K)
    (h : Compatible X) : S.internalSchema.State K where
  F := (aggregateCover hS hne).desc h.agree
  values v := (X ((aggregateCover hS hne).partOb ⟨.value v, trivial⟩)).values v

/-- Consistency inside the aggregates: a state of the internal schema is a
compatible family of states of the aggregate schemas, its restrictions. -/
noncomputable def familyEquiv :
    S.internalSchema.State K ≃ { X : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K //
      Compatible X } where
  toFun Y := ⟨parts hS Y, compatible_parts hS hne Y⟩
  invFun X := glueParts hS hne X.1 X.2
  left_inv Y := State.ext'
    ((aggregateCover hS hne).desc_unique (compatible_parts hS hne Y).agree Y.F
      fun _ => rfl).symm fun _ _ => rfl
  right_inv X := by
    obtain ⟨X, h⟩ := X
    refine Subtype.ext (funext fun A => State.ext' ((aggregateCover hS hne).leg_desc h.agree A)
      fun v x => ?_)
    exact h.values _ A v x

/-! ## States of the context as states of the internal schema -/

/-- The functor `G` sends the two sides of the equation `q` to the same
morphism. -/
def Satisfies {T : Schema} {X : Type*} [Category X] (G : T.cat ⥤ X) (q : Equation) : Prop :=
  ∀ (a b : T.Obj) (p p' : Quiver.Path a b), a.1 = .entity q.src → names p = q.lhs →
    names p' = q.rhs → G.map (mor p) = G.map (mor p')

variable (S) in
/-- The functor from the internal schema category to the schema category: the
identity on paths, which also identifies the two sides of each equation across
aggregates. -/
def toContext : S.internalSchema.cat ⥤ S.cat :=
  CategoryTheory.Quotient.lift _ (CategoryTheory.Quotient.functor S.rel) (by
    rintro a b f g ⟨q, hq, ha, h₁, h₂⟩
    exact CategoryTheory.Quotient.sound _ ⟨q, (mem_internalEqns.mp hq).1, ha,
      (names_internalSchema (S := S) f).symm.trans h₁,
      (names_internalSchema (S := S) g).symm.trans h₂⟩)

/-- A functor out of the internal schema category that satisfies the equations
across aggregates, as a functor out of the schema category. -/
def liftCross {X : Type*} [Category X] (G : S.internalSchema.cat ⥤ X)
    (hG : ∀ q ∈ S.crossAggregateEqns, Satisfies G q) : S.cat ⥤ X :=
  CategoryTheory.Quotient.lift _ (CategoryTheory.Quotient.functor S.internalSchema.rel ⋙ G) (by
    rintro a b f g ⟨q, hq, ha, h₁, h₂⟩
    rcases mem_internalEqns_or_cross hq with hi | hc
    · exact congrArg G.map (CategoryTheory.Quotient.sound _ ⟨q, hi, ha,
        (names_internalSchema f).trans h₁, (names_internalSchema g).trans h₂⟩)
    · exact hG q hc a b f g ha ((names_internalSchema f).trans h₁)
        ((names_internalSchema g).trans h₂))

section Lift

variable {X : Type*} [Category X]

theorem toContext_liftCross (G : S.internalSchema.cat ⥤ X)
    (hG : ∀ q ∈ S.crossAggregateEqns, Satisfies G q) : S.toContext ⋙ liftCross G hG = G :=
  CategoryTheory.Quotient.lift_unique' _ _ _ rfl

theorem liftCross_unique (G : S.internalSchema.cat ⥤ X)
    (hG : ∀ q ∈ S.crossAggregateEqns, Satisfies G q) (G' : S.cat ⥤ X)
    (h : S.toContext ⋙ G' = G) : G' = liftCross G hG := by
  subst h
  exact CategoryTheory.Quotient.lift_unique' _ _ _ rfl

/-- A functor out of the schema category satisfies every equation of `S` on the
internal schema category. -/
theorem satisfies_toContext (G' : S.cat ⥤ X) {q : Equation} (hq : q ∈ S.eqns) :
    Satisfies (S.toContext ⋙ G') q := fun _ _ p p' ha h₁ h₂ =>
  congrArg G'.map (CategoryTheory.Quotient.sound S.rel ⟨q, hq, ha,
    (names_internalSchema (S := S) p).symm.trans h₁,
    (names_internalSchema (S := S) p').symm.trans h₂⟩)

end Lift

/-- Consistency across the aggregates: a state of `S` is a state of the internal
schema in which the equations across aggregates hold. -/
def crossEquiv :
    S.State K ≃ { Y : S.internalSchema.State K //
      ∀ q ∈ S.crossAggregateEqns, Satisfies Y.F q } where
  toFun Z := ⟨⟨S.toContext ⋙ Z.F, Z.values⟩, fun _ hq =>
    satisfies_toContext Z.F (mem_crossAggregateEqns.mp hq).1⟩
  invFun Y := ⟨liftCross Y.1.F Y.2, Y.1.values⟩
  left_inv Z := State.ext' (liftCross_unique _ (fun _ hq =>
    satisfies_toContext Z.F (mem_crossAggregateEqns.mp hq).1) Z.F rfl).symm fun _ _ => rfl
  right_inv Y := Subtype.ext (State.ext' (toContext_liftCross Y.1.F Y.2) fun _ _ => rfl)

/-- Consistency of a context: a state of `S` is a compatible family of states of the
aggregate schemas whose glued state satisfies the equations across aggregates. -/
noncomputable def contextEquiv :
    S.State K ≃ { X : { X : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K // Compatible X } //
      ∀ q ∈ S.crossAggregateEqns, Satisfies ((familyEquiv hS hne).symm X).F q } :=
  crossEquiv.trans (Equiv.subtypeEquiv (familyEquiv hS hne) fun Y => by
    rw [Equiv.symm_apply_apply])

end States

end Schema

end DDD
