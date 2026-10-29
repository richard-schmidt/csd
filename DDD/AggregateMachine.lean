import DDD.Aggregates
import DDD.OpenMachine

/-!
# Machines on aggregates

A context runs as a machine per aggregate, side by side. A step changes one
aggregate and is checked against its own schema; the rules across aggregates are
reported between steps instead of refused.

- `FinState.violations S X`: the failures of the check of `X` against `S`, one
  by one: a missing column, a reference to an entity that does not exist
  (`dangling`), a value of the wrong type, an equation that fails at an entity.
  There are none exactly when the check passes (`violations_eq_nil_iff`).
- `FinState.glueFamily S F`: the finite state of the context glued from a finite
  state of each aggregate. Each entity type takes its entities from the
  aggregate it belongs to, each generator its column from the aggregate of its
  source. The identities an aggregate holds are bounds on its references, not
  data of the context.
- When each aggregate state passes the check of its aggregate schema, every
  violation of the glued state is a rule across aggregates (`Schema.Across`): a
  reference that leaves its aggregate and finds no entity there, or an equation
  across aggregates that fails (`violations_glue`).
- `CheckedState.parts`: a checked state of the context restricts to a checked
  state of each aggregate, and the parts glue back to its normal form
  (`glue_parts`), with no violation (`violations_parts`).
- `aggregateMachine`: a command proposes a new state of one aggregate, taken when
  it passes the check of the aggregate schema. `dispatch` runs machines side by
  side, one input at a time; `contextMachine` wires the aggregate machines so
  that the context shows the violations of the glued state.
-/

namespace DDD

open CategoryTheory Production CyberPhy Optics Schema

/-- A failure of the check of a finite state against a schema. -/
inductive Violation where
  /-- The column of the generator `name` out of `src` is missing or has the wrong
  length. -/
  | column (src name : String)
  /-- Entity `i` of `src` refers along `name` to entity `j` of the target, which
  does not exist. -/
  | dangling (src name : String) (i j : Nat)
  /-- The value of entity `i` of `src` along the attribute `name` has the wrong
  value type. -/
  | valueType (src name : String) (i : Nat)
  /-- The equation `q` fails at entity `i` of its source. -/
  | eqn (q : Equation) (i : Nat)
deriving DecidableEq, Repr

theorem filterMap_zipIdx_eq_nil {α β : Type} {c : List α} {g : α × Nat → Option β}
    {p : α → Prop} (hg : ∀ x, g x = none ↔ p x.1) :
    c.zipIdx.filterMap g = [] ↔ ∀ a ∈ c, p a := by
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h a ha
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    exact (hg (a, i)).mp (h (a, i) (List.mem_zipIdx_iff_getElem?.mpr hi))
  · intro h x hx
    exact (hg x).mpr (h x.1 (List.fst_mem_of_mem_zipIdx hx))

namespace FinState

variable {K : ValueType → Type} [∀ v, DecidableEq (K v)] (X : FinState K)

/-- The failures of the column of the reference `r`. -/
def refViolations (r : Ref) : List Violation :=
  match X.refCol r.src r.name with
  | some c =>
    if c.length = X.size r.src then
      c.zipIdx.filterMap fun x =>
        if x.1 < X.size r.tgt then none else some (.dangling r.src r.name x.2 x.1)
    else [.column r.src r.name]
  | none => [.column r.src r.name]

/-- The failures of the column of the attribute `a`. -/
def attrViolations (a : Attr) : List Violation :=
  match X.attrCol a.src a.name with
  | some c =>
    if c.length = X.size a.src then
      c.zipIdx.filterMap fun x => if x.1.1 = a.tgt then none else some (.valueType a.src a.name x.2)
    else [.column a.src a.name]
  | none => [.column a.src a.name]

/-- The entities at which the equation `q` fails. -/
def eqnViolations (S : Schema) (q : Equation) : List Violation :=
  (List.range (X.size q.src)).filterMap fun i =>
    if X.eval S (.ent q.src i) q.lhs = X.eval S (.ent q.src i) q.rhs then none
    else some (.eqn q i)

/-- The failures of the check of `X` against `S`. -/
def violations (S : Schema) : List Violation :=
  S.refs.flatMap X.refViolations ++ S.attrs.flatMap X.attrViolations ++
    S.eqns.flatMap (X.eqnViolations S)

omit [∀ v, DecidableEq (K v)] in
theorem refViolations_eq_nil (r : Ref) : X.refViolations r = [] ↔
    (match X.refCol r.src r.name with
      | some c => c.length == X.size r.src && c.all (· < X.size r.tgt)
      | none => false) = true := by
  unfold refViolations
  split
  · rename_i c _
    by_cases h : c.length = X.size r.src
    · rw [if_pos h, filterMap_zipIdx_eq_nil (p := fun j => j < X.size r.tgt)
        fun x => by split <;> simp_all]
      simp [h]
    · simp [h]
  · simp

omit [∀ v, DecidableEq (K v)] in
theorem attrViolations_eq_nil (a : Attr) : X.attrViolations a = [] ↔
    (match X.attrCol a.src a.name with
      | some c => c.length == X.size a.src && c.all (·.1 == a.tgt)
      | none => false) = true := by
  unfold attrViolations
  split
  · rename_i c _
    by_cases h : c.length = X.size a.src
    · rw [if_pos h, filterMap_zipIdx_eq_nil (p := fun x => x.1 = a.tgt)
        fun x => by split <;> simp_all]
      simp [h]
    · simp [h]
  · simp

theorem eqnViolations_eq_nil (S : Schema) (q : Equation) : X.eqnViolations S q = [] ↔
    ∀ i ∈ List.range (X.size q.src),
      decide (X.eval S (.ent q.src i) q.lhs = X.eval S (.ent q.src i) q.rhs) = true := by
  rw [eqnViolations, List.filterMap_eq_nil_iff]
  refine forall₂_congr fun i _ => ?_
  split <;> simp_all

/-- A finite state has no violation exactly when it passes the check. -/
theorem violations_eq_nil_iff (S : Schema) : X.violations S = [] ↔ X.check S = true := by
  simp only [violations, check, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    Bool.and_eq_true, List.all_eq_true]
  exact and_congr (and_congr (forall₂_congr fun r _ => X.refViolations_eq_nil r)
    (forall₂_congr fun a _ => X.attrViolations_eq_nil a))
    (forall₂_congr fun q _ => X.eqnViolations_eq_nil S q)

end FinState

namespace Schema

variable (S : Schema)

/-- The aggregate the entity type `e` belongs to. -/
def ownerOf (e : String) : Option S.Aggs :=
  S.allAggregates.attach.find? fun A => decide (e ∈ A.1.entities)

/-- A violation of a rule across aggregates: a reference out of an aggregate whose
target lies outside it, or an equation across aggregates. -/
def Across : Violation → Prop
  | .dangling src name _ _ => ∃ r ∈ S.refs, r.src = src ∧ r.name = name ∧
      ∃ A ∈ S.allAggregates, r.src ∈ A.entities ∧ r.tgt ∉ A.entities
  | .eqn q _ => q ∈ S.crossAggregateEqns
  | _ => False

variable {S}

theorem ownerOf_eq (hS : S.WellFormed) {A : Aggregate} (hA : A ∈ S.allAggregates) {e : String}
    (he : e ∈ A.entities) : S.ownerOf e = some ⟨A, hA⟩ := by
  have hsome : (S.ownerOf e).isSome :=
    List.find?_isSome.mpr ⟨⟨A, hA⟩, List.mem_attach _ _, decide_eq_true he⟩
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hB
  rw [hB]
  exact congrArg some (Subtype.ext (eq_of_mem_entities hS B.2 hA (of_decide_eq_true hp) he))

end Schema

namespace FinState

variable {K : ValueType → Type} {S : Schema}

/-- The state, in the family `F`, of the aggregate the entity type `e` belongs
to. -/
def partOf (F : S.Aggs → FinState K) (e : String) : FinState K :=
  match S.ownerOf e with
  | some A => F A
  | none => ⟨[], [], []⟩

end FinState

namespace Schema

open FinState

variable {K : ValueType → Type} (S : Schema)

/-- The finite state of the context glued from a finite state of each aggregate:
the entities of each entity type from the aggregate it belongs to, and the column
of each generator from the aggregate of its source. -/
def glueFamily (F : S.Aggs → FinState K) : FinState K where
  sizes := S.entities.map fun e => (e, (partOf F e).size e)
  refs := S.refs.map fun r => ((r.src, r.name), ((partOf F r.src).refCol r.src r.name).getD [])
  attrs := S.attrs.map fun a =>
    ((a.src, a.name), ((partOf F a.src).attrCol a.src a.name).getD [])

end Schema

namespace FinState

variable {K : ValueType → Type} {S : Schema}

variable {F : S.Aggs → FinState K}

theorem partOf_eq (hS : S.WellFormed) {A : Aggregate} (hA : A ∈ S.allAggregates) {e : String}
    (he : e ∈ A.entities) : partOf F e = F ⟨A, hA⟩ := by
  simp [partOf, ownerOf_eq hS hA he]

theorem size_glue {e : String} (he : e ∈ S.entities) :
    (S.glueFamily F).size e = (partOf F e).size e := by
  have := lookup_map_key (fun e => e) (fun e => (partOf F e).size e) S.entities (b := e)
    (by simpa using he)
  change ((S.glueFamily F).sizes.lookup e).getD 0 = _
  simp only [glueFamily]
  rw [this]
  rfl

theorem refCol_glue {r : Ref} (hr : r ∈ S.refs) :
    (S.glueFamily F).refCol r.src r.name =
      some (((partOf F r.src).refCol r.src r.name).getD []) :=
  lookup_map_key (fun r : Ref => (r.src, r.name))
    (fun k => ((partOf F k.1).refCol k.1 k.2).getD []) S.refs (List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem attrCol_glue {a : Attr} (ha : a ∈ S.attrs) :
    (S.glueFamily F).attrCol a.src a.name =
      some (((partOf F a.src).attrCol a.src a.name).getD []) :=
  lookup_map_key (fun a : Attr => (a.src, a.name))
    (fun k => ((partOf F k.1).attrCol k.1 k.2).getD []) S.attrs (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- A step along a generator ending at an entity follows a reference of the
schema. -/
theorem step?_of_step_ent {X : FinState K} {T : Schema} {e e' : String} {i j : Nat} {n : String}
    (h : X.step T (.ent e i) n = some (.ent e' j)) : T.step? (.entity e) n = some (.entity e') := by
  simp only [step] at h
  split at h
  · rename_i r hr
    obtain ⟨j', -, hj'⟩ := Option.map_eq_some_iff.mp h
    cases hj'
    simp [Schema.step?, hr]
  · split at h
    · obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.mp h
      cases hx
    · cases h

variable (hS : S.WellFormed) {A : Aggregate} (hA : A ∈ S.allAggregates)

include hS in
/-- Out of an entity type of an aggregate, the glued state steps as the state of
the aggregate does. -/
theorem step_glue {e : String} (he : e ∈ A.entities) (i : Nat) (n : String) :
    (S.glueFamily F).step S (.ent e i) n =
      (F ⟨A, hA⟩).step (S.aggregateSchema A) (.ent e i) n := by
  simp only [step, ref?_aggregate he, attr?_aggregate he]
  cases hr : S.ref? e n with
  | some r =>
    obtain ⟨hrm, rfl, rfl⟩ := ref?_spec hr
    simp only
    rw [refCol_glue hrm, partOf_eq hS hA he]
    cases (F ⟨A, hA⟩).refCol r.src r.name <;> simp
  | none =>
    simp only
    cases ha : S.attr? e n with
    | some a =>
      obtain ⟨ham, rfl, rfl⟩ := attr?_spec ha
      simp only
      rw [attrCol_glue ham, partOf_eq hS hA he]
      cases (F ⟨A, hA⟩).attrCol a.src a.name <;> simp
    | none => rfl

include hS in
/-- Along a path of an aggregate schema, the glued state evaluates as the state of
the aggregate does. -/
theorem eval_glue (l : List String) :
    ∀ {e : String} (i : Nat), e ∈ A.entities →
      ((S.aggregateSchema A).tgt? (.entity e) l).isSome →
      (S.glueFamily F).eval S (.ent e i) l =
        (F ⟨A, hA⟩).eval (S.aggregateSchema A) (.ent e i) l := by
  induction l with
  | nil => intro _ _ _ _; rfl
  | cons n ns ih =>
    intro e i he hl
    simp only [eval]
    rw [step_glue hS hA he]
    rw [tgt?_cons] at hl
    obtain ⟨o₁, hs⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind hl)
    rw [hs, Option.bind_some] at hl
    cases hy : (F ⟨A, hA⟩).step (S.aggregateSchema A) (.ent e i) n with
    | none => rfl
    | some y =>
      simp only [Option.bind_some]
      cases ns with
      | nil => rfl
      | cons n' ns' =>
        cases y with
        | val => rfl
        | ent e' j =>
          obtain rfl : o₁ = .entity e' := Option.some.inj (hs.symm.trans (step?_of_step_ent hy))
          have he' : e' ∈ A.entities := by
            rw [tgt?_cons] at hl
            obtain ⟨o₂, hs₂⟩ :=
              Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind hl)
            obtain ⟨⟨e'', he'', he''A⟩, -⟩ := step?_of_aggregate hs₂
            cases he''
            exact he''A
          exact ih j he' hl

end FinState

section Glue

variable {K : ValueType → Type} [∀ v, DecidableEq (K v)] {S : Schema}

open FinState in
/-- When each aggregate state passes the check of its aggregate schema, every
violation of the glued state is a rule across aggregates: a reference that leaves
its aggregate and finds no entity, or an equation across aggregates that fails. -/
theorem violations_glue (hS : S.WellFormed)
    (F : ∀ A : S.Aggs, CheckedState K (S.aggregateSchema A.1)) :
    ∀ x ∈ (S.glueFamily fun A => (F A).1).violations S, S.Across x := by
  intro x hx
  simp only [violations, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (⟨r, hr, hx⟩ | ⟨a, ha, hx⟩) | ⟨q, hq, hx⟩
  · have hsrc := hS.ref_src r hr
    obtain ⟨A, hA, hsA⟩ := exists_aggregate hsrc
    have hrA : r ∈ (S.aggregateSchema A).refs :=
      List.mem_filter.mpr ⟨hr, decide_eq_true hsA⟩
    obtain ⟨c, hc, hlen, hlt⟩ := check_ref (F ⟨A, hA⟩).2 hrA
    have hcol : (S.glueFamily fun A => (F A).1).refCol r.src r.name = some c := by
      rw [refCol_glue hr, partOf_eq hS hA hsA, hc]
      rfl
    have hsize : c.length = (S.glueFamily fun A => (F A).1).size r.src := by
      rw [size_glue hsrc, partOf_eq hS hA hsA, hlen]
    simp only [refViolations, hcol, if_pos hsize] at hx
    obtain ⟨⟨j, i⟩, hmem, hx⟩ := List.mem_filterMap.mp hx
    split at hx
    · cases hx
    · rename_i hge
      cases hx
      refine ⟨r, hr, rfl, rfl, A, hA, hsA, fun htA => hge ?_⟩
      rw [size_glue (hS.ref_tgt r hr), partOf_eq hS hA htA]
      exact hlt j (List.fst_mem_of_mem_zipIdx hmem)
  · have hsrc := hS.attr_src a ha
    obtain ⟨A, hA, hsA⟩ := exists_aggregate hsrc
    have haA : a ∈ (S.aggregateSchema A).attrs :=
      List.mem_filter.mpr ⟨ha, decide_eq_true hsA⟩
    obtain ⟨c, hc, hlen, hty⟩ := check_attr (F ⟨A, hA⟩).2 haA
    have hcol : (S.glueFamily fun A => (F A).1).attrCol a.src a.name = some c := by
      rw [attrCol_glue ha, partOf_eq hS hA hsA, hc]
      rfl
    have hsize : c.length = (S.glueFamily fun A => (F A).1).size a.src := by
      rw [size_glue hsrc, partOf_eq hS hA hsA, hlen]
    simp only [attrViolations, hcol, if_pos hsize] at hx
    obtain ⟨⟨y, i⟩, hmem, hx⟩ := List.mem_filterMap.mp hx
    rw [if_pos (hty y (List.fst_mem_of_mem_zipIdx hmem))] at hx
    cases hx
  · simp only [eqnViolations, List.mem_filterMap, List.mem_range] at hx
    obtain ⟨i, hi, hx⟩ := hx
    split at hx
    · cases hx
    · rename_i hne
      cases hx
      rcases mem_internalEqns_or_cross hq with hint | hcross
      · exfalso
        obtain ⟨-, A, hA, hqA⟩ := mem_internalEqns.mp hint
        simp only [internal, Bool.and_eq_true, decide_eq_true_eq] at hqA
        obtain ⟨⟨hsA, hl⟩, hr⟩ := hqA
        rw [← tgt?_aggregateSchema] at hl hr
        have hqm : q ∈ (S.aggregateSchema A).eqns := by
          refine List.mem_filter.mpr ⟨hq, ?_⟩
          simp only [internal, Bool.and_eq_true, decide_eq_true_eq]
          rw [← tgt?_aggregateSchema, ← tgt?_aggregateSchema]
          exact ⟨⟨hsA, hl⟩, hr⟩
        have hi' : i < (F ⟨A, hA⟩).1.size q.src := by
          rwa [size_glue (hS.eqn_src q hq), partOf_eq hS hA hsA] at hi
        apply hne
        rw [eval_glue hS hA _ i hsA hl, eval_glue hS hA _ i hsA hr]
        exact check_eqn (F ⟨A, hA⟩).2 hqm hi'
      · exact hcross

/-! ## The parts of a state of the context -/

/-- The inclusion of an aggregate schema in the schema. -/
theorem aggregate_valid_context (hS : S.WellFormed) (A : S.Aggs) :
    ({} : Translation).Valid (S.aggregateSchema A.1) S :=
  Translation.empty_valid_trans (aggregateSchema_wellFormed hS A.2) hS (aggregate_valid hS A.2)
    (internal_valid hS)

/-- A checked state of the context, restricted to each aggregate. -/
def CheckedState.parts (hS : S.WellFormed) (X : CheckedState K S) :
    ∀ A : S.Aggs, CheckedState K (S.aggregateSchema A.1) :=
  fun A => X.restrict (aggregateSchema_wellFormed hS A.2) (aggregate_valid_context hS A)

theorem CheckedState.parts_val (hS : S.WellFormed) (X : CheckedState K S) (A : S.Aggs) :
    (X.parts hS A).1 = X.1.restrict {} (S.aggregateSchema A.1) S := rfl

open FinState in
/-- The parts of a checked state glue back to its normal form. -/
theorem glue_parts (hS : S.WellFormed) (X : CheckedState K S) :
    (S.glueFamily fun A => (X.parts hS A).1) = (X.normalize hS).1 := by
  have h : (X.normalize hS).1 =
      ⟨S.entities.map fun e => (e, X.1.size (({} : Translation).ent e)),
        S.refs.map fun r => ((r.src, r.name), X.1.refColumn {} S r.src r.name),
        S.attrs.map fun a => ((a.src, a.name), X.1.attrColumn {} S a.src a.name)⟩ := rfl
  rw [h]
  unfold Schema.glueFamily
  congr 1
  · refine List.map_congr_left fun e he => ?_
    obtain ⟨A, hA, heA⟩ := exists_aggregate he
    rw [partOf_eq hS hA heA, CheckedState.parts_val,
      size_restrict (S := S.aggregateSchema A) (List.mem_append_left _ heA)]
  · refine List.map_congr_left fun r hr => ?_
    obtain ⟨A, hA, hsA⟩ := exists_aggregate (hS.ref_src r hr)
    rw [partOf_eq hS hA hsA, CheckedState.parts_val,
      refCol_restrict (S := S.aggregateSchema A) (List.mem_filter.mpr ⟨hr, decide_eq_true hsA⟩)]
    rfl
  · refine List.map_congr_left fun a ha => ?_
    obtain ⟨A, hA, hsA⟩ := exists_aggregate (hS.attr_src a ha)
    rw [partOf_eq hS hA hsA, CheckedState.parts_val,
      attrCol_restrict (S := S.aggregateSchema A)
        (List.mem_filter.mpr ⟨ha, decide_eq_true hsA⟩)]
    rfl

/-- The parts of a checked state glue to a state with no violation. -/
theorem violations_parts (hS : S.WellFormed) (X : CheckedState K S) :
    (S.glueFamily fun A => (X.parts hS A).1).violations S = [] := by
  rw [glue_parts hS X]
  exact ((X.normalize hS).1.violations_eq_nil_iff S).mpr (X.normalize hS).2

end Glue

/-! ## Machines -/

/-- Machines side by side, one input at a time: an input names the machine it goes
to, which takes it; the other machines keep their state. The view is the views
of all. -/
def dispatch {ι : Type} [DecidableEq ι] {B : ι → Box} (M : ∀ i, Machine (B i)) :
    Machine ⟨Σ i, (B i).σᵢ, ∀ i, (B i).σₒ⟩ where
  state := ∀ i, (M i).state
  lens :=
    { view := fun s i => (M i).lens.view (s i)
      update := fun s c => Function.update s c.1 ((M c.1).lens.update (s c.1) c.2) }

section Dispatch

variable {ι : Type} [DecidableEq ι] {B : ι → Box} (M : ∀ i, Machine (B i))

/-- The machine an input names takes it. -/
theorem dispatch_update_self (s : (dispatch M).state) (i : ι) (c : (B i).σᵢ) :
    (dispatch M).lens.update s ⟨i, c⟩ i = (M i).lens.update (s i) c :=
  Function.update_self _ _ _

/-- The other machines keep their state. -/
theorem dispatch_update_ne (s : (dispatch M).state) {i j : ι} (h : j ≠ i) (c : (B i).σᵢ) :
    (dispatch M).lens.update s ⟨i, c⟩ j = s j :=
  Function.update_of_ne h _ _

end Dispatch

section Machines

variable {K : ValueType → Type} [∀ v, DecidableEq (K v)] {S : Schema}

variable (K) in
/-- A machine on the aggregate `A`: a command proposes a new finite state of the
aggregate, which the machine takes, in normal form, when it passes the check of
the aggregate schema; otherwise it keeps its state. -/
def aggregateMachine (hS : S.WellFormed) (A : S.Aggs) {C : Type}
    (propose : FinState K → C → FinState K) :
    Machine ⟨C, CheckedState K (S.aggregateSchema A.1)⟩ where
  state := CheckedState K (S.aggregateSchema A.1)
  lens :=
    { view := id
      update := fun s c =>
        if h : (propose s.1 c).check (S.aggregateSchema A.1) = true then
          CheckedState.normalize (aggregateSchema_wellFormed hS A.2) ⟨_, h⟩
        else s }

theorem aggregateMachine_update_of_check (hS : S.WellFormed) (A : S.Aggs) {C : Type}
    (propose : FinState K → C → FinState K) (s : CheckedState K (S.aggregateSchema A.1)) (c : C)
    (h : (propose s.1 c).check (S.aggregateSchema A.1) = true) :
    (aggregateMachine K hS A propose).lens.update s c =
      CheckedState.normalize (aggregateSchema_wellFormed hS A.2) ⟨_, h⟩ := dif_pos h

/-- A proposal that breaks a rule of the aggregate is refused. -/
theorem aggregateMachine_update_of_not_check (hS : S.WellFormed) (A : S.Aggs) {C : Type}
    (propose : FinState K → C → FinState K) (s : CheckedState K (S.aggregateSchema A.1)) (c : C)
    (h : ¬ (propose s.1 c).check (S.aggregateSchema A.1) = true) :
    (aggregateMachine K hS A propose).lens.update s c = s := dif_neg h

variable (K S) in
/-- The wiring of a context: commands pass to the aggregates they name, and the
context shows the violations of the state glued from the aggregate states. -/
def reportWiring (C : S.Aggs → Type) :
    (⟨Σ A, C A, ∀ A : S.Aggs, CheckedState K (S.aggregateSchema A.1)⟩ : Box) ⟶
      ⟨Σ A, C A, List Violation⟩ where
  in_comp p := p.2
  out_comp F := (S.glueFamily fun A => (F A).1).violations S

/-- The machine of a context: the aggregate machines side by side, one command at a
time, showing the violations of the glued state. -/
def contextMachine {C : S.Aggs → Type}
    (M : ∀ A : S.Aggs, Machine ⟨C A, CheckedState K (S.aggregateSchema A.1)⟩) :
    Machine ⟨Σ A, C A, List Violation⟩ :=
  wire (reportWiring K S C) (dispatch M)

variable {C : S.Aggs → Type}
  (M : ∀ A : S.Aggs, Machine ⟨C A, CheckedState K (S.aggregateSchema A.1)⟩)

/-- The context shows the violations of the state glued from what the aggregates
show. -/
theorem contextMachine_view (s : (contextMachine M).state) :
    (contextMachine M).lens.view s =
      (S.glueFamily fun A => ((M A).lens.view (s A)).1).violations S := rfl

/-- A command changes the aggregate it names, and only that one. -/
theorem contextMachine_update (s : (contextMachine M).state) (A : S.Aggs) (c : C A) :
    (contextMachine M).lens.update s ⟨A, c⟩ =
      Function.update s A ((M A).lens.update (s A) c) := rfl

/-- Everything the context reports is a rule across aggregates. -/
theorem contextMachine_across (hS : S.WellFormed) (s : (contextMachine M).state) :
    ∀ x ∈ (contextMachine M).lens.view s, S.Across x :=
  violations_glue hS fun A => (M A).lens.view (s A)

end Machines

end DDD
