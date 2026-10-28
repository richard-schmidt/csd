import DDD.Translation

/-!
# Gluing schemas

Strict integration is an explicit merge. `Schema.glue B₁ B₂` is the pushout of
two presentations along a common kernel `K` that both include with the same
names: the union of the generators, identified along the kernel, and the union of
the equations. `Schema.Gluable K B₁ B₂` states the conditions: `K` is included in
both, by the empty translation, and `B₁` and `B₂` share only entity types and
generators of `K`. `checkGluable` is its check.

A `Gluing` bundles a kernel, two schemas, and the conditions, with the legs
`inl` and `inr` of the glued schema and the square `ι₁ ⋙ inl = ι₂ ⋙ inr`.
-/

namespace DDD

open CategoryTheory

namespace Schema

/-- The generators of a schema, by source entity type and name. -/
def gens (S : Schema) : List (String × String) :=
  S.refs.map (fun r => (r.src, r.name)) ++ S.attrs.map (fun a => (a.src, a.name))

theorem mem_gens_iff {S : Schema} {e n : String} :
    (e, n) ∈ S.gens ↔ (S.ref? e n).isSome ∨ (S.attr? e n).isSome := by
  simp only [gens, List.mem_append, List.mem_map, Prod.mk.injEq, ref?, attr?,
    List.find?_isSome, Bool.and_eq_true, beq_iff_eq]

theorem step?_isSome_iff {S : Schema} {e n : String} :
    (S.step? (.entity e) n).isSome ↔ (e, n) ∈ S.gens := by
  rw [mem_gens_iff]
  simp only [step?]
  cases S.ref? e n <;> simp

/-- The members that aggregates in `A₂` with the root of `A` add to `A`. -/
def extraMembers (A : Aggregate) (A₂ : List Aggregate) : List Member :=
  (A₂.filter fun A' => A'.root == A.root).flatMap fun A' =>
    A'.members.filter fun m => m ∉ A.members

/-- The aggregates of a glued schema: those of the first schema, each with the
members the second schema gives the same root, then the aggregates of the second
schema with other roots. -/
def mergeAggregates (A₁ A₂ : List Aggregate) : List Aggregate :=
  A₁.map (fun A => ⟨A.root, A.members ++ extraMembers A A₂⟩) ++
    A₂.filter fun A => A.root ∉ A₁.map fun A' => A'.root

/-- `B₁` and `B₂` glued along what they share: the entity types and generators of
both, each once, and the equations of both. -/
def glue (B₁ B₂ : Schema) : Schema where
  entities := B₁.entities ++ B₂.entities.filter fun e => e ∉ B₁.entities
  refs := B₁.refs ++ B₂.refs.filter fun r => (r.src, r.name) ∉ B₁.gens
  attrs := B₁.attrs ++ B₂.attrs.filter fun a => (a.src, a.name) ∉ B₁.gens
  eqns := B₁.eqns ++ B₂.eqns
  aggregates := mergeAggregates B₁.aggregates B₂.aggregates

variable {B₁ B₂ : Schema}

theorem glue_ref?_of_mem {e n : String} (h : (e, n) ∈ B₁.gens) :
    (glue B₁ B₂).ref? e n = B₁.ref? e n := by
  have hnone : (B₂.refs.filter fun r => (r.src, r.name) ∉ B₁.gens).find?
      (fun r => r.src == e && r.name == n) = none := by
    rw [List.find?_eq_none]
    intro r hr hq
    simp only [List.mem_filter, decide_eq_true_eq] at hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact hr.2 h
  simp only [ref?, glue, List.find?_append, hnone, Option.or_none]

theorem glue_ref?_of_not_mem {e n : String} (h : (e, n) ∉ B₁.gens) :
    (glue B₁ B₂).ref? e n = B₂.ref? e n := by
  have h₁ : B₁.ref? e n = none := by
    rw [mem_gens_iff] at h
    simpa using (not_or.mp h).1
  simp only [ref?] at h₁ ⊢
  simp only [glue, List.find?_append, List.find?_filter, h₁, Option.none_or]
  congr 1
  funext r
  by_cases hr : r.src = e ∧ r.name = n
  · obtain ⟨rfl, rfl⟩ := hr
    simp [h]
  · have hf : (r.src == e && r.name == n) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hr hc
    simp [hf]

theorem glue_attr?_of_mem {e n : String} (h : (e, n) ∈ B₁.gens) :
    (glue B₁ B₂).attr? e n = B₁.attr? e n := by
  have hnone : (B₂.attrs.filter fun a => (a.src, a.name) ∉ B₁.gens).find?
      (fun a => a.src == e && a.name == n) = none := by
    rw [List.find?_eq_none]
    intro a ha hq
    simp only [List.mem_filter, decide_eq_true_eq] at ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact ha.2 h
  simp only [attr?, glue, List.find?_append, hnone, Option.or_none]

theorem glue_attr?_of_not_mem {e n : String} (h : (e, n) ∉ B₁.gens) :
    (glue B₁ B₂).attr? e n = B₂.attr? e n := by
  have h₁ : B₁.attr? e n = none := by
    rw [mem_gens_iff] at h
    simpa using (not_or.mp h).2
  simp only [attr?] at h₁ ⊢
  simp only [glue, List.find?_append, List.find?_filter, h₁, Option.none_or]
  congr 1
  funext a
  by_cases ha : a.src = e ∧ a.name = n
  · obtain ⟨rfl, rfl⟩ := ha
    simp [h]
  · have hf : (a.src == e && a.name == n) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ha hc
    simp [hf]

/-- A generator of the glued schema is a generator of the first schema, or else of
the second. -/
theorem glue_step? (o : Ob) (n : String) :
    (glue B₁ B₂).step? o n = (B₁.step? o n).or (B₂.step? o n) := by
  cases o with
  | value => rfl
  | entity e =>
    by_cases h : (e, n) ∈ B₁.gens
    · have hs := step?_isSome_iff.mpr h
      simp only [step?, glue_ref?_of_mem h, glue_attr?_of_mem h] at hs ⊢
      cases hB : B₁.ref? e n <;> cases hA : B₁.attr? e n <;> simp_all
    · have hs : B₁.step? (.entity e) n = none := by
        simpa [← step?_isSome_iff] using h
      rw [hs, Option.none_or]
      simp only [step?, glue_ref?_of_not_mem h, glue_attr?_of_not_mem h]

theorem glue_tgt?_of_left : ∀ {o x : Ob} {l : List String}, B₁.tgt? o l = some x →
    (glue B₁ B₂).tgt? o l = some x
  | _, _, [], h => h
  | o, x, n :: ns, h => by
    cases hs : B₁.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [tgt?_cons, hs, Option.bind_some] at h
      simp [glue_step?, hs, glue_tgt?_of_left h]

/-! ## The conditions for gluing -/

/-- `B₁` and `B₂` can be glued along `K`: the empty translation includes `K` in
both, and they share only entity types and generators of `K`. -/
structure Gluable (K B₁ B₂ : Schema) : Prop where
  left : ({} : Translation).Valid K B₁
  right : ({} : Translation).Valid K B₂
  entities : ∀ e ∈ B₁.entities, e ∈ B₂.entities → e ∈ K.entities
  gens : ∀ g ∈ B₁.gens, g ∈ B₂.gens → g ∈ K.gens

/-- The check for `Gluable`. -/
def checkGluable (K B₁ B₂ : Schema) : Bool :=
  ({} : Translation).checkValid K B₁ B₁.pathEq &&
  ({} : Translation).checkValid K B₂ B₂.pathEq &&
  B₁.entities.all (fun e => !decide (e ∈ B₂.entities) || decide (e ∈ K.entities)) &&
  B₁.gens.all (fun g => !decide (g ∈ B₂.gens) || decide (g ∈ K.gens))

theorem checkGluable_sound {K : Schema} (h₁ : B₁.WellFormed) (h₂ : B₂.WellFormed)
    (h : checkGluable K B₁ B₂ = true) : Gluable K B₁ B₂ := by
  simp only [checkGluable, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, hr⟩, he⟩, hg⟩ := h
  exact ⟨Translation.checkValid_sound (fun a _ _ h => pathEq_sound h₁ a h) hl,
    Translation.checkValid_sound (fun a _ _ h => pathEq_sound h₂ a h) hr,
    fun e h₁ h₂ => (he e h₁).resolve_left (not_not.mpr h₂),
    fun g h₁ h₂ => (hg g h₁).resolve_left (not_not.mpr h₂)⟩

/-- Where both schemas have a generator, it has the same target in both. -/
theorem Gluable.step?_eq {K : Schema} (h : Gluable K B₁ B₂) {o x y : Ob} {n : String}
    (h₁ : B₁.step? o n = some x) (h₂ : B₂.step? o n = some y) : x = y := by
  cases o with
  | value => simp [step?] at h₁
  | entity e =>
    have hk := h.gens (e, n) (step?_isSome_iff.mp (by simp [h₁]))
      (step?_isSome_iff.mp (by simp [h₂]))
    simp only [Schema.gens, List.mem_append, List.mem_map, Prod.mk.injEq] at hk
    rcases hk with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · have e₁ := h.left.ref r hr
      have e₂ := h.right.ref r hr
      simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton] at e₁ e₂
      exact Option.some.inj (h₁.symm.trans (e₁.trans (e₂.symm.trans h₂)))
    · have e₁ := h.left.attr a ha
      have e₂ := h.right.attr a ha
      simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton] at e₁ e₂
      exact Option.some.inj (h₁.symm.trans (e₁.trans (e₂.symm.trans h₂)))

theorem Gluable.glue_step?_of_right {K : Schema} (h : Gluable K B₁ B₂) {o x : Ob}
    {n : String} (h₂ : B₂.step? o n = some x) : (glue B₁ B₂).step? o n = some x := by
  rw [glue_step?, h₂]
  cases h₁ : B₁.step? o n with
  | none => rfl
  | some y => rw [h.step?_eq h₁ h₂]; rfl

theorem Gluable.glue_tgt?_of_right {K : Schema} (h : Gluable K B₁ B₂) :
    ∀ {o x : Ob} {l : List String}, B₂.tgt? o l = some x → (glue B₁ B₂).tgt? o l = some x
  | _, _, [], hl => hl
  | o, x, n :: ns, hl => by
    cases hs : B₂.step? o n with
    | none => simp [hs] at hl
    | some o' =>
      simp only [tgt?_cons, hs, Option.bind_some] at hl
      simp [h.glue_step?_of_right hs, h.glue_tgt?_of_right hl]

end Schema

/-! ## Gluings and their legs -/

/-- A gluing of `left` and `right` along `kernel`, with the conditions the bridge
theorem needs. -/
structure Gluing where
  kernel : Schema
  left : Schema
  right : Schema
  wf_kernel : kernel.WellFormed
  wf_left : left.WellFormed
  wf_right : right.WellFormed
  wf_glued : (Schema.glue left right).WellFormed
  gluable : Schema.Gluable kernel left right

namespace Gluing

open Schema

variable (D : Gluing)

/-- The glued schema. -/
abbrev glued : Schema := glue D.left D.right

theorem inl_valid : ({} : Translation).Valid D.left D.glued where
  entity e he := List.mem_append_left _ he
  ref r hr := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton, glue_step?,
      step?_of_mem_refs D.wf_left hr, Option.some_or]
  attr a ha := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton, glue_step?,
      step?_of_mem_attrs D.wf_left ha, Option.some_or]
  eqn q hq := by
    obtain ⟨o, hl, hr⟩ := D.wf_left.eqn_parallel q hq
    rw [Translation.mapPath_empty hl, Translation.mapPath_empty hr]
    exact ⟨_, pathEq_of_mem_eqns D.wf_glued (List.mem_append_left _ hq)⟩

theorem inr_valid : ({} : Translation).Valid D.right D.glued where
  entity e he := by
    by_cases h : e ∈ D.left.entities
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨he, by simpa using h⟩)
  ref r hr := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    exact D.gluable.glue_step?_of_right (step?_of_mem_refs D.wf_right hr)
  attr a ha := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    exact D.gluable.glue_step?_of_right (step?_of_mem_attrs D.wf_right ha)
  eqn q hq := by
    obtain ⟨o, hl, hr⟩ := D.wf_right.eqn_parallel q hq
    rw [Translation.mapPath_empty hl, Translation.mapPath_empty hr]
    exact ⟨_, pathEq_of_mem_eqns D.wf_glued (List.mem_append_right _ hq)⟩

/-- The kernel in the first schema. -/
def ι₁ : D.kernel.cat ⥤ D.left.cat := Translation.functor D.wf_left D.gluable.left

/-- The kernel in the second schema. -/
def ι₂ : D.kernel.cat ⥤ D.right.cat := Translation.functor D.wf_right D.gluable.right

/-- The first schema in the glued schema. -/
def inl : D.left.cat ⥤ D.glued.cat := Translation.functor D.wf_glued D.inl_valid

/-- The second schema in the glued schema. -/
def inr : D.right.cat ⥤ D.glued.cat := Translation.functor D.wf_glued D.inr_valid

/-- The square of the pushout commutes. -/
theorem comm : D.ι₁ ⋙ D.inl = D.ι₂ ⋙ D.inr := by
  refine ext_functor (fun a => rfl) fun a b e => ?_
  simp only [Functor.comp_map, ι₁, ι₂, inl, inr, Translation.functor_map_mor, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  congr 1
  apply names_injective
  simp only [Translation.names_functorPath_empty]

end Gluing

end DDD
