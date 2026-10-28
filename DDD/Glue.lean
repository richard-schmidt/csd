import DDD.Translation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Gluing schemas

Strict integration is an explicit merge. `Schema.glue B₁ B₂` is the pushout of
two presentations along a common kernel `K` that both include with the same
names: the union of the generators, identified along the kernel, and the union of
the equations. `Schema.Gluable K B₁ B₂` states the conditions: `K` is included in
both, by the empty translation, and `B₁` and `B₂` share only entity types and
generators of `K`. `checkGluable` is its check; `gluingClashes` lists the names
they share outside `K`.

A `Gluing` bundles a kernel, two schemas, and the conditions, with the legs
`inl` and `inr` of the glued schema and the square `ι₁ ⋙ inl = ι₂ ⋙ inr`.

The bridge theorem: for every category `X`, functors from the glued schema
category to `X` correspond to pairs of functors from the two schema categories
that agree on the kernel (`Gluing.glueEquiv`), so the square is a pushout in
`Cat` (`Gluing.isPushout`). The functor glued from `F₁` and `F₂` (`desc`) is
`F₁` on the generators of the first schema and `F₂` on the others; it respects
the equations because the glued equations are those of the two schemas.
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
  valueObjects := B₁.valueObjects ++ B₂.valueObjects.filter fun e => e ∉ B₁.valueObjects

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

/-- The names that `B₁` and `B₂` share outside the kernel `K`: entity types by
name, generators as `Entity.name`. Gluing needs this list empty; a non-empty
list names what to rename. -/
def gluingClashes (K B₁ B₂ : Schema) : List String :=
  (B₁.entities.filter fun e => e ∈ B₂.entities ∧ e ∉ K.entities) ++
    (B₁.gens.filter fun g => g ∈ B₂.gens ∧ g ∉ K.gens).map fun g => g.1 ++ "." ++ g.2

theorem gluingClashes_eq_nil_iff {K : Schema} : gluingClashes K B₁ B₂ = [] ↔
    (∀ e ∈ B₁.entities, e ∈ B₂.entities → e ∈ K.entities) ∧
      (∀ g ∈ B₁.gens, g ∈ B₂.gens → g ∈ K.gens) := by
  simp only [gluingClashes, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq, not_and, not_not]

/-- The check for `Gluable`. -/
def checkGluable (K B₁ B₂ : Schema) : Bool :=
  ({} : Translation).checkValid K B₁ B₁.pathEq &&
  ({} : Translation).checkValid K B₂ B₂.pathEq &&
  (gluingClashes K B₁ B₂).isEmpty

theorem checkGluable_sound {K : Schema} (h₁ : B₁.WellFormed) (h₂ : B₂.WellFormed)
    (h : checkGluable K B₁ B₂ = true) : Gluable K B₁ B₂ := by
  simp only [checkGluable, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨hl, hr⟩, hc⟩ := h
  obtain ⟨he, hg⟩ := gluingClashes_eq_nil_iff.mp hc
  exact ⟨Translation.checkValid_sound (fun a _ _ h => pathEq_sound h₁ a h) hl,
    Translation.checkValid_sound (fun a _ _ h => pathEq_sound h₂ a h) hr, he, hg⟩

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

/-- Where both schemas have a generator, the kernel has it too. -/
theorem Gluable.kernel_step? {K : Schema} (h : Gluable K B₁ B₂) (hK : K.WellFormed)
    {o x y : Ob} {n : String} (h₁ : B₁.step? o n = some x) (h₂ : B₂.step? o n = some y) :
    K.step? o n = some x := by
  cases o with
  | value => simp [step?] at h₁
  | entity e =>
    have hk := h.gens (e, n) (step?_isSome_iff.mp (by simp [h₁]))
      (step?_isSome_iff.mp (by simp [h₂]))
    simp only [Schema.gens, List.mem_append, List.mem_map, Prod.mk.injEq] at hk
    rcases hk with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · have e₁ := h.left.ref r hr
      simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton] at e₁
      rw [step?_of_mem_refs hK hr, ← e₁, h₁]
    · have e₁ := h.left.attr a ha
      simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton] at e₁
      rw [step?_of_mem_attrs hK ha, ← e₁, h₁]

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

/-! ## The bridge theorem

Functors out of the glued schema category correspond to pairs of functors out of
the two schema categories that agree on the kernel. -/

section Desc

variable {X : Type*} [Category X] {F₁ : D.left.cat ⥤ X} {F₂ : D.right.cat ⥤ X}

theorem isOb_right_of_not_left (a : D.glued.Obj) (h : ¬ D.left.IsOb a.1) :
    D.right.IsOb a.1 := by
  obtain ⟨o, ho⟩ := a
  cases o with
  | value => exact absurd trivial h
  | entity e =>
    simp only [IsOb, glue, List.mem_append, List.mem_filter, decide_eq_true_eq] at ho h ⊢
    rcases ho with h' | ⟨h', -⟩
    · exact absurd h' h
    · exact h'

theorem isOb_kernel {o : Ob} (h₁ : D.left.IsOb o) (h₂ : D.right.IsOb o) :
    D.kernel.IsOb o := by
  cases o with
  | value => trivial
  | entity e => exact D.gluable.entities e h₁ h₂

variable (F₁ F₂) in
/-- The object map of the glued functor: `F₁` on the objects of the first schema,
`F₂` on the others. -/
def descObj (a : D.glued.Obj) : X :=
  if h : D.left.IsOb a.1 then F₁.obj (D.left.obj ⟨a.1, h⟩)
  else F₂.obj (D.right.obj ⟨a.1, D.isOb_right_of_not_left a h⟩)

theorem descObj_left (a : D.glued.Obj) (h : D.left.IsOb a.1) :
    D.descObj F₁ F₂ a = F₁.obj (D.left.obj ⟨a.1, h⟩) := dif_pos h

variable (hF : D.ι₁ ⋙ F₁ = D.ι₂ ⋙ F₂)

include hF in
/-- On the kernel, `F₁` and `F₂` agree. -/
theorem obj_agree {o : Ob} (h₁ : D.left.IsOb o) (h₂ : D.right.IsOb o) :
    F₁.obj (D.left.obj ⟨o, h₁⟩) = F₂.obj (D.right.obj ⟨o, h₂⟩) := by
  have hk := D.isOb_kernel h₁ h₂
  have e₁ : D.ι₁.obj (D.kernel.obj ⟨o, hk⟩) = D.left.obj ⟨o, h₁⟩ :=
    congrArg D.left.obj (Subtype.ext (Translation.ob_empty o))
  have e₂ : D.ι₂.obj (D.kernel.obj ⟨o, hk⟩) = D.right.obj ⟨o, h₂⟩ :=
    congrArg D.right.obj (Subtype.ext (Translation.ob_empty o))
  rw [← e₁, ← e₂]
  exact Functor.congr_obj hF _

include hF in
theorem descObj_right (a : D.glued.Obj) (h : D.right.IsOb a.1) :
    D.descObj F₁ F₂ a = F₂.obj (D.right.obj ⟨a.1, h⟩) := by
  unfold descObj
  split
  · exact D.obj_agree hF _ _
  · rfl

/-- The map of the glued functor on a generator: through `F₁` if the generator is
one of the first schema, through `F₂` otherwise. -/
def descMap {a b : D.glued.Obj} (e : a ⟶ b) : D.descObj F₁ F₂ a ⟶ D.descObj F₁ F₂ b :=
  match h : D.left.step? a.1 e.1 with
  | some x =>
    have hx : x = b.1 := by
      have h' := e.2
      rw [glue_step?, h] at h'
      exact Option.some.inj h'
    have ha : D.left.IsOb a.1 := isOb_src_of_step? D.wf_left h
    have hb : D.left.IsOb b.1 := hx ▸ isOb_of_step? D.wf_left h
    eqToHom (D.descObj_left a ha) ≫
      F₁.map (D.left.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 (hx ▸ h)) ≫
      eqToHom (D.descObj_left b hb).symm
  | none =>
    have h₂ : D.right.step? a.1 e.1 = some b.1 := by
      have h' := e.2
      rw [glue_step?, h, Option.none_or] at h'
      exact h'
    have ha : D.right.IsOb a.1 := isOb_src_of_step? D.wf_right h₂
    have hb : D.right.IsOb b.1 := isOb_of_step? D.wf_right h₂
    eqToHom (D.descObj_right hF a ha) ≫
      F₂.map (D.right.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 h₂) ≫
      eqToHom (D.descObj_right hF b hb).symm

theorem descMap_left {a b : D.glued.Obj} (e : a ⟶ b) (ha : D.left.IsOb a.1)
    (hb : D.left.IsOb b.1) (h : D.left.step? a.1 e.1 = some b.1) :
    D.descMap hF e = eqToHom (D.descObj_left a ha) ≫
      F₁.map (D.left.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 h) ≫
      eqToHom (D.descObj_left b hb).symm := by
  unfold descMap
  split
  · rename_i x hx
    obtain rfl : x = b.1 := Option.some.inj (hx.symm.trans h)
    rfl
  · rename_i hx
    simp [hx] at h

/-- On a generator of the second schema, the glued functor is `F₂`; where the
generator is also one of the first schema, it is a kernel generator, on which
`F₁` and `F₂` agree. -/
theorem descMap_right {a b : D.glued.Obj} (e : a ⟶ b) (ha : D.right.IsOb a.1)
    (hb : D.right.IsOb b.1) (h : D.right.step? a.1 e.1 = some b.1) :
    D.descMap hF e = eqToHom (D.descObj_right hF a ha) ≫
      F₂.map (D.right.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 h) ≫
      eqToHom (D.descObj_right hF b hb).symm := by
  unfold descMap
  split
  · rename_i x hx
    obtain rfl : x = b.1 := D.gluable.step?_eq hx h
    have ha₁ : D.left.IsOb a.1 := isOb_src_of_step? D.wf_left hx
    have hb₁ : D.left.IsOb b.1 := isOb_of_step? D.wf_left hx
    have hk : D.kernel.step? a.1 e.1 = some b.1 := D.gluable.kernel_step? D.wf_kernel hx h
    have ka : D.kernel.IsOb a.1 := isOb_src_of_step? D.wf_kernel hk
    have kb : D.kernel.IsOb b.1 := isOb_of_step? D.wf_kernel hk
    have g₁ := Translation.functor_empty_genMor D.wf_left D.gluable.left
      (a := ⟨a.1, ka⟩) (b := ⟨b.1, kb⟩) e.1 hk ha₁ hb₁ hx
    have g₂ := Translation.functor_empty_genMor D.wf_right D.gluable.right
      (a := ⟨a.1, ka⟩) (b := ⟨b.1, kb⟩) e.1 hk ha hb h
    have hc := Functor.congr_hom hF (D.kernel.genMor (a := ⟨a.1, ka⟩) (b := ⟨b.1, kb⟩) e.1 hk)
    simp only [Functor.comp_map, ι₁, ι₂] at hc
    have k₁ : D.left.genMor (a := ⟨a.1, ha₁⟩) (b := ⟨b.1, hb₁⟩) e.1 hx =
        eqToHom (by rw [Translation.functor_obj, Translation.obj_empty]) ≫
          (Translation.functor D.wf_left D.gluable.left).map
            (D.kernel.genMor (a := ⟨a.1, ka⟩) (b := ⟨b.1, kb⟩) e.1 hk) ≫
          eqToHom (by rw [Translation.functor_obj, Translation.obj_empty]) := by
      rw [g₁]
      simp
    dsimp only
    rw [k₁, Functor.map_comp, Functor.map_comp, hc, g₂]
    simp [eqToHom_map]
  · rfl

/-- The prefunctor of the glued functor. -/
def descPrefunctor : D.glued.Obj ⥤q X where
  obj := D.descObj F₁ F₂
  map := D.descMap hF

/-- On a path of the glued schema whose names are a path of the first schema, the
glued functor is `F₁`. -/
theorem lift_map_left {a : D.glued.Obj} (ha : D.left.IsOb a.1) :
    ∀ {b : D.glued.Obj} (p : Quiver.Path a b) (hb : D.left.IsOb b.1)
      (h : D.left.tgt? a.1 (names p) = some b.1),
      (Paths.lift (D.descPrefunctor hF)).map p = eqToHom (D.descObj_left a ha) ≫
        F₁.map (D.left.mor (D.left.pathOf D.wf_left ⟨a.1, ha⟩ ⟨b.1, hb⟩ (names p) h)) ≫
        eqToHom (D.descObj_left b hb).symm
  | _, .nil, hb, h => by
    have : D.left.pathOf D.wf_left ⟨a.1, ha⟩ ⟨a.1, hb⟩ (names Quiver.Path.nil) h =
        Quiver.Path.nil := names_injective _ _ (by simp)
    rw [this]
    simp [Paths.lift_nil]
    rfl
  | b, .cons (b := c) p e, hb, h => by
    have h' := h
    rw [names_cons, tgt?_append] at h'
    obtain ⟨c', hc', he⟩ := Option.bind_eq_some_iff.mp h'
    obtain rfl : c' = c.1 :=
      Option.some.inj ((glue_tgt?_of_left hc').symm.trans (tgt?_names p))
    rw [tgt?_singleton] at he
    have hc : D.left.IsOb c.1 := isOb_src_of_step? D.wf_left he
    rw [Paths.lift_cons, lift_map_left ha p hc hc']
    change _ ≫ D.descMap hF e = _
    rw [D.descMap_left hF e hc hb he]
    have hp : D.left.pathOf D.wf_left ⟨a.1, ha⟩ ⟨b.1, hb⟩ (names (p.cons e)) h =
        (D.left.pathOf D.wf_left ⟨a.1, ha⟩ ⟨c.1, hc⟩ (names p) hc').comp
          (D.left.genPath ⟨c.1, hc⟩ ⟨b.1, hb⟩ e.1 he) :=
      names_injective _ _ (by simp)
    rw [hp, mor_comp, Functor.map_comp]
    simp

/-- On a path of the glued schema whose names are a path of the second schema, the
glued functor is `F₂`. -/
theorem lift_map_right {a : D.glued.Obj} (ha : D.right.IsOb a.1) :
    ∀ {b : D.glued.Obj} (p : Quiver.Path a b) (hb : D.right.IsOb b.1)
      (h : D.right.tgt? a.1 (names p) = some b.1),
      (Paths.lift (D.descPrefunctor hF)).map p = eqToHom (D.descObj_right hF a ha) ≫
        F₂.map (D.right.mor (D.right.pathOf D.wf_right ⟨a.1, ha⟩ ⟨b.1, hb⟩ (names p) h)) ≫
        eqToHom (D.descObj_right hF b hb).symm
  | _, .nil, hb, h => by
    have : D.right.pathOf D.wf_right ⟨a.1, ha⟩ ⟨a.1, hb⟩ (names Quiver.Path.nil) h =
        Quiver.Path.nil := names_injective _ _ (by simp)
    rw [this]
    simp [Paths.lift_nil]
    rfl
  | b, .cons (b := c) p e, hb, h => by
    have h' := h
    rw [names_cons, tgt?_append] at h'
    obtain ⟨c', hc', he⟩ := Option.bind_eq_some_iff.mp h'
    obtain rfl : c' = c.1 :=
      Option.some.inj ((D.gluable.glue_tgt?_of_right hc').symm.trans (tgt?_names p))
    rw [tgt?_singleton] at he
    have hc : D.right.IsOb c.1 := isOb_src_of_step? D.wf_right he
    rw [Paths.lift_cons, lift_map_right ha p hc hc']
    change _ ≫ D.descMap hF e = _
    rw [D.descMap_right hF e hc hb he]
    have hp : D.right.pathOf D.wf_right ⟨a.1, ha⟩ ⟨b.1, hb⟩ (names (p.cons e)) h =
        (D.right.pathOf D.wf_right ⟨a.1, ha⟩ ⟨c.1, hc⟩ (names p) hc').comp
          (D.right.genPath ⟨c.1, hc⟩ ⟨b.1, hb⟩ e.1 he) :=
      names_injective _ _ (by simp)
    rw [hp, mor_comp, Functor.map_comp]
    simp

/-- The functor glued from `F₁` and `F₂`. It respects the equations of both
schemas, which are the equations of the glued schema. -/
def desc : D.glued.cat ⥤ X :=
  CategoryTheory.Quotient.lift D.glued.rel (Paths.lift (D.descPrefunctor hF)) (by
    rintro a b f g ⟨q, hq, ha, h₁, h₂⟩
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨o, hl, hr⟩ := D.wf_left.eqn_parallel q hq
      have hqa : D.left.IsOb a.1 := ha ▸ D.wf_left.eqn_src q hq
      rw [← ha, ← h₁] at hl
      rw [← ha, ← h₂] at hr
      obtain rfl : o = b.1 :=
        Option.some.inj ((glue_tgt?_of_left hl).symm.trans (tgt?_names f))
      have hb : D.left.IsOb b.1 := isOb_of_tgt? D.wf_left hqa hl
      change (Paths.lift (D.descPrefunctor hF)).map f = (Paths.lift (D.descPrefunctor hF)).map g
      rw [D.lift_map_left hF hqa f hb hl, D.lift_map_left hF hqa g hb hr]
      have hm : D.left.mor (D.left.pathOf D.wf_left ⟨a.1, hqa⟩ ⟨b.1, hb⟩ (names f) hl) =
          D.left.mor (D.left.pathOf D.wf_left ⟨a.1, hqa⟩ ⟨b.1, hb⟩ (names g) hr) := by
        apply PathEq.mor_eq
        rw [names_pathOf, names_pathOf, h₁, h₂]
        have hpe := pathEq_of_mem_eqns D.wf_left hq
        have hobj : (⟨a.1, hqa⟩ : D.left.Obj) = ⟨.entity q.src, D.wf_left.eqn_src q hq⟩ :=
          Subtype.ext ha
        rw [hobj]
        exact hpe
      rw [hm]
    · obtain ⟨o, hl, hr⟩ := D.wf_right.eqn_parallel q hq
      have hqa : D.right.IsOb a.1 := ha ▸ D.wf_right.eqn_src q hq
      rw [← ha, ← h₁] at hl
      rw [← ha, ← h₂] at hr
      obtain rfl : o = b.1 :=
        Option.some.inj ((D.gluable.glue_tgt?_of_right hl).symm.trans (tgt?_names f))
      have hb : D.right.IsOb b.1 := isOb_of_tgt? D.wf_right hqa hl
      change (Paths.lift (D.descPrefunctor hF)).map f = (Paths.lift (D.descPrefunctor hF)).map g
      rw [D.lift_map_right hF hqa f hb hl, D.lift_map_right hF hqa g hb hr]
      have hm : D.right.mor (D.right.pathOf D.wf_right ⟨a.1, hqa⟩ ⟨b.1, hb⟩ (names f) hl) =
          D.right.mor (D.right.pathOf D.wf_right ⟨a.1, hqa⟩ ⟨b.1, hb⟩ (names g) hr) := by
        apply PathEq.mor_eq
        rw [names_pathOf, names_pathOf, h₁, h₂]
        have hpe := pathEq_of_mem_eqns D.wf_right hq
        have hobj : (⟨a.1, hqa⟩ : D.right.Obj) = ⟨.entity q.src, D.wf_right.eqn_src q hq⟩ :=
          Subtype.ext ha
        rw [hobj]
        exact hpe
      rw [hm])

theorem desc_obj (a : D.glued.Obj) : (D.desc hF).obj (D.glued.obj a) = D.descObj F₁ F₂ a := rfl

/-- The glued functor restricts to `F₁` on the first schema. -/
theorem inl_desc : D.inl ⋙ D.desc hF = F₁ := by
  have hobj : ∀ a : D.left.Obj, (D.inl ⋙ D.desc hF).obj (D.left.obj a) = F₁.obj (D.left.obj a) :=
    fun a => by
      change D.descObj F₁ F₂ (Translation.obj D.inl_valid a) = _
      rw [Translation.obj_empty]
      exact D.descObj_left _ a.2
  refine ext_functor hobj fun a b e => ?_
  have ha : D.left.IsOb (Translation.ob {} a.1) := (Translation.ob_empty a.1).symm ▸ a.2
  have hb : D.left.IsOb (Translation.ob {} b.1) := (Translation.ob_empty b.1).symm ▸ b.2
  have hp : D.left.tgt? (Translation.ob {} a.1)
      (names (Translation.functorPath D.wf_glued D.inl_valid e.toPath)) =
        some (Translation.ob {} b.1) := by
    rw [Translation.names_functorPath_empty, Translation.ob_empty, Translation.ob_empty]
    simpa [tgt?_singleton] using e.2
  change (Paths.lift (D.descPrefunctor hF)).map
      (Translation.functorPath D.wf_glued D.inl_valid e.toPath) = _
  rw [D.lift_map_left hF ha _ hb hp,
    map_mor_eq_of_names F₁ (Subtype.ext (Translation.ob_empty a.1))
      (Subtype.ext (Translation.ob_empty b.1)) _ e.toPath
        (by simp [Translation.names_functorPath_empty])]
  simp

/-- The glued functor restricts to `F₂` on the second schema. -/
theorem inr_desc : D.inr ⋙ D.desc hF = F₂ := by
  have hobj : ∀ a : D.right.Obj, (D.inr ⋙ D.desc hF).obj (D.right.obj a) = F₂.obj (D.right.obj a) :=
    fun a => by
      change D.descObj F₁ F₂ (Translation.obj D.inr_valid a) = _
      rw [Translation.obj_empty]
      exact D.descObj_right hF _ a.2
  refine ext_functor hobj fun a b e => ?_
  have ha : D.right.IsOb (Translation.ob {} a.1) := (Translation.ob_empty a.1).symm ▸ a.2
  have hb : D.right.IsOb (Translation.ob {} b.1) := (Translation.ob_empty b.1).symm ▸ b.2
  have hp : D.right.tgt? (Translation.ob {} a.1)
      (names (Translation.functorPath D.wf_glued D.inr_valid e.toPath)) =
        some (Translation.ob {} b.1) := by
    rw [Translation.names_functorPath_empty, Translation.ob_empty, Translation.ob_empty]
    simpa [tgt?_singleton] using e.2
  change (Paths.lift (D.descPrefunctor hF)).map
      (Translation.functorPath D.wf_glued D.inr_valid e.toPath) = _
  rw [D.lift_map_right hF ha _ hb hp,
    map_mor_eq_of_names F₂ (Subtype.ext (Translation.ob_empty a.1))
      (Subtype.ext (Translation.ob_empty b.1)) _ e.toPath
        (by simp [Translation.names_functorPath_empty])]
  simp

theorem desc_map_genPath {a b : D.glued.Obj} (e : a ⟶ b) :
    (D.desc hF).map (D.glued.mor e.toPath) = D.descMap hF e :=
  Paths.lift_toPath _ _

/-- The glued functor is the only functor that restricts to `F₁` and `F₂`. -/
theorem desc_unique (F : D.glued.cat ⥤ X) (h₁ : D.inl ⋙ F = F₁) (h₂ : D.inr ⋙ F = F₂) :
    F = D.desc hF := by
  have hobj : ∀ a : D.glued.Obj, F.obj (D.glued.obj a) = (D.desc hF).obj (D.glued.obj a) := by
    intro a
    rw [desc_obj]
    by_cases ha : D.left.IsOb a.1
    · have e : D.inl.obj (D.left.obj ⟨a.1, ha⟩) = D.glued.obj a :=
        congrArg D.glued.obj (Subtype.ext (Translation.ob_empty a.1))
      rw [← e, D.descObj_left a ha]
      exact Functor.congr_obj h₁ _
    · have ha₂ := D.isOb_right_of_not_left a ha
      have e : D.inr.obj (D.right.obj ⟨a.1, ha₂⟩) = D.glued.obj a :=
        congrArg D.glued.obj (Subtype.ext (Translation.ob_empty a.1))
      rw [← e, D.descObj_right hF a ha₂]
      exact Functor.congr_obj h₂ _
  refine ext_functor hobj fun a b e => ?_
  rw [desc_map_genPath]
  cases hs : D.left.step? a.1 e.1 with
  | some x =>
    obtain rfl : x = b.1 := by
      have h' := e.2
      rw [glue_step?, hs] at h'
      exact Option.some.inj h'
    have ha : D.left.IsOb a.1 := isOb_src_of_step? D.wf_left hs
    have hb : D.left.IsOb b.1 := isOb_of_step? D.wf_left hs
    rw [D.descMap_left hF e ha hb hs]
    have g := Translation.functor_empty_genMor D.wf_glued D.inl_valid
      (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs a.2 b.2 e.2
    have k : D.glued.mor e.toPath =
        eqToHom (congrArg D.glued.obj (Subtype.ext (Translation.ob_empty a.1) :
          Translation.obj D.inl_valid ⟨a.1, ha⟩ = ⟨a.1, a.2⟩)).symm ≫
        D.inl.map (D.left.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs) ≫
        eqToHom (congrArg D.glued.obj (Subtype.ext (Translation.ob_empty b.1) :
          Translation.obj D.inl_valid ⟨b.1, hb⟩ = ⟨b.1, b.2⟩)) := by
      simp only [inl]
      rw [g]
      simp
      rfl
    have hc := Functor.congr_hom h₁ (D.left.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs)
    simp only [Functor.comp_map] at hc
    rw [k, Functor.map_comp, Functor.map_comp, hc]
    simp [eqToHom_map]
  | none =>
    have hs₂ : D.right.step? a.1 e.1 = some b.1 := by
      have h' := e.2
      rw [glue_step?, hs, Option.none_or] at h'
      exact h'
    have ha : D.right.IsOb a.1 := isOb_src_of_step? D.wf_right hs₂
    have hb : D.right.IsOb b.1 := isOb_of_step? D.wf_right hs₂
    rw [D.descMap_right hF e ha hb hs₂]
    have g := Translation.functor_empty_genMor D.wf_glued D.inr_valid
      (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs₂ a.2 b.2 e.2
    have k : D.glued.mor e.toPath =
        eqToHom (congrArg D.glued.obj (Subtype.ext (Translation.ob_empty a.1) :
          Translation.obj D.inr_valid ⟨a.1, ha⟩ = ⟨a.1, a.2⟩)).symm ≫
        D.inr.map (D.right.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs₂) ≫
        eqToHom (congrArg D.glued.obj (Subtype.ext (Translation.ob_empty b.1) :
          Translation.obj D.inr_valid ⟨b.1, hb⟩ = ⟨b.1, b.2⟩)) := by
      simp only [inr]
      rw [g]
      simp
      rfl
    have hc := Functor.congr_hom h₂ (D.right.genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs₂)
    simp only [Functor.comp_map] at hc
    rw [k, Functor.map_comp, Functor.map_comp, hc]
    simp [eqToHom_map]

end Desc

/-- The bridge theorem: functors out of the glued schema category correspond to
pairs of functors out of the two schema categories that agree on the kernel. -/
def glueEquiv (X : Type*) [Category X] :
    (D.glued.cat ⥤ X) ≃ { F : (D.left.cat ⥤ X) × (D.right.cat ⥤ X) // D.ι₁ ⋙ F.1 = D.ι₂ ⋙ F.2 }
    where
  toFun F := ⟨(D.inl ⋙ F, D.inr ⋙ F), congrArg (· ⋙ F) D.comm⟩
  invFun F := D.desc F.2
  left_inv F := (D.desc_unique _ F rfl rfl).symm
  right_inv F := Subtype.ext (Prod.ext (D.inl_desc F.2) (D.inr_desc F.2))

/-- The bridge theorem in `Cat`: the glued schema category is the pushout of the two
schema categories along the kernel. -/
theorem isPushout : IsPushout (C := Cat.{0, 0}) D.ι₁ D.ι₂ D.inl D.inr :=
  IsPushout.of_isColimit (c := Limits.PushoutCocone.mk (C := Cat.{0, 0}) D.inl D.inr D.comm)
    (Limits.PushoutCocone.IsColimit.mk _ (fun s => D.desc s.condition)
      (fun s => D.inl_desc s.condition) (fun s => D.inr_desc s.condition)
      (fun s m h₁ h₂ => D.desc_unique s.condition m h₁ h₂))

end Gluing

/-! ## Strict non-interference

A merge can impose an equation of one schema on the other, or more generally a
translation can identify paths or add morphisms between images. The check below
decides, for acyclic schemas, that the functor of a translation is full and
faithful. -/

namespace Schema

/-- The objects of a schema that a path can end at, given its target `t` in
another schema: the declared entity types, and the value type `t` names, if it
names one. -/
def obsFor (S : Schema) (t : Option Ob) : List Ob :=
  S.entities.map .entity ++ match t with
    | some (.value v) => [.value v]
    | _ => []

theorem mem_obsFor {S : Schema} {o : Ob} (h : S.IsOb o) {t : Option Ob}
    (ht : ∀ v, o = .value v → t = some (.value v)) : o ∈ S.obsFor t := by
  cases o with
  | entity e => exact List.mem_append_left _ (List.mem_map.mpr ⟨e, h, rfl⟩)
  | value v =>
    obtain rfl := ht v rfl
    simp [obsFor]

/-- Only the empty path leaves a value type. -/
theorem eq_nil_of_tgt?_value {S : Schema} {v : ValueType} {l : List String} {x : Ob}
    (h : S.tgt? (.value v) l = some x) : l = [] ∧ x = .value v := by
  cases l with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons n ns => simp [step?] at h

end Schema

namespace Translation

open Schema

variable (T : Translation)

/-- Faithfulness at the entity type `e`: parallel paths out of `e` whose images are
equal in `S'` are equal in `S`. -/
def faithfulAt (S S' : Schema) (e : String) : Bool :=
  (S.paths (.entity e) S.entities.length).all fun l =>
    let C := S.classOf (.entity e) l
    let C' := S'.classOf (T.ob (.entity e)) (T.mapPath S (.entity e) l)
    (S.paths (.entity e) S.entities.length).all fun l' =>
      !(decide (S.tgt? (.entity e) l = S.tgt? (.entity e) l') &&
          decide (T.mapPath S (.entity e) l' ∈ C')) || decide (l' ∈ C)

/-- Fullness at the entity type `e`: every path of `S'` from the image of `e` to the
image of an object `o` of `S` is equal to the image of a path from `e` to `o`. -/
def fullAt (S S' : Schema) (e : String) : Bool :=
  let images := (S.paths (.entity e) S.entities.length).map fun l =>
    (S.tgt? (.entity e) l, S'.classOf (T.ob (.entity e)) (T.mapPath S (.entity e) l))
  (S'.paths (T.ob (.entity e)) S'.entities.length).all fun g =>
    (S.obsFor (S'.tgt? (T.ob (.entity e)) g)).all fun o =>
      !decide (S'.tgt? (T.ob (.entity e)) g = some (T.ob o)) ||
        images.any fun li => decide (li.1 = some o) && decide (g ∈ li.2)

/-- The check for strict non-interference: the functor of `T` is faithful and full,
for acyclic `S` and `S'`. -/
def checkFullyFaithful (S S' : Schema) : Bool :=
  S.entities.all fun e => T.faithfulAt S S' e && T.fullAt S S' e

variable {T} {S S' : Schema}

theorem checkFullyFaithful_sound (hS : S.WellFormed) (hS' : S'.WellFormed) (hA : S.Acyclic)
    (hA' : S'.Acyclic) (hT : T.Valid S S') (h : T.checkFullyFaithful S S' = true) :
    (functor hS' hT).Full ∧ (functor hS' hT).Faithful := by
  simp only [checkFullyFaithful, List.all_eq_true, Bool.and_eq_true] at h
  constructor
  · refine ⟨fun {X Y} f => ?_⟩
    obtain ⟨a, rfl⟩ := S.obj_surjective X
    obtain ⟨b, rfl⟩ := S.obj_surjective Y
    obtain ⟨g, rfl⟩ := S'.mor_surjective (a := obj hT a) (b := obj hT b) f
    obtain ⟨o, ho⟩ := a
    cases o with
    | value v =>
      obtain ⟨hg, hb⟩ := eq_nil_of_tgt?_value (tgt?_names g)
      have hb' : b = ⟨.value v, ho⟩ := by
        obtain ⟨ob, hob⟩ := b
        cases ob with
        | entity e' => simp [obj, ob] at hb
        | value w => simp only [obj, ob, Ob.value.injEq] at hb; subst hb; rfl
      subst hb'
      refine ⟨𝟙 _, ?_⟩
      rw [CategoryTheory.Functor.map_id]
      have : g = Quiver.Path.nil := names_injective _ _ hg
      subst this
      exact mor_nil.symm
    | entity e =>
      have hfull := (h e ho).2
      simp only [fullAt, List.any_map, Function.comp_def, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hfull
      have hg' : S'.tgt? (T.ob (.entity e)) (names g) = some (T.ob b.1) := tgt?_names g
      have hgP : names g ∈ S'.paths (T.ob (.entity e)) S'.entities.length :=
        (mem_paths _ _ _).mpr ⟨by simp [hg'],
          hA' ⟨T.ob (.entity e), isOb_ob hT ho⟩ _ (by simp [hg'])⟩
      have hb : b.1 ∈ S.obsFor (S'.tgt? (T.ob (.entity e)) (names g)) :=
        mem_obsFor b.2 fun v hv => by rw [hg', hv]; rfl
      obtain ⟨l, -, hl, hpe⟩ := (hfull (names g) hgP b.1 hb).resolve_left
        (not_not.mpr hg')
      let p := S.pathOf hS ⟨.entity e, ho⟩ b l hl
      refine ⟨mor p, ?_⟩
      rw [functor_map_mor]
      apply PathEq.mor_eq
      rw [names_functorPath, names_pathOf]
      exact pathEqAcyclic_sound hS' _ (by simpa [pathEqAcyclic] using hpe)
  · refine ⟨fun {X Y} f₁ f₂ hf => ?_⟩
    obtain ⟨a, rfl⟩ := S.obj_surjective X
    obtain ⟨b, rfl⟩ := S.obj_surjective Y
    obtain ⟨p, rfl⟩ := S.mor_surjective f₁
    obtain ⟨q, rfl⟩ := S.mor_surjective f₂
    rw [functor_map_mor, functor_map_mor] at hf
    obtain ⟨o, ho⟩ := a
    cases o with
    | value v =>
      have hp := (eq_nil_of_tgt?_value (tgt?_names p)).1
      have hq := (eq_nil_of_tgt?_value (tgt?_names q)).1
      rw [names_injective p q (hp.trans hq.symm)]
    | entity e =>
      have hfaith := (h e ho).1
      simp only [faithfulAt, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq] at hfaith
      have hp : S.tgt? (.entity e) (names p) = some b.1 := tgt?_names p
      have hq : S.tgt? (.entity e) (names q) = some b.1 := tgt?_names q
      have memp : names p ∈ S.paths (.entity e) S.entities.length :=
        (mem_paths _ _ _).mpr ⟨by simp [hp], hA ⟨.entity e, ho⟩ _ (by simp [hp])⟩
      have memq : names q ∈ S.paths (.entity e) S.entities.length :=
        (mem_paths _ _ _).mpr ⟨by simp [hq], hA ⟨.entity e, ho⟩ _ (by simp [hq])⟩
      have hpe' : T.mapPath S (.entity e) (names q) ∈
          S'.classOf (T.ob (.entity e)) (T.mapPath S (.entity e) (names p)) := by
        have h' := pathEqAcyclic_complete hS' hA' (obj hT ⟨.entity e, ho⟩)
          (l := names (functorPath hS' hT p)) (l' := names (functorPath hS' hT q))
          ⟨_, _, _, rfl, rfl, hf⟩
        rw [names_functorPath, names_functorPath] at h'
        simpa [pathEqAcyclic] using h'
      rcases hfaith (names p) memp (names q) memq with (hne | hne) | hpe
      · exact absurd (hp.trans hq.symm) hne
      · exact absurd hpe' hne
      · exact PathEq.mor_eq (pathEqAcyclic_sound hS _ (by simpa [pathEqAcyclic] using hpe))

end Translation

end DDD
