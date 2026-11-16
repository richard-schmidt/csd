import DDD.Keys
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# The closure of a state under its keys

A state satisfies the keys of its schema when two entities that agree on every
field of a key are equal (`Schema.State.Keys`). The closure of a state identifies
the entities that the keys force to be equal, and then what they reference.

- `State.KeyRel X`: the least family of equivalence relations on the elements of
  `X` that every generator respects and that relates two entities whose key fields
  are related. A morphism into a state that satisfies the keys sends related
  elements to one element (`KeyRel.app_eq`).
- `State.Consistent X`: the relation does not relate two distinct values. A state
  is consistent exactly when it has a morphism into a state that satisfies the
  keys (`consistent_iff`); a state that satisfies the keys is consistent
  (`Keys.consistent`).
- `State.closure X h`: the quotient of a consistent state by the relation. It
  satisfies the keys (`closure_keys`), and `State.unit` maps `X` onto it.
- The universal property: a morphism from `X` into a state that satisfies the keys
  factors through the closure, in one way (`State.lift`, `unit_lift`,
  `lift_unique`, `closureHomEquiv`). The closure of a state that satisfies the keys
  is the state (`closureIso`).
- `closureAdjunction`: the states that satisfy the keys are reflective in the
  consistent states, with the closure as the reflection (`keyedReflective`).
- Merges: the closure of a pushout of states is the pushout among the states that
  satisfy the keys (`merge_existsUnique`, `isPushout_closure`), and when the
  pushout is not consistent no state that satisfies the keys receives the two
  sides compatibly (`not_consistent_of_isPushout`).
- `Σ_T`: under `Translation.AttrBijective`, the closure of `Σ_T X` is a left
  adjoint of `Δ_T` from the states that satisfy the keys, on the states whose
  `Σ_T X` is consistent (`Translation.sigmaClosureHomEquiv`,
  `Translation.keyedSigmaAdjunction`). When `T` keeps keys, `Δ_T` of such a state
  satisfies the keys of the source (`Translation.restrictState_keys`).
- Limits: the limit of a non-empty diagram of states that satisfy the keys
  satisfies them (`limitState_keys`, `keys_of_isLimit`).
-/

namespace DDD

open CategoryTheory Limits

namespace Schema

variable {S : Schema} {K : ValueType → Type}

namespace State

variable (X : S.State K)

/-- The relation the keys force on the elements of a state: the least family of
equivalence relations that every morphism of the schema respects and that relates
two entities whose fields of a key are related. -/
inductive KeyRel : ∀ a : S.cat, X.F.obj a → X.F.obj a → Prop
  | refl {a : S.cat} (x : X.F.obj a) : KeyRel a x x
  | symm {a : S.cat} {x y : X.F.obj a} : KeyRel a x y → KeyRel a y x
  | trans {a : S.cat} {x y z : X.F.obj a} : KeyRel a x y → KeyRel a y z → KeyRel a x z
  | map {a b : S.cat} (f : a ⟶ b) {x y : X.F.obj a} :
      KeyRel a x y → KeyRel b (X.F.map f x) (X.F.map f y)
  | key (k : Key) (hk : k ∈ S.allKeys) (he : k.entity ∈ S.entities)
      (x y : X.F.obj (S.obj ⟨.entity k.entity, he⟩)) :
      (∀ n ∈ k.fields, ∀ (b : S.Obj) (h : S.step? (.entity k.entity) n = some b.1),
        KeyRel (S.obj b) (X.F.map (S.genMor (a := ⟨.entity k.entity, he⟩) n h) x)
          (X.F.map (S.genMor (a := ⟨.entity k.entity, he⟩) n h) y)) →
      KeyRel (S.obj ⟨.entity k.entity, he⟩) x y

/-- The relation as a setoid at each object. -/
def keySetoid (a : S.cat) : Setoid (X.F.obj a) :=
  ⟨X.KeyRel a, ⟨KeyRel.refl, KeyRel.symm, KeyRel.trans⟩⟩

variable {X} in
/-- A morphism into a state that satisfies the keys sends related elements to one
element. -/
theorem KeyRel.app_eq {Y : S.State K} (f : X ⟶ Y) (hY : Y.Keys) {a : S.cat}
    {x y : X.F.obj a} (h : X.KeyRel a x y) : f.α.app a x = f.α.app a y := by
  induction h with
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | map g _ ih => rw [FunctorToTypes.naturality, FunctorToTypes.naturality, ih]
  | key k hk he x y _ ih =>
    refine hY k hk he _ _ fun n hn b hb => ?_
    rw [← FunctorToTypes.naturality, ← FunctorToTypes.naturality]
    exact ih n hn b hb

/-- A state is consistent when its keys do not force two distinct values to be
equal. -/
def Consistent : Prop :=
  ∀ (v : ValueType) (x y : X.F.obj (S.valueObj v)), X.KeyRel (S.valueObj v) x y → x = y

variable {X} in
/-- A state with a morphism into a state that satisfies the keys is consistent. -/
theorem consistent_of_hom {Y : S.State K} (f : X ⟶ Y) (hY : Y.Keys) : X.Consistent := by
  intro v x y r
  have h := KeyRel.app_eq f hY r
  have hx := f.values v x
  rw [h, f.values v y] at hx
  exact (X.values v).injective hx.symm

variable {X} in
/-- A state that satisfies the keys is consistent. -/
theorem Keys.consistent (hX : X.Keys) : X.Consistent := consistent_of_hom (𝟙 X) hX

/-- The quotient of a state by the relation of its keys, as a functor. -/
def closureFunctor : S.cat ⥤ Type where
  obj a := Quotient (X.keySetoid a)
  map f := Quotient.map (X.F.map f) fun _ _ h => KeyRel.map f h
  map_id a := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
  map_comp f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]

variable {X}

/-- The closure of a consistent state: its quotient by the relation of its keys.
The values are those of the state. -/
def closure (h : X.Consistent) : S.State K where
  F := X.closureFunctor
  values v :=
    { toFun := Quotient.lift (X.values v) fun x y r => congrArg _ (h v x y r)
      invFun := fun k => Quotient.mk (X.keySetoid _) ((X.values v).symm k)
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h x => simp
      right_inv := fun k => by simp }

/-- The map of a consistent state onto its closure. -/
def unit (h : X.Consistent) : X ⟶ X.closure h where
  α := { app := fun a x => Quotient.mk (X.keySetoid a) x
         naturality := fun _ _ _ => rfl }
  values := fun _ _ => rfl

theorem unit_app_surjective (h : X.Consistent) (a : S.cat) :
    Function.Surjective ((X.unit h).α.app a) := fun q => Quotient.exists_rep q

/-- Two elements have the same image in the closure exactly when they are
related. -/
theorem unit_app_eq_iff (h : X.Consistent) {a : S.cat} {x y : X.F.obj a} :
    (X.unit h).α.app a x = (X.unit h).α.app a y ↔ X.KeyRel a x y :=
  ⟨fun e => Quotient.exact e, fun r => Quotient.sound r⟩

/-- The closure satisfies the keys. -/
theorem closure_keys (h : X.Consistent) : (X.closure h).Keys := by
  intro k hk he x y hxy
  induction x using Quotient.inductionOn with
  | h x =>
  induction y using Quotient.inductionOn with
  | h y =>
    exact Quotient.sound (KeyRel.key k hk he x y fun n hn b hb =>
      Quotient.exact (hxy n hn b hb))

variable {Y : S.State K}

/-- A morphism into a state that satisfies the keys, from the closure. -/
def lift (h : X.Consistent) (hY : Y.Keys) (f : X ⟶ Y) : X.closure h ⟶ Y where
  α :=
    { app := fun a => Quotient.lift (f.α.app a) fun _ _ r => KeyRel.app_eq f hY r
      naturality := fun a b g => by
        funext q
        induction q using Quotient.inductionOn with
        | h x => exact congrFun (f.α.naturality g) x }
  values := fun v q => by
    induction q using Quotient.inductionOn with
    | h x => exact f.values v x

@[simp] theorem unit_lift (h : X.Consistent) (hY : Y.Keys) (f : X ⟶ Y) :
    X.unit h ≫ lift h hY f = f :=
  State.hom_ext fun _ _ => rfl

/-- The map onto the closure is an epimorphism. -/
theorem unit_cancel (h : X.Consistent) {g g' : X.closure h ⟶ Y}
    (e : X.unit h ≫ g = X.unit h ≫ g') : g = g' :=
  State.hom_ext fun a q => by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (fun m : X ⟶ Y => m.α.app a x) e

theorem lift_unique (h : X.Consistent) (hY : Y.Keys) (f : X ⟶ Y) (g : X.closure h ⟶ Y)
    (e : X.unit h ≫ g = f) : g = lift h hY f :=
  unit_cancel h (e.trans (unit_lift h hY f).symm)

/-- The universal property of the closure: morphisms from the closure into a state
that satisfies the keys are the morphisms from the state. -/
def closureHomEquiv (h : X.Consistent) (hY : Y.Keys) : (X.closure h ⟶ Y) ≃ (X ⟶ Y) where
  toFun g := X.unit h ≫ g
  invFun f := lift h hY f
  left_inv g := (lift_unique h hY _ g rfl).symm
  right_inv f := unit_lift h hY f

variable (X) in
/-- A state is consistent exactly when it has a morphism into a state that
satisfies the keys. -/
theorem consistent_iff : X.Consistent ↔ ∃ Y : S.State K, Y.Keys ∧ Nonempty (X ⟶ Y) :=
  ⟨fun h => ⟨X.closure h, closure_keys h, ⟨X.unit h⟩⟩, fun ⟨_, hY, ⟨f⟩⟩ => consistent_of_hom f hY⟩

/-- The closure of a state that satisfies the keys is the state. -/
def closureIso (hX : X.Keys) : X ≅ X.closure hX.consistent where
  hom := X.unit hX.consistent
  inv := lift hX.consistent hX (𝟙 X)
  hom_inv_id := unit_lift _ _ _
  inv_hom_id := unit_cancel _ (by rw [← Category.assoc, unit_lift, Category.id_comp,
    Category.comp_id])

end State

/-! ## Reflection -/

variable (S K)

/-- The states that satisfy the keys. -/
def keyed : ObjectProperty (S.State K) := fun X => X.Keys

/-- The consistent states. -/
def consistent : ObjectProperty (S.State K) := fun X => X.Consistent

theorem keyed_le_consistent : keyed S K ≤ consistent S K := fun _ h => State.Keys.consistent h

/-- The inclusion of the states that satisfy the keys into the consistent states. -/
abbrev keyedInclusion : (keyed S K).FullSubcategory ⥤ (consistent S K).FullSubcategory :=
  ObjectProperty.ιOfLE (keyed_le_consistent S K)

/-- The closure of a consistent state, as a state that satisfies the keys. -/
def closureObj (X : (consistent S K).FullSubcategory) : (keyed S K).FullSubcategory :=
  ⟨X.obj.closure X.property, State.closure_keys X.property⟩

/-- Morphisms from the closure of a consistent state into a state that satisfies
the keys are the morphisms from the state. -/
def closureEquiv (X : (consistent S K).FullSubcategory) (Y : (keyed S K).FullSubcategory) :
    (closureObj S K X ⟶ Y) ≃ (X ⟶ (keyedInclusion S K).obj Y) :=
  State.closureHomEquiv X.property Y.property

theorem closureEquiv_naturality (X : (consistent S K).FullSubcategory)
    (Y Y' : (keyed S K).FullSubcategory) (g : Y ⟶ Y') (h : closureObj S K X ⟶ Y) :
    closureEquiv S K X Y' (h ≫ g) = closureEquiv S K X Y h ≫ (keyedInclusion S K).map g := by
  change X.obj.unit X.property ≫ (h ≫ g) = (X.obj.unit X.property ≫ h) ≫ g
  exact (Category.assoc _ _ _).symm

/-- The closure, as a functor from the consistent states to the states that satisfy
the keys. -/
def closureFunctor : (consistent S K).FullSubcategory ⥤ (keyed S K).FullSubcategory :=
  Adjunction.leftAdjointOfEquiv (closureEquiv S K) (closureEquiv_naturality S K)

/-- The closure is left adjoint to the inclusion of the states that satisfy the
keys into the consistent states. -/
def closureAdjunction : closureFunctor S K ⊣ keyedInclusion S K :=
  Adjunction.adjunctionOfEquivLeft (closureEquiv S K) (closureEquiv_naturality S K)

/-- The states that satisfy the keys are reflective in the consistent states. -/
instance keyedReflective : Reflective (keyedInclusion S K) where
  L := closureFunctor S K
  adj := closureAdjunction S K

/-! ## Merges -/

namespace State

variable {S K}
variable {X Y Z P W : S.State K} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-- A pushout of states is consistent when a state that satisfies the keys
receives its two sides compatibly. So when the pushout is not consistent, no
state that satisfies the keys receives both. -/
theorem consistent_of_isPushout (hP : IsPushout f g inl inr) (hW : W.Keys) (a : X ⟶ W)
    (b : Y ⟶ W) (hab : f ≫ a = g ≫ b) : P.Consistent :=
  consistent_of_hom (hP.desc a b hab) hW

theorem not_consistent_of_isPushout (hP : IsPushout f g inl inr) (hc : ¬ P.Consistent)
    (hW : W.Keys) (a : X ⟶ W) (b : Y ⟶ W) : f ≫ a ≠ g ≫ b :=
  fun hab => hc (consistent_of_isPushout hP hW a b hab)

/-- The merge of two states along a shared state: the closure of their pushout. A
compatible pair of morphisms into a state that satisfies the keys factors through
it, in one way. -/
theorem merge_existsUnique (hP : IsPushout f g inl inr) (hc : P.Consistent) (hW : W.Keys)
    (a : X ⟶ W) (b : Y ⟶ W) (hab : f ≫ a = g ≫ b) :
    ∃! m : P.closure hc ⟶ W, inl ≫ P.unit hc ≫ m = a ∧ inr ≫ P.unit hc ≫ m = b := by
  refine ⟨lift hc hW (hP.desc a b hab), ⟨?_, ?_⟩, fun m hm => ?_⟩
  · rw [unit_lift, hP.inl_desc]
  · rw [unit_lift, hP.inr_desc]
  · exact lift_unique hc hW _ m (hP.hom_ext (by rw [hm.1, hP.inl_desc])
      (by rw [hm.2, hP.inr_desc]))

/-- The closure of a pushout of states that satisfy the keys is their pushout among
the states that satisfy the keys. -/
theorem isPushout_closure (hX : X.Keys) (hY : Y.Keys) (hZ : Z.Keys)
    (hP : IsPushout f g inl inr) (hc : P.Consistent) :
    IsPushout (C := (keyed S K).FullSubcategory) (Z := ⟨Z, hZ⟩) (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩)
      (P := ⟨P.closure hc, closure_keys hc⟩) f g (show X ⟶ P.closure hc from inl ≫ P.unit hc)
      (show Y ⟶ P.closure hc from inr ≫ P.unit hc) := by
  have w : f ≫ inl ≫ P.unit hc = g ≫ inr ≫ P.unit hc := by
    rw [← Category.assoc, hP.w, Category.assoc]
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk (C := (keyed S K).FullSubcategory) _
    (fun s => lift hc s.pt.property (hP.desc s.inl s.inr s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    change (inl ≫ P.unit hc) ≫ lift hc s.pt.property (hP.desc s.inl s.inr s.condition) = s.inl
    rw [Category.assoc, unit_lift, hP.inl_desc]
  · intro s
    change (inr ≫ P.unit hc) ≫ lift hc s.pt.property (hP.desc s.inl s.inr s.condition) = s.inr
    rw [Category.assoc, unit_lift, hP.inr_desc]
  · intro s m h₁ h₂
    refine lift_unique hc s.pt.property _ m (hP.hom_ext ?_ ?_)
    · rw [hP.inl_desc, ← Category.assoc]
      exact h₁
    · rw [hP.inr_desc, ← Category.assoc]
      exact h₂

/-! ## Limits -/

section Limits

variable {J : Type} [SmallCategory J] (F : J ⥤ S.State K)

/-- The limit of a non-empty diagram of states that satisfy the keys satisfies
them: two elements that agree on the fields of a key agree in every member. -/
theorem limitState_keys [Nonempty J] (h : ∀ j, (F.obj j).Keys) : (limitState F).Keys := by
  intro k hk he x y hxy
  have he' : ∀ j, x.elem j = y.elem j := fun j =>
    h j k hk he _ _ fun n hn b hb =>
      congrArg (fun z : LimitElem F _ => z.elem j) (hxy n hn b hb)
  apply LimitElem.ext
  · obtain ⟨j⟩ := ‹Nonempty J›
    rw [← x.agree j, ← y.agree j, he' j]
  · funext j
    exact he' j

/-- A limit of a non-empty diagram of states that satisfy the keys satisfies
them. -/
theorem keys_of_isLimit [Nonempty J] {c : Cone F} (hc : IsLimit c)
    (h : ∀ j, (F.obj j).Keys) : c.pt.Keys :=
  Keys.of_iso (hc.conePointUniqueUpToIso (limitConeIsLimit F)).symm (limitState_keys F h)

end Limits

end State

end Schema

/-! ## `Σ_T` on states that satisfy the keys -/

namespace Translation

open Schema

variable {T : Translation} {S S' : Schema} {hS' : S'.WellFormed} {hT : T.Valid S S'}
  {K : ValueType → Type} (hb : AttrBijective hS' hT)

/-- Under `AttrBijective`, morphisms from the closure of `Σ_T X` into a state that
satisfies the keys are the morphisms from `X` into its restriction. -/
noncomputable def sigmaClosureHomEquiv (X : S.State K)
    (hc : ((sigmaStateFunctor hb).obj X).Consistent) {Y : S'.State K} (hY : Y.Keys) :
    (((sigmaStateFunctor hb).obj X).closure hc ⟶ Y) ≃ (X ⟶ restrictState hS' hT Y) :=
  (State.closureHomEquiv hc hY).trans ((sigmaStateAdjunction hb).homEquiv X Y)

/-- The states `X` of `S` whose `Σ_T X` is consistent. -/
def sigmaConsistent : ObjectProperty (S.State K) :=
  fun X => ((sigmaStateFunctor hb).obj X).Consistent

/-- `Σ_T` of the restriction of a state that satisfies the keys is consistent. -/
theorem sigmaConsistent_restrict {Y : S'.State K} (hY : Y.Keys) :
    sigmaConsistent hb (restrictState hS' hT Y) :=
  State.consistent_of_hom ((sigmaStateAdjunction hb).counit.app Y) hY

/-- `Σ_T X` is consistent exactly when `X` has a morphism into the restriction of a
state that satisfies the keys. -/
theorem sigmaConsistent_iff (X : S.State K) :
    sigmaConsistent hb X ↔
      ∃ Y : S'.State K, Y.Keys ∧ Nonempty (X ⟶ restrictState hS' hT Y) :=
  ⟨fun h => ⟨_, State.closure_keys h,
      ⟨sigmaClosureHomEquiv hb X h (State.closure_keys h) (𝟙 _)⟩⟩,
    fun ⟨_, hY, ⟨f⟩⟩ =>
      State.consistent_of_hom (((sigmaStateAdjunction hb).homEquiv X _).symm f) hY⟩

/-- `Δ_T` from the states of `S'` that satisfy the keys to the states of `S` whose
`Σ_T` is consistent. -/
def keyedRestrict : (keyed S' K).FullSubcategory ⥤ (sigmaConsistent (K := K) hb).FullSubcategory :=
  ObjectProperty.lift _ ((keyed S' K).ι ⋙ restrictStateFunctor hS' hT)
    fun Y => sigmaConsistent_restrict hb Y.property

/-- The closure of `Σ_T X`, as a state that satisfies the keys. -/
noncomputable def keyedSigmaObj (X : (sigmaConsistent (K := K) hb).FullSubcategory) :
    (keyed S' K).FullSubcategory :=
  ⟨((sigmaStateFunctor hb).obj X.obj).closure X.property, State.closure_keys X.property⟩

noncomputable def keyedSigmaEquiv (X : (sigmaConsistent (K := K) hb).FullSubcategory)
    (Y : (keyed S' K).FullSubcategory) :
    (keyedSigmaObj hb X ⟶ Y) ≃ (X ⟶ (keyedRestrict hb).obj Y) :=
  sigmaClosureHomEquiv hb X.obj X.property Y.property

theorem keyedSigmaEquiv_naturality (X : (sigmaConsistent (K := K) hb).FullSubcategory)
    (Y Y' : (keyed S' K).FullSubcategory) (g : Y ⟶ Y') (h : keyedSigmaObj hb X ⟶ Y) :
    keyedSigmaEquiv hb X Y' (h ≫ g) = keyedSigmaEquiv hb X Y h ≫ (keyedRestrict hb).map g := by
  change (sigmaStateAdjunction hb).homEquiv X.obj Y'.obj
      (State.unit X.property ≫ (h ≫ g)) =
    (sigmaStateAdjunction hb).homEquiv X.obj Y.obj (State.unit X.property ≫ h) ≫
      (restrictStateFunctor hS' hT).map g
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]

/-- `Σ_T` on states that satisfy the keys: the closure of `Σ_T X`, on the states
whose `Σ_T X` is consistent. -/
noncomputable def keyedSigma :
    (sigmaConsistent (K := K) hb).FullSubcategory ⥤ (keyed S' K).FullSubcategory :=
  Adjunction.leftAdjointOfEquiv (keyedSigmaEquiv hb) (keyedSigmaEquiv_naturality hb)

/-- The closure of `Σ_T` is left adjoint to `Δ_T` from the states that satisfy the
keys. -/
noncomputable def keyedSigmaAdjunction : keyedSigma (K := K) hb ⊣ keyedRestrict hb :=
  Adjunction.adjunctionOfEquivLeft (keyedSigmaEquiv hb) (keyedSigmaEquiv_naturality hb)

end Translation

end DDD
