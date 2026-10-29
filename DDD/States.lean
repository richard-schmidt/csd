import DDD.Glue
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# States

A state of a schema is the data of one context: a set of entities for each entity
type, a function for each generator, and the equations satisfied.

- Entity-only states, `Schema.EntityState S`: functors `S.cat ⥤ Type`, with no
  condition on value types. A translation moves them by restriction
  `Translation.restrict` (`Δ_T`) and by its adjoints `Translation.sigma` (`Σ_T`,
  left Kan extension) and `Translation.pi` (`Π_T`, right Kan extension).
- Attributed states, `Schema.State K S`: functors with a bijection between the
  set at each value type `v` and `K v`, and morphisms that commute with the
  bijections, so they are the identity on values. Entities have an identity
  independent of their attributes, values do not. `Translation.restrictState`
  is `Δ_T` on them; translations send value types to themselves, so it needs no
  condition. `Σ_T` is not the left Kan extension here: a path from a translated
  entity type to a value type that `S` lacks would receive formal values
  instead of values in `K`. `StateSigma.lean` gives `Σ_T` on attributed states
  under the condition that excludes such paths; `StateLimits.lean` gives their
  limits and colimits.

Data gluing: the states of a glued schema correspond to pairs of states of the two
schemas with equal restrictions to the kernel, for entity-only states
(`Gluing.entityStateEquiv`, the bridge theorem with `X = Type`) and for attributed
states (`Gluing.stateEquiv`).
-/

namespace DDD

open CategoryTheory

namespace Schema

/-- The entity-only states of a schema: functors from its category to types. -/
abbrev EntityState (S : Schema) : Type 1 := S.cat ⥤ Type

/-- A state of `S` with values in `K`: a functor from the schema category to types,
with a bijection between the set at each value type `v` and `K v`. Reading an
attribute value is applying the bijection. -/
structure State (K : ValueType → Type) (S : Schema) where
  F : S.cat ⥤ Type
  values : ∀ v, F.obj (S.obj ⟨.value v, trivial⟩) ≃ K v

variable {K : ValueType → Type} {S : Schema}

/-- Two states are equal when their functors are equal and their bijections agree
along that equality. -/
theorem State.ext' {X Y : S.State K} (hF : X.F = Y.F)
    (hv : ∀ v (x : X.F.obj (S.obj ⟨.value v, trivial⟩)),
      Y.values v (cast (by rw [hF]) x) = X.values v x) : X = Y := by
  obtain ⟨F, vX⟩ := X
  obtain ⟨G, vY⟩ := Y
  obtain rfl : F = G := hF
  congr
  funext v
  ext x
  exact (hv v x).symm

/-- Equal states have bijections that agree along the equality of their functors. -/
theorem State.values_eq {X Y : S.State K} (h : X = Y) (v : ValueType)
    (x : X.F.obj (S.obj ⟨.value v, trivial⟩)) :
    Y.values v (cast (by rw [h]) x) = X.values v x := by
  subst h
  rfl

/-- A morphism of states: a natural transformation that commutes with the
bijections, so it is the identity on values. -/
@[ext]
structure State.Hom (X Y : S.State K) where
  α : X.F ⟶ Y.F
  values : ∀ v x, Y.values v (α.app (S.obj ⟨.value v, trivial⟩) x) = X.values v x

instance : Category (S.State K) where
  Hom := State.Hom
  id X := ⟨𝟙 X.F, fun _ _ => rfl⟩
  comp f g := ⟨f.α ≫ g.α, fun v x => (g.values v _).trans (f.values v x)⟩
  id_comp f := State.Hom.ext (Category.id_comp f.α)
  comp_id f := State.Hom.ext (Category.comp_id f.α)
  assoc f g h := State.Hom.ext (Category.assoc f.α g.α h.α)

end Schema

namespace Translation

variable {T : Translation} {S S' : Schema}

/-- `Σ_T`: left Kan extension along the functor of a translation. -/
noncomputable def sigma (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S.EntityState ⥤ S'.EntityState :=
  (functor hS' hT).lan

/-- `Π_T`: right Kan extension along the functor of a translation. -/
noncomputable def pi (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S.EntityState ⥤ S'.EntityState :=
  (functor hS' hT).ran

/-- `Σ_T ⊣ Δ_T`. -/
noncomputable def sigmaAdjunction (hS' : S'.WellFormed) (hT : T.Valid S S') :
    sigma hS' hT ⊣ restrict hS' hT :=
  (functor hS' hT).lanAdjunction Type

/-- `Δ_T ⊣ Π_T`. -/
noncomputable def piAdjunction (hS' : S'.WellFormed) (hT : T.Valid S S') :
    restrict hS' hT ⊣ pi hS' hT :=
  (functor hS' hT).ranAdjunction Type

variable {K : ValueType → Type}

/-- `Δ_T` on attributed states: the bijections stay where they are, since `T`
sends value types to themselves. -/
def restrictState (hS' : S'.WellFormed) (hT : T.Valid S S') (X : S'.State K) : S.State K where
  F := functor hS' hT ⋙ X.F
  values v := X.values v

/-- `Δ_T` on attributed states, as a functor. -/
def restrictStateFunctor (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S'.State K ⥤ S.State K where
  obj := restrictState hS' hT
  map f := ⟨Functor.whiskerLeft (functor hS' hT) f.α, fun v x => f.values v x⟩

end Translation

namespace Gluing

variable (D : Gluing)

/-- Data gluing for entity-only states: a state of the glued schema is a pair of
states of the two schemas with equal restrictions to the kernel. -/
def entityStateEquiv :
    D.glued.EntityState ≃
      { F : D.left.EntityState × D.right.EntityState // D.ι₁ ⋙ F.1 = D.ι₂ ⋙ F.2 } :=
  D.glueEquiv Type

variable {K : ValueType → Type}

/-- Data gluing for attributed states: a state of the glued schema is a pair of
states of the two schemas with equal restrictions to the kernel. -/
def stateEquiv :
    D.glued.State K ≃ { P : D.left.State K × D.right.State K //
      Translation.restrictState D.wf_left D.gluable.left P.1 =
        Translation.restrictState D.wf_right D.gluable.right P.2 } where
  toFun X := ⟨(Translation.restrictState D.wf_glued D.inl_valid X,
      Translation.restrictState D.wf_glued D.inr_valid X),
    Schema.State.ext' (congrArg (· ⋙ X.F) D.comm) fun _ _ => rfl⟩
  invFun P :=
    { F := D.desc (congrArg Schema.State.F P.2)
      values := fun v => (Equiv.cast (D.descObj_left (F₁ := P.1.1.F) (F₂ := P.1.2.F)
        ⟨.value v, trivial⟩ trivial)).trans (P.1.1.values v) }
  left_inv X := by
    have hF : D.ι₁ ⋙ (D.inl ⋙ X.F) = D.ι₂ ⋙ (D.inr ⋙ X.F) := congrArg (· ⋙ X.F) D.comm
    exact Schema.State.ext' (D.desc_unique hF X.F rfl rfl).symm fun _ _ => rfl
  right_inv P := by
    obtain ⟨⟨P₁, P₂⟩, hP⟩ := P
    have hF : D.ι₁ ⋙ P₁.F = D.ι₂ ⋙ P₂.F := congrArg Schema.State.F hP
    apply Subtype.ext
    apply Prod.ext
    · exact Schema.State.ext' (D.inl_desc hF) fun _ _ => rfl
    · refine Schema.State.ext' (D.inr_desc hF) fun v x => ?_
      have h := Schema.State.values_eq hP v
        (cast (D.descObj_left (F₁ := P₁.F) (F₂ := P₂.F) ⟨.value v, trivial⟩ trivial) x)
      simp only [Translation.restrictState, cast_cast] at h
      exact h

end Gluing

end DDD
