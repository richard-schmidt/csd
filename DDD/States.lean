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
- Attributed states, `Schema.State K S`, in the strict formulation: functors that
  send each value type `v` to `K v`, and morphisms that are the identity on value
  types. Entities have an identity independent of their attributes, values do
  not. `Translation.restrictState` is `Δ_T` on them; translations send value types
  to themselves, so it needs no condition. `Σ_T` is not the left Kan extension
  here: a path from a translated entity type to a value type that `S` lacks would
  receive formal values instead of values in `K`.

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

/-- A state of `S` with values in `K`, in the strict formulation: a functor from the
schema category to types that sends each value type `v` to `K v`. -/
@[ext]
structure State (K : ValueType → Type) (S : Schema) where
  F : S.cat ⥤ Type
  values : ∀ v, F.obj (S.obj ⟨.value v, trivial⟩) = K v

variable {K : ValueType → Type} {S : Schema}

/-- A morphism of states: a natural transformation that is the identity on value
types. -/
@[ext]
structure State.Hom (X Y : S.State K) where
  α : X.F ⟶ Y.F
  values : ∀ v, α.app (S.obj ⟨.value v, trivial⟩) = eqToHom ((X.values v).trans (Y.values v).symm)

instance : Category (S.State K) where
  Hom := State.Hom
  id X := ⟨𝟙 X.F, fun v => by simp⟩
  comp f g := ⟨f.α ≫ g.α, fun v => by simp [f.values, g.values]⟩
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

/-- `Δ_T` on attributed states: the values stay where they are, since `T` sends
value types to themselves. -/
def restrictState (hS' : S'.WellFormed) (hT : T.Valid S S') (X : S'.State K) : S.State K where
  F := functor hS' hT ⋙ X.F
  values v := X.values v

/-- `Δ_T` on attributed states, as a functor. -/
def restrictStateFunctor (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S'.State K ⥤ S.State K where
  obj := restrictState hS' hT
  map f := ⟨Functor.whiskerLeft (functor hS' hT) f.α, fun v => f.values v⟩

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
    Schema.State.ext (congrArg (· ⋙ X.F) D.comm)⟩
  invFun P :=
    { F := D.desc (congrArg Schema.State.F P.2)
      values := fun v => (D.descObj_left (F₁ := P.1.1.F) (F₂ := P.1.2.F) ⟨.value v, trivial⟩
        trivial).trans (P.1.1.values v) }
  left_inv X := by
    apply Schema.State.ext
    have hF : D.ι₁ ⋙ (D.inl ⋙ X.F) = D.ι₂ ⋙ (D.inr ⋙ X.F) := congrArg (· ⋙ X.F) D.comm
    exact (D.desc_unique hF X.F rfl rfl).symm
  right_inv P := by
    obtain ⟨⟨P₁, P₂⟩, hP⟩ := P
    have hF : D.ι₁ ⋙ P₁.F = D.ι₂ ⋙ P₂.F := congrArg Schema.State.F hP
    apply Subtype.ext
    apply Prod.ext
    · apply Schema.State.ext
      exact D.inl_desc hF
    · apply Schema.State.ext
      exact D.inr_desc hF

end Gluing

end DDD
