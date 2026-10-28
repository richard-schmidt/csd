import DDD.Translation
import Mathlib.CategoryTheory.Category.Cat.Op
import Mathlib.CategoryTheory.Grothendieck

/-!
# Context maps and lax integration

A context map is a quiver of contexts, with an arrow `u ⟶ d` from each upstream
context `u` to each downstream context `d` it serves, a well-formed schema per
context and a valid translation per arrow, from the upstream schema to the
downstream one.

- `ContextMap.diagram`: the functor `D : J ⥤ Cat` on the free category `J` of the
  arrows (`Paths`), sending each context to its schema category and each arrow
  to the functor of its translation.
- `ContextMap.Lax`: the lax integration, `(Grothendieck (D ⋙ Cat.opFunctor))ᵒᵖ`.
  `embed c` includes the schema of the context `c`. A reference from `x` in a
  downstream context `d` to `y` in an upstream context `u` is a path `f : u ⟶ d`
  of `J` and a morphism `x ⟶ D f y` in the schema of `d` (`ContextMap.ref`).
  `projection` is the dependency graph of the contexts, onto `Jᵒᵖ`.
- `nonInterference`: if no context has an endomorphism in `J` other than the
  identity, every context embeds fully faithfully and injectively on objects.
  `endo_eq_id_of_rank` gives the hypothesis for every context map with a rank
  that increases along its arrows, so for every map without cycles.
-/

namespace DDD

open CategoryTheory

/-- If no object of the base has an endomorphism other than the identity, the
inclusion of each fiber into the Grothendieck construction is full. -/
theorem Grothendieck.ι_full {B : Type*} [Category B] (F : B ⥤ Cat)
    (h : ∀ (b : B) (f : b ⟶ b), f = 𝟙 b) (b : B) : (Grothendieck.ι F b).Full where
  map_surjective {x y} g := by
    obtain ⟨base, fiber⟩ := g
    obtain rfl := h b base
    refine ⟨eqToHom (by simp) ≫ fiber, ?_⟩
    refine CategoryTheory.Grothendieck.ext _ _ rfl ?_
    simp

/-- In a quiver with a rank that increases along every arrow, every endomorphism
in the free category is an identity. -/
theorem endo_eq_id_of_rank {V : Type} [Quiver.{1} V] (rank : V → Nat)
    (hrank : ∀ {a b : V}, (a ⟶ b) → rank a < rank b) :
    ∀ (c : Paths V) (f : c ⟶ c), f = 𝟙 c := by
  have hle : ∀ {a b : V} (p : Quiver.Path a b), rank a + p.length ≤ rank b := by
    intro a b p
    induction p with
    | nil => simp
    | cons _ e ih => have := hrank e; simp only [Quiver.Path.length_cons]; omega
  intro c f
  have := hle (a := c) (b := c) f
  exact Quiver.Path.eq_nil_of_length_zero f (by omega)

/-- A context map on the contexts `C`: a well-formed schema per context and a
valid translation per arrow, from the upstream schema to the downstream one. -/
structure ContextMap (C : Type) [Quiver.{1} C] where
  schema : C → Schema
  translation : ∀ {u d : C}, (u ⟶ d) → Translation
  wellFormed : ∀ c, (schema c).WellFormed
  valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d)

namespace ContextMap

variable {C : Type} [Quiver.{1} C] (M : ContextMap C)

/-- Each context to its schema category, each arrow to the functor of its
translation. -/
def prefunctor : C ⥤q Cat.{0, 0} where
  obj c := (M.schema c).cat
  map f := (M.translation f).functor (M.wellFormed _) (M.valid f)

/-- The diagram `D : J ⥤ Cat` of a context map, on the free category `J` of its
arrows. -/
def diagram : Paths C ⥤ Cat.{0, 0} := Paths.lift M.prefunctor

theorem diagram_obj (c : C) : M.diagram.obj c = (M.schema c).cat := rfl

theorem diagram_map_toPath {u d : C} (f : u ⟶ d) :
    M.diagram.map f.toPath = (M.translation f).functor (M.wellFormed _) (M.valid f) :=
  Paths.lift_toPath _ _

/-- The lax integration: the contravariant Grothendieck construction of the
diagram. -/
def Lax : Type := (Grothendieck (M.diagram ⋙ Cat.opFunctor))ᵒᵖ

instance : Category M.Lax :=
  inferInstanceAs (Category (Grothendieck (M.diagram ⋙ Cat.opFunctor))ᵒᵖ)

/-- The schema of the context `c` inside the lax integration. -/
def embed (c : C) : (M.schema c).cat ⥤ M.Lax :=
  (Grothendieck.ι (M.diagram ⋙ Cat.opFunctor) c).rightOp

/-- A reference from `x` in the downstream context `d` to `y` in the upstream
context `u`: a path `f : u ⟶ d` of `J` and a morphism `x ⟶ D f y` in the schema
of `d`. -/
def ref {u d : Paths C} (f : u ⟶ d) {x : (M.schema d).cat} {y : (M.schema u).cat}
    (φ : x ⟶ (M.diagram.map f).obj y) : (M.embed d).obj x ⟶ (M.embed u).obj y :=
  Quiver.Hom.op (⟨f, φ.op⟩ : CategoryTheory.Grothendieck.Hom (F := M.diagram ⋙ Cat.opFunctor)
    ⟨u, Opposite.op y⟩ ⟨d, Opposite.op x⟩)

/-- The dependency graph of the contexts: the projection of the lax integration
onto `Jᵒᵖ`. -/
def projection : M.Lax ⥤ (Paths C)ᵒᵖ :=
  (Grothendieck.forget (M.diagram ⋙ Cat.opFunctor)).op

theorem projection_ref {u d : Paths C} (f : u ⟶ d) {x : (M.schema d).cat}
    {y : (M.schema u).cat} (φ : x ⟶ (M.diagram.map f).obj y) :
    M.projection.map (M.ref f φ) = f.op := rfl

instance (c : C) : (M.embed c).Faithful :=
  @Functor.rightOp_faithful _ _ _ _ (Grothendieck.ι (M.diagram ⋙ Cat.opFunctor) c)
    (CategoryTheory.Grothendieck.faithful_ι (F := M.diagram ⋙ Cat.opFunctor) c)

theorem embed_injective (c : C) : Function.Injective (M.embed c).obj := by
  intro x y h
  have h₁ := congrArg Opposite.unop h
  change (⟨c, Opposite.op x⟩ : Grothendieck (M.diagram ⋙ Cat.opFunctor)) = ⟨c, Opposite.op y⟩ at h₁
  injection h₁ with _ h₂
  exact Opposite.op_injective h₂

/-- Lax non-interference: if no context has an endomorphism in `J` other than the
identity, every context embeds into the lax integration fully faithfully and
injectively on objects. -/
theorem nonInterference (hJ : ∀ (c : Paths C) (f : c ⟶ c), f = 𝟙 c) (c : C) :
    (M.embed c).Full ∧ (M.embed c).Faithful ∧ Function.Injective (M.embed c).obj := by
  refine ⟨?_, inferInstance, M.embed_injective c⟩
  exact @Functor.rightOp_full _ _ _ _ (Grothendieck.ι (M.diagram ⋙ Cat.opFunctor) c)
    (Grothendieck.ι_full (M.diagram ⋙ Cat.opFunctor) hJ c)

end ContextMap

end DDD
