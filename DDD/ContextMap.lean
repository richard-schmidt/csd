import DDD.Compose
import DDD.Glue
import Mathlib.CategoryTheory.Category.Cat.Op
import Mathlib.CategoryTheory.Grothendieck

/-!
# Context maps and their integrations

A context map is a quiver of contexts, with an arrow `u ⟶ d` from each upstream
context `u` to each downstream context `d` it serves, a well-formed schema per
context, a valid translation per arrow, from the upstream schema to the
downstream one, declared equations between routes, and the contexts marked as
kernels.

- `ContextMap.J`: the category of contexts, the free category on the arrows
  (`Paths`) quotiented by the declared equations between routes (`routeEqns`).
  Without declarations it is the free category.
- `ContextMap.diagram`: the functor `D : J ⥤ Cat`, sending each context to its
  schema category, each arrow to the functor of its translation, and each route
  to the composite. It is defined on the quotient because routes declared equal
  have the same composite (`coherent`).
- Coherence by check: `routeTranslation p` is the composite translation along a
  route, and its functor is the functor of the route (`routeDiagram_map`).
  Equations declared as a list of `RouteEqn` are checked by `checkRouteEqn`;
  `coherent_of_check` gives `coherent` from the checks, and
  `routeDiagram_map_ne` refutes an equation whose check fails.
- `ContextMap.Lax`: the lax integration, `(Grothendieck (D ⋙ Cat.opFunctor))ᵒᵖ`.
  `embed c` includes the schema of the context `c`. A reference from `x` in a
  downstream context `d` to `y` in an upstream context `u` is a morphism
  `f : u ⟶ d` of `J` and a morphism `x ⟶ D f y` in the schema of `d`
  (`ContextMap.ref`). `projection` is the dependency graph of the contexts,
  onto `Jᵒᵖ`.
- `nonInterference`: if no context has an endomorphism in `J` other than the
  identity, every context embeds fully faithfully and injectively on objects.
  `endo_eq_id_of_rank` gives the hypothesis on the free category for every
  context map with a rank that increases along its arrows, so for every map
  without cycles, and `ContextMap.endo_eq_id` carries it to `J`.
- Published languages: `Publishes f` for an arrow `f : p ⟶ o` states that `f`
  includes `p` in its owner `o` and that `p` contains roots of `o` only
  (`Schema.RootsOnly`); it is decidable.
- Strict integration: every arrow out of a context marked as a kernel is the
  empty translation, an inclusion that keeps names. Two arrows out of a kernel
  whose targets share nothing outside it glue (`kernelGluing`); the kernel span
  of the gluing is the image of the two arrows under `D`
  (`kernelGluing_ι₁`, `kernelGluing_ι₂`), so the glued schema category is the
  pushout of that span in `Cat` (`isPushout_kernel`).
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

/-- If every endomorphism of a category is an identity, so is every endomorphism
of a quotient of it. -/
theorem Quotient.endo_eq_id {B : Type*} [Category B] {r : HomRel B}
    (h : ∀ (b : B) (f : b ⟶ b), f = 𝟙 b) :
    ∀ (c : CategoryTheory.Quotient r) (f : c ⟶ c), f = 𝟙 c := by
  rintro ⟨c⟩ f
  obtain ⟨g, rfl⟩ := (CategoryTheory.Quotient.functor r).map_surjective f
  rw [h c g, CategoryTheory.Functor.map_id]
  rfl

section Routes

variable {C : Type} [Quiver.{1} C]

/-- The functor on the free category of the arrows: each context to its schema
category, each arrow to the functor of its translation, and each route to the
composite. -/
def routeDiagram (schema : C → Schema) (translation : ∀ {u d : C}, (u ⟶ d) → Translation)
    (wellFormed : ∀ c, (schema c).WellFormed)
    (valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d)) :
    Paths C ⥤ Cat.{0, 0} :=
  Paths.lift
    { obj c := (schema c).cat
      map f := (translation f).functor (wellFormed _) (valid f) }

/-- The composite of the translations along a route, as finite data. -/
def routeTranslation (schema : C → Schema) (translation : ∀ {u d : C}, (u ⟶ d) → Translation)
    {u : C} : ∀ {d : C}, Quiver.Path u d → Translation
  | _, .nil => {}
  | _, .cons (b := b) p f =>
    (routeTranslation schema translation p).comp (schema u) (schema b) (translation f)

@[simp] theorem routeTranslation_nil (schema : C → Schema)
    (translation : ∀ {u d : C}, (u ⟶ d) → Translation) (u : C) :
    routeTranslation schema translation (Quiver.Path.nil : Quiver.Path u u) = {} := rfl

@[simp] theorem routeTranslation_cons (schema : C → Schema)
    (translation : ∀ {u d : C}, (u ⟶ d) → Translation) {u b d : C} (p : Quiver.Path u b)
    (f : b ⟶ d) :
    routeTranslation schema translation (p.cons f) =
      (routeTranslation schema translation p).comp (schema u) (schema b) (translation f) := rfl

variable {schema : C → Schema} {translation : ∀ {u d : C}, (u ⟶ d) → Translation}

theorem routeTranslation_valid (wellFormed : ∀ c, (schema c).WellFormed)
    (valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d)) :
    {u : C} → ∀ {d : C} (p : Quiver.Path u d),
      (routeTranslation schema translation p).Valid (schema u) (schema d)
  | u, _, .nil => by
    rw [routeTranslation_nil]
    exact Translation.empty_valid_self (wellFormed u)
  | u, _, .cons p f => by
    rw [routeTranslation_cons]
    exact Translation.comp_valid (wellFormed u) (wellFormed _)
      (routeTranslation_valid wellFormed valid p) (valid f)

/-- The functor of a route is the functor of the composite translation along it. -/
theorem routeDiagram_map (wellFormed : ∀ c, (schema c).WellFormed)
    (valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d))
    {u d : C} (p : Quiver.Path u d) :
    (routeDiagram schema translation wellFormed valid).map p =
      Translation.functor (wellFormed d) (routeTranslation_valid wellFormed valid p) := by
  induction p with
  | nil =>
    refine (Paths.lift_nil _ _).trans ?_
    rw [Translation.functor_congr (wellFormed u) _ (Translation.empty_valid_self (wellFormed u))
      (routeTranslation_nil schema translation u), Translation.functor_empty_self]
    rfl
  | cons p f ih =>
    refine (Paths.lift_cons _ _ _).trans ?_
    change (routeDiagram schema translation wellFormed valid).map p ≫ _ = _
    rw [ih, Translation.functor_congr (wellFormed _) _
      (Translation.comp_valid (wellFormed u) (wellFormed _)
        (routeTranslation_valid wellFormed valid p) (valid f))
        (routeTranslation_cons schema translation p f),
      Translation.functor_comp (wellFormed u) (wellFormed _) (wellFormed _)]
    rfl

/-- An equation between two routes with the same endpoints. -/
structure RouteEqn (C : Type) [Quiver.{1} C] where
  src : C
  tgt : C
  lhs : Quiver.Path src tgt
  rhs : Quiver.Path src tgt

/-- The relation on routes that a list of equations declares. -/
def RouteEqn.rel (eqns : List (RouteEqn C)) : HomRel (Paths C) :=
  fun u d p q => (⟨u, d, p, q⟩ : RouteEqn C) ∈ eqns

variable (schema translation) in
/-- The check for a declared equation: the composite translations along its two
routes induce the same functor. -/
def checkRouteEqn (e : RouteEqn C) : Bool :=
  (routeTranslation schema translation e.lhs).checkSameFunctor
    (routeTranslation schema translation e.rhs) (schema e.src) (schema e.tgt).pathEq

/-- Coherence by check: when every declared equation passes `checkRouteEqn`, the
translations respect the declarations. -/
theorem coherent_of_check (wellFormed : ∀ c, (schema c).WellFormed)
    (valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d))
    (eqns : List (RouteEqn C)) (h : ∀ e ∈ eqns, checkRouteEqn schema translation e = true) :
    ∀ ⦃u d : Paths C⦄ (p q : u ⟶ d), RouteEqn.rel eqns p q →
      (routeDiagram schema translation wellFormed valid).map p =
        (routeDiagram schema translation wellFormed valid).map q := by
  intro u d p q hpq
  rw [routeDiagram_map wellFormed valid p, routeDiagram_map wellFormed valid q]
  exact Translation.checkSameFunctor_sound (wellFormed d) _ _
    (fun a _ _ h => Schema.pathEq_sound (wellFormed d) a h) (h _ hpq)

/-- When path equality in the target is decided, a failed check refutes the
equation: the two routes have different functors. -/
theorem routeDiagram_map_ne (wellFormed : ∀ c, (schema c).WellFormed)
    (valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d))
    (e : RouteEqn C)
    (hpeq : ∀ (a : (schema e.tgt).Obj) (l l' : List String),
      (schema e.tgt).pathEq a.1 l l' = true ↔ (schema e.tgt).PathEq a l l')
    (h : checkRouteEqn schema translation e = false) :
    (routeDiagram schema translation wellFormed valid).map e.lhs ≠
      (routeDiagram schema translation wellFormed valid).map e.rhs := by
  intro hm
  rw [routeDiagram_map wellFormed valid, routeDiagram_map wellFormed valid] at hm
  have := (Translation.checkSameFunctor_iff (wellFormed e.src) (wellFormed e.tgt) _ _ hpeq).mpr hm
  simp [checkRouteEqn, this] at h

end Routes

/-- A context map on the contexts `C`: a well-formed schema per context, a valid
translation per arrow, from the upstream schema to the downstream one, the
declared equations between routes, which the translations respect, and the
contexts marked as kernels, out of which every arrow is an inclusion. By default
no equation is declared and no context is a kernel. -/
structure ContextMap (C : Type) [Quiver.{1} C] where
  schema : C → Schema
  translation : ∀ {u d : C}, (u ⟶ d) → Translation
  wellFormed : ∀ c, (schema c).WellFormed
  valid : ∀ {u d : C} (f : u ⟶ d), (translation f).Valid (schema u) (schema d)
  /-- The declared equations between routes. -/
  routeEqns : HomRel (Paths C) := fun _ _ _ _ => False
  /-- Routes declared equal have the same composite functor. -/
  coherent : ∀ ⦃u d : Paths C⦄ (p q : u ⟶ d), routeEqns p q →
      (routeDiagram schema translation wellFormed valid).map p =
        (routeDiagram schema translation wellFormed valid).map q := by
    intro _ _ _ _ h
    cases h
  /-- The contexts marked as kernels. -/
  kernel : C → Bool := fun _ => false
  /-- Every arrow out of a kernel is the empty translation. -/
  inclusion : ∀ {u d : C} (f : u ⟶ d), kernel u = true → translation f = {} := by
    intro _ _ _ h
    cases h

namespace ContextMap

variable {C : Type} [Quiver.{1} C] (M : ContextMap C)

/-! ## The category of contexts and the diagram -/

/-- The diagram on the free category of the arrows, before the declared
equations. -/
def freeDiagram : Paths C ⥤ Cat.{0, 0} :=
  routeDiagram M.schema M.translation M.wellFormed M.valid

/-- The category of contexts: the free category on the arrows, quotiented by the
declared equations between routes. -/
def J : Type := CategoryTheory.Quotient M.routeEqns

instance : Category M.J := inferInstanceAs (Category (CategoryTheory.Quotient M.routeEqns))

/-- A context, as an object of `J`. -/
def ctx (c : C) : M.J := ⟨c⟩

/-- A route, as a morphism of `J`. -/
def route {u d : C} (p : Quiver.Path u d) : M.ctx u ⟶ M.ctx d :=
  (CategoryTheory.Quotient.functor M.routeEqns).map p

/-- An arrow, as a morphism of `J`. -/
def arrow {u d : C} (f : u ⟶ d) : M.ctx u ⟶ M.ctx d := M.route f.toPath

/-- Routes declared equal are equal in `J`. -/
theorem route_eq {u d : C} {p q : Quiver.Path u d} (h : M.routeEqns p q) :
    M.route p = M.route q :=
  CategoryTheory.Quotient.sound _ h

/-- Every morphism of `J` is a route. -/
theorem route_surjective {u d : C} (f : M.ctx u ⟶ M.ctx d) :
    ∃ p : Quiver.Path u d, M.route p = f :=
  (CategoryTheory.Quotient.functor M.routeEqns).map_surjective f

/-- The diagram `D : J ⥤ Cat` of a context map. -/
def diagram : M.J ⥤ Cat.{0, 0} :=
  CategoryTheory.Quotient.lift M.routeEqns M.freeDiagram fun _ _ p q h => M.coherent p q h

theorem diagram_obj (c : C) : M.diagram.obj (M.ctx c) = (M.schema c).cat := rfl

theorem diagram_map_route {u d : C} (p : Quiver.Path u d) :
    M.diagram.map (M.route p) = M.freeDiagram.map p := rfl

theorem diagram_map_arrow {u d : C} (f : u ⟶ d) :
    M.diagram.map (M.arrow f) = (M.translation f).functor (M.wellFormed _) (M.valid f) :=
  Paths.lift_toPath _ _

/-- If the only route from each context to itself is the empty one, every
endomorphism of `J` is an identity. -/
theorem endo_eq_id (h : ∀ (c : Paths C) (f : c ⟶ c), f = 𝟙 c) :
    ∀ (c : M.J) (f : c ⟶ c), f = 𝟙 c :=
  Quotient.endo_eq_id h

/-! ## Lax integration -/

/-- The lax integration: the contravariant Grothendieck construction of the
diagram. -/
def Lax : Type := (Grothendieck (M.diagram ⋙ Cat.opFunctor))ᵒᵖ

instance : Category M.Lax :=
  inferInstanceAs (Category (Grothendieck (M.diagram ⋙ Cat.opFunctor))ᵒᵖ)

/-- The schema of the context `c` inside the lax integration. -/
def embed (c : C) : (M.schema c).cat ⥤ M.Lax :=
  (Grothendieck.ι (M.diagram ⋙ Cat.opFunctor) (M.ctx c)).rightOp

/-- A reference from `x` in the downstream context `d` to `y` in the upstream
context `u`: a morphism `f : u ⟶ d` of `J` and a morphism `x ⟶ D f y` in the
schema of `d`. -/
def ref {u d : C} (f : M.ctx u ⟶ M.ctx d) {x : (M.schema d).cat} {y : (M.schema u).cat}
    (φ : x ⟶ (M.diagram.map f).obj y) : (M.embed d).obj x ⟶ (M.embed u).obj y :=
  Quiver.Hom.op (⟨f, φ.op⟩ : CategoryTheory.Grothendieck.Hom (F := M.diagram ⋙ Cat.opFunctor)
    ⟨M.ctx u, Opposite.op y⟩ ⟨M.ctx d, Opposite.op x⟩)

/-- The dependency graph of the contexts: the projection of the lax integration
onto `Jᵒᵖ`. -/
def projection : M.Lax ⥤ M.Jᵒᵖ :=
  (Grothendieck.forget (M.diagram ⋙ Cat.opFunctor)).op

theorem projection_ref {u d : C} (f : M.ctx u ⟶ M.ctx d) {x : (M.schema d).cat}
    {y : (M.schema u).cat} (φ : x ⟶ (M.diagram.map f).obj y) :
    M.projection.map (M.ref f φ) = f.op := rfl

instance (c : C) : (M.embed c).Faithful :=
  @Functor.rightOp_faithful _ _ _ _ (Grothendieck.ι (M.diagram ⋙ Cat.opFunctor) (M.ctx c))
    (CategoryTheory.Grothendieck.faithful_ι (F := M.diagram ⋙ Cat.opFunctor) (M.ctx c))

theorem embed_injective (c : C) : Function.Injective (M.embed c).obj := by
  intro x y h
  have h₁ := congrArg Opposite.unop h
  change (⟨M.ctx c, Opposite.op x⟩ : Grothendieck (M.diagram ⋙ Cat.opFunctor)) =
    ⟨M.ctx c, Opposite.op y⟩ at h₁
  injection h₁ with _ h₂
  exact Opposite.op_injective h₂

/-- Lax non-interference: if no context has an endomorphism in `J` other than the
identity, every context embeds into the lax integration fully faithfully and
injectively on objects. -/
theorem nonInterference (hJ : ∀ (c : M.J) (f : c ⟶ c), f = 𝟙 c) (c : C) :
    (M.embed c).Full ∧ (M.embed c).Faithful ∧ Function.Injective (M.embed c).obj := by
  refine ⟨?_, inferInstance, M.embed_injective c⟩
  exact @Functor.rightOp_full _ _ _ _ (Grothendieck.ι (M.diagram ⋙ Cat.opFunctor) (M.ctx c))
    (Grothendieck.ι_full (M.diagram ⋙ Cat.opFunctor) hJ (M.ctx c))

/-! ## Published languages -/

/-- The arrow `f : p ⟶ o` presents `p` as a published language of `o`: `f` is
the empty translation, and `p` contains roots of `o` only. -/
def Publishes {p o : C} (f : p ⟶ o) : Prop :=
  M.translation f = {} ∧ (M.schema p).RootsOnly (M.schema o)

instance {p o : C} (f : p ⟶ o) : Decidable (M.Publishes f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Strict integration along kernels -/

/-- An arrow out of a kernel includes the schema of the kernel with the same
names. -/
theorem valid_empty {k d : C} (f : k ⟶ d) (hk : M.kernel k = true) :
    ({} : Translation).Valid (M.schema k) (M.schema d) :=
  M.inclusion f hk ▸ M.valid f

variable {k d₁ d₂ : C} (f₁ : k ⟶ d₁) (f₂ : k ⟶ d₂) (hk : M.kernel k = true)
  (hc : Schema.gluingClashes (M.schema k) (M.schema d₁) (M.schema d₂) = [])
  (hwf : (Schema.glue (M.schema d₁) (M.schema d₂)).WellFormed)

/-- The targets of two arrows out of a kernel, glued along it. The conditions:
the targets share no name outside the kernel, and the glued schema is well
formed. -/
def kernelGluing : Gluing where
  kernel := M.schema k
  left := M.schema d₁
  right := M.schema d₂
  wf_kernel := M.wellFormed k
  wf_left := M.wellFormed d₁
  wf_right := M.wellFormed d₂
  wf_glued := hwf
  gluable :=
    ⟨M.valid_empty f₁ hk, M.valid_empty f₂ hk, (Schema.gluingClashes_eq_nil_iff.mp hc).1,
      (Schema.gluingClashes_eq_nil_iff.mp hc).2⟩

/-- The first leg of the kernel span is the image of the first arrow under `D`. -/
theorem kernelGluing_ι₁ : (M.kernelGluing f₁ f₂ hk hc hwf).ι₁ = M.diagram.map (M.arrow f₁) := by
  rw [diagram_map_arrow]
  exact Translation.functor_congr _ _ _ (M.inclusion f₁ hk).symm

/-- The second leg of the kernel span is the image of the second arrow under
`D`. -/
theorem kernelGluing_ι₂ : (M.kernelGluing f₁ f₂ hk hc hwf).ι₂ = M.diagram.map (M.arrow f₂) := by
  rw [diagram_map_arrow]
  exact Translation.functor_congr _ _ _ (M.inclusion f₂ hk).symm

/-- Strict integration along a kernel: the glued schema category is the pushout
in `Cat` of the images under `D` of the two arrows out of the kernel. -/
theorem isPushout_kernel :
    IsPushout (M.diagram.map (M.arrow f₁)) (M.diagram.map (M.arrow f₂))
      (M.kernelGluing f₁ f₂ hk hc hwf).inl (M.kernelGluing f₁ f₂ hk hc hwf).inr := by
  rw [← kernelGluing_ι₁, ← kernelGluing_ι₂]
  exact (M.kernelGluing f₁ f₂ hk hc hwf).isPushout

end ContextMap

end DDD
