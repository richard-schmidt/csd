import DDD.StateLimits

/-!
# `Σ_T` on attributed states

`Δ_T` on attributed states (`Translation.restrictStateFunctor`) has a left adjoint
exactly when `T` neither adds nor identifies paths into value types: for each
object `a` of `S` and value type `v`, the functor of `T` is a bijection from the
morphisms `a ⟶ v` of `S` onto the morphisms `T a ⟶ v` of `S'`
(`Translation.AttrBijective`).

- Under the condition, `Σ_T X` at an object `b` of `S'` is the quotient of the
  triples `(a, f : T a ⟶ b, x ∈ X a)` that identifies `(a, T h ≫ f, x)` with
  `(a', f, X h x)`; at a value type, the triple `(a, f, x)` has the value of `x`
  along the morphism of `S` that `T` sends to `f` (`Translation.sigmaState`). The
  adjunction is `sigmaStateAdjunction`.
- Conversely, when every `K v` has two elements, a left adjoint makes `Δ_T`
  preserve the terminal state, whose entities are the profiles; the restriction
  of profiles along `T` is then a bijection, and so is `T` on morphisms into each
  value type (`attrBijective_of_isRightAdjoint`). Without the condition, an
  entity whose image has an attribute path that `S` lacks has no value to take
  along it, and one with two paths that `T` identifies has two values that
  would have to agree.

`isRightAdjoint_restrictStateFunctor_iff` states the equivalence. A fully faithful
translation satisfies the condition (`attrBijective_of_fullyFaithful`), so the
check `checkFullyFaithful` decides it for acyclic schemas when it passes; a path
of `S'` out of the image of an entity type to a value type that no path of `S`
out of that entity type reaches refutes it (`not_attrBijective`).
-/

namespace DDD

open CategoryTheory Limits Schema

namespace Translation

variable {T : Translation} {S S' : Schema} (hS' : S'.WellFormed) (hT : T.Valid S S')
  {K : ValueType → Type}

/-- `T` neither adds nor identifies paths into value types: for each object `a` and
value type `v`, the functor of `T` is a bijection from `a ⟶ v` onto `T a ⟶ v`. -/
def AttrBijective : Prop :=
  ∀ (a : S.cat) (v : ValueType),
    Function.Bijective fun g : a ⟶ S.valueObj v => (functor hS' hT).map g

variable {hS' hT}

/-- A fully faithful translation is bijective on paths into value types. -/
theorem attrBijective_of_fullyFaithful (hF : (functor hS' hT).Full)
    (hF' : (functor hS' hT).Faithful) : AttrBijective hS' hT :=
  fun _ _ => ⟨(functor hS' hT).map_injective, (functor hS' hT).map_surjective⟩

/-- A path of `S'` from the image of the entity type `e` to the value type `v`,
when no path of `S` leads from `e` to `v`, refutes the condition. -/
theorem not_attrBijective (hA : S.Acyclic) {e : String}
    (he : e ∈ S.entities) {l : List String} {v : ValueType}
    (hl : S'.tgt? (T.ob (.entity e)) l = some (.value v))
    (hno : (S.paths (.entity e) S.entities.length).all
      (fun l' => S.tgt? (.entity e) l' != some (.value v)) = true) :
    ¬ AttrBijective hS' hT := by
  intro hb
  obtain ⟨b, p', hb', -⟩ := S'.exists_path hS' (obj hT ⟨.entity e, he⟩) l hl
  obtain rfl : b = ⟨.value v, trivial⟩ := Subtype.ext hb'
  obtain ⟨g, -⟩ := (hb (S.obj ⟨.entity e, he⟩) v).2 (Schema.mor p')
  obtain ⟨p, rfl⟩ := S.mor_surjective g
  have hp : S.tgt? (.entity e) (names p) = some (.value v) := tgt?_names p
  have hmem : names p ∈ S.paths (.entity e) S.entities.length :=
    (mem_paths _ _ _).mpr ⟨by simp [hp], hA ⟨.entity e, he⟩ _ (by simp [hp])⟩
  have h := List.all_eq_true.mp hno _ hmem
  simp [hp] at h

variable (hb : AttrBijective hS' hT)

/-- Under `AttrBijective`, the morphism of `S` that `T` sends to `f`. -/
noncomputable def attrEquiv (a : S.cat) (v : ValueType) :
    (a ⟶ S.valueObj v) ≃ ((functor hS' hT).obj a ⟶ S'.valueObj v) :=
  Equiv.ofBijective _ (hb a v)

theorem attrEquiv_apply (a : S.cat) (v : ValueType) (g : a ⟶ S.valueObj v) :
    attrEquiv hb a v g = (functor hS' hT).map g := rfl

@[simp] theorem map_attrEquiv_symm (a : S.cat) (v : ValueType)
    (f : (functor hS' hT).obj a ⟶ S'.valueObj v) :
    (functor hS' hT).map ((attrEquiv hb a v).symm f) = f :=
  (attrEquiv hb a v).apply_symm_apply f

theorem attrEquiv_symm_comp {a a' : S.cat} (h : a ⟶ a') {v : ValueType}
    (f : (functor hS' hT).obj a' ⟶ S'.valueObj v) :
    (attrEquiv hb a v).symm ((functor hS' hT).map h ≫ f) = h ≫ (attrEquiv hb a' v).symm f := by
  rw [Equiv.symm_apply_eq, attrEquiv_apply, Functor.map_comp]
  exact congrArg _ ((attrEquiv hb a' v).apply_symm_apply f).symm

theorem attrEquiv_symm_id (v : ValueType) :
    (attrEquiv hb (S.valueObj v) v).symm (𝟙 ((functor hS' hT).obj (S.valueObj v))) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq, attrEquiv_apply, CategoryTheory.Functor.map_id]

/-! ## The left adjoint -/

variable (X : S.State K)

variable (hS' hT) in
/-- A generator of `Σ_T X` at `b`: an object `a` of `S`, a morphism `T a ⟶ b` and an
element of `X` at `a`. -/
abbrev SigmaPre (b : S'.cat) : Type := Σ a : S.cat, ((functor hS' hT).obj a ⟶ b) × X.F.obj a

variable (hS' hT) in
/-- `(a, T h ≫ f, x)` is related to `(a', f, X h x)`. -/
def SigmaRel (b : S'.cat) (p q : SigmaPre hS' hT X b) : Prop :=
  ∃ h : p.1 ⟶ q.1, p.2.1 = (functor hS' hT).map h ≫ q.2.1 ∧ q.2.2 = X.F.map h p.2.2

variable (hS' hT) in
/-- `Σ_T X` as a functor on `S'`. -/
@[simps]
def sigmaFunctor : S'.cat ⥤ Type where
  obj b := Quot (SigmaRel hS' hT X b)
  map f := Quot.map (fun p => ⟨p.1, p.2.1 ≫ f, p.2.2⟩) fun p q ⟨h, h₁, h₂⟩ =>
    ⟨h, by simp [h₁], h₂⟩
  map_id b := by
    funext q
    induction q using Quot.ind with
    | mk p =>
      obtain ⟨a, f, x⟩ := p
      change Quot.mk _ (⟨a, f ≫ 𝟙 b, x⟩ : SigmaPre hS' hT X b) = Quot.mk _ ⟨a, f, x⟩
      rw [Category.comp_id]
  map_comp f f' := by
    funext q
    induction q using Quot.ind with
    | mk p =>
      obtain ⟨a, f₀, x⟩ := p
      change Quot.mk _ (⟨a, f₀ ≫ f ≫ f', x⟩ : SigmaPre hS' hT X _) =
        Quot.mk _ ⟨a, (f₀ ≫ f) ≫ f', x⟩
      rw [Category.assoc]

/-- The value at `v` of a generator `(a, f, x)`: the value of `x` along the morphism
of `S` that `T` sends to `f`. -/
noncomputable def sigmaValue {v : ValueType} (p : SigmaPre hS' hT X (S'.valueObj v)) :
    K v :=
  X.values v (X.F.map ((attrEquiv hb p.1 v).symm p.2.1) p.2.2)

theorem sigmaValue_id {v : ValueType} (x : X.F.obj (S.valueObj v)) :
    sigmaValue hb X ⟨S.valueObj v, 𝟙 ((functor hS' hT).obj (S.valueObj v)), x⟩ = X.values v x := by
  change X.values v (X.F.map ((attrEquiv hb (S.valueObj v) v).symm
    (𝟙 ((functor hS' hT).obj (S.valueObj v)))) x) = _
  rw [attrEquiv_symm_id, FunctorToTypes.map_id_apply]

theorem sigmaValue_rel {v : ValueType} {p q : SigmaPre hS' hT X (S'.valueObj v)}
    (h : SigmaRel hS' hT X _ p q) : sigmaValue hb X p = sigmaValue hb X q := by
  obtain ⟨h, h₁, h₂⟩ := h
  simp only [sigmaValue, h₁, h₂, attrEquiv_symm_comp, FunctorToTypes.map_comp_apply]

/-- `Σ_T X`, under `AttrBijective`. -/
noncomputable def sigmaState : S'.State K where
  F := sigmaFunctor hS' hT X
  values v :=
    { toFun := Quot.lift (sigmaValue hb X) fun _ _ h => sigmaValue_rel hb X h
      invFun := fun k =>
        Quot.mk _ ⟨S.valueObj v, 𝟙 ((functor hS' hT).obj (S.valueObj v)), (X.values v).symm k⟩
      left_inv := fun q => by
        induction q using Quot.ind with
        | mk p =>
          refine (Quot.sound ⟨(attrEquiv hb p.1 v).symm p.2.1, ?_, ?_⟩).symm
          · simp
          · simp [sigmaValue]
      right_inv := fun k => by
        change sigmaValue hb X _ = k
        rw [sigmaValue_id, Equiv.apply_symm_apply] }

variable {X} {Y : S'.State K}

/-- A morphism out of `Σ_T X` restricts to a morphism out of `X`. -/
noncomputable def sigmaHomEquiv :
    (sigmaState hb X ⟶ Y) ≃ (X ⟶ (restrictStateFunctor hS' hT).obj Y) where
  toFun β :=
    { α :=
        { app := fun a x =>
            β.α.app ((functor hS' hT).obj a) (Quot.mk _ ⟨a, 𝟙 ((functor hS' hT).obj a), x⟩)
          naturality := fun a a' h => by
            funext x
            change β.α.app _ (Quot.mk _ ⟨a', 𝟙 ((functor hS' hT).obj a'), X.F.map h x⟩) =
              Y.F.map ((functor hS' hT).map h)
                (β.α.app _ (Quot.mk _ ⟨a, 𝟙 ((functor hS' hT).obj a), x⟩))
            rw [← FunctorToTypes.naturality]
            exact congrArg _ (Quot.sound ⟨h, by simp, rfl⟩).symm }
      values := fun v x => by
        exact (β.values v _).trans (sigmaValue_id hb X x) }
  invFun γ :=
    { α :=
        { app := fun b => Quot.lift (fun p => Y.F.map p.2.1 (γ.α.app p.1 p.2.2))
            fun p q ⟨h, h₁, h₂⟩ => by
              simp only
              rw [h₁, h₂, FunctorToTypes.map_comp_apply]
              exact congrArg _ (FunctorToTypes.naturality _ _ γ.α h p.2.2).symm
          naturality := fun b b' f => by
            funext q
            induction q using Quot.ind with
            | mk p => exact FunctorToTypes.map_comp_apply Y.F _ _ _ }
      values := fun v q => by
        induction q using Quot.ind with
        | mk p =>
          obtain ⟨a, f, x⟩ := p
          change Y.values v (Y.F.map f (γ.α.app a x)) =
            X.values v (X.F.map ((attrEquiv hb a v).symm f) x)
          have hn := FunctorToTypes.naturality _ _ γ.α ((attrEquiv hb a v).symm f) x
          conv_lhs => rw [← map_attrEquiv_symm hb a v f]
          exact (congrArg (Y.values v) hn.symm).trans (γ.values v _) }
  left_inv β := by
    ext b q
    induction q using Quot.ind with
    | mk p =>
      obtain ⟨a, f, x⟩ := p
      change Y.F.map f (β.α.app _ (Quot.mk _ ⟨a, 𝟙 ((functor hS' hT).obj a), x⟩)) =
        β.α.app b (Quot.mk _ ⟨a, f, x⟩)
      rw [← FunctorToTypes.naturality]
      change β.α.app b (Quot.mk _ ⟨a, 𝟙 ((functor hS' hT).obj a) ≫ f, x⟩) = _
      rw [Category.id_comp]
  right_inv γ := by
    ext a x
    exact FunctorToTypes.map_id_apply Y.F _

/-- `Σ_T` on attributed states, under `AttrBijective`. -/
noncomputable def sigmaStateFunctor : S.State K ⥤ S'.State K :=
  Adjunction.leftAdjointOfEquiv (fun X Y => sigmaHomEquiv hb (X := X) (Y := Y))
    fun _ _ _ _ _ => rfl

/-- `Σ_T ⊣ Δ_T` on attributed states, under `AttrBijective`. -/
noncomputable def sigmaStateAdjunction :
    sigmaStateFunctor hb ⊣ restrictStateFunctor (K := K) hS' hT :=
  Adjunction.adjunctionOfEquivLeft _ _

theorem sigmaStateFunctor_obj (X : S.State K) : (sigmaStateFunctor hb).obj X = sigmaState hb X :=
  rfl

/-! ## The converse -/

/-- With two elements in each `K i`, a family of maps `t i` is bijective when
precomposition with it is a bijection between families of functions into `K`. -/
theorem bijective_of_bijective_precomp {ι : Type*} {A B K : ι → Type*} [∀ i, Nontrivial (K i)]
    (t : ∀ i, A i → B i)
    (h : Function.Bijective fun (φ : ∀ i, B i → K i) i a => φ i (t i a)) (i : ι) :
    Function.Bijective (t i) := by
  classical
  let base : ∀ i, K i := fun i => Classical.arbitrary (K i)
  constructor
  · intro a₁ a₂ he
    by_contra hne
    obtain ⟨k₁, k₂, hk⟩ := exists_pair_ne (K i)
    obtain ⟨φ, hφ⟩ :=
      h.2 (Function.update (fun i _ => base i) i fun a => if a = a₁ then k₁ else k₂)
    have h₁ := congrFun (congrFun hφ i) a₁
    have h₂ := congrFun (congrFun hφ i) a₂
    simp only [Function.update_self, if_neg (Ne.symm hne)] at h₁ h₂
    rw [he] at h₁
    exact hk (h₁.symm.trans h₂)
  · intro b
    by_contra hb
    push_neg at hb
    obtain ⟨k, hk⟩ := exists_ne (base i)
    have heq := @h.1 (fun i _ => base i)
      (Function.update (fun i _ => base i) i fun b' => if b' = b then k else base i) (by
        funext i' a
        by_cases hi : i' = i
        · subst hi
          simp [Function.update_self, hb a]
        · simp [Function.update_of_ne hi])
    have := congrFun (congrFun heq i) b
    simp only [Function.update_self] at this
    exact hk this.symm

/-- A left adjoint of `Δ_T` on attributed states makes `T` bijective on paths into
value types, when every `K v` has two elements: `Δ_T` preserves the terminal state,
and restriction of profiles along `T` is bijective. -/
theorem attrBijective_of_isRightAdjoint [∀ v, Nontrivial (K v)]
    [(restrictStateFunctor (K := K) hS' hT).IsRightAdjoint] : AttrBijective hS' hT := by
  intro a v
  let R := restrictStateFunctor (K := K) hS' hT
  have hR : IsTerminal (R.obj (State.terminal S' K)) :=
    (State.terminalIsTerminal S' K).isTerminalObj R _
  let e := hR.uniqueUpToIso (State.terminalIsTerminal S K)
  have hbij : Function.Bijective (e.hom.α.app a) :=
    Function.bijective_iff_has_inverse.mpr ⟨e.inv.α.app a,
      fun x => congrArg (fun m : R.obj (State.terminal S' K) ⟶ _ => m.α.app a x) e.hom_inv_id,
      fun x => congrArg (fun m : State.terminal S K ⟶ _ => m.α.app a x) e.inv_hom_id⟩
  have he : e.hom = State.toTerminal _ := (State.terminalIsTerminal S K).hom_ext _ _
  have hfun : (State.toTerminal (R.obj (State.terminal S' K))).α.app a =
      fun (φ : S'.Profile K ((functor hS' hT).obj a)) v g => φ v ((functor hS' hT).map g) := by
    funext φ v g
    change φ v ((functor hS' hT).map g ≫ 𝟙 _) = φ v ((functor hS' hT).map g)
    rw [Category.comp_id]
  rw [he, hfun] at hbij
  exact bijective_of_bijective_precomp (K := K) (A := fun v => a ⟶ S.valueObj v)
    (B := fun v => (functor hS' hT).obj a ⟶ S'.valueObj v) (fun v g => (functor hS' hT).map g)
    hbij v

/-- `Δ_T` on attributed states has a left adjoint exactly when `T` is bijective on
paths into value types, when every `K v` has two elements. -/
theorem isRightAdjoint_restrictStateFunctor_iff [∀ v, Nontrivial (K v)] :
    (restrictStateFunctor (K := K) hS' hT).IsRightAdjoint ↔ AttrBijective hS' hT :=
  ⟨fun _ => attrBijective_of_isRightAdjoint (hS' := hS') (hT := hT) (K := K),
    fun hb => ⟨_, ⟨sigmaStateAdjunction hb⟩⟩⟩

end Translation

end DDD
