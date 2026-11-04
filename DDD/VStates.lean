import DDD.ValueCat
import DDD.StateSigma

/-!
# States over the category of value types

An interpretation of the value types of a list `L` is a functor out of the
category of value types (`Interp`): it gives each value type `v` a set `I.K v`
and each conversion a function between these sets, and it satisfies the
equations of `TypeList.Basic`, which hold in `L.cat`. The general theorems hold
for every interpretation.

A state of `S` with conversions (`Schema.VState I S`) is a functor out of
`S.vcat L` with an isomorphism between its restriction to the value types and
`I`: the states that agree with `I` on the value types.

- `VState.toState`: the restriction along `S.cat ⥤ S.vcat L`, an attributed state
  of `S` with values in `I.K`.
- `State.vext`: an attributed state of `S` extends to a state with conversions,
  each conversion acting through `I` and the bijections of the state; its
  restriction is the state (`toState_vext`).
- `VState.equivalence`: in a well-formed schema, restriction is an equivalence
  between the states with conversions and the attributed states, and a bijection
  on objects (`VState.equivState`). The results on attributed states hold for
  states with conversions through it: limits and colimits (`VState.hasLimits`,
  `VState.hasColimits`), `Δ_T` and `Σ_T` (`Translation.vrestrictStateFunctor`,
  `Translation.vsigmaStateAdjunction`, `Translation.isRightAdjoint_vrestrict_iff`),
  and data gluing (`Gluing.vstateEquiv`). Restriction to `S.cat` commutes with
  `Δ_T` (`Translation.toStateIso`).
-/

namespace DDD

open CategoryTheory Limits

/-- An interpretation of the value types of `L`: a functor out of the category of
value types. It satisfies the equations between conversions, which hold in
`L.cat`. -/
structure Interp (L : TypeList) where
  F : L.cat ⥤ Type

namespace TypeList

/-- The object of the value type `v` in the category of value types. -/
def vobjOf (L : TypeList) (v : ValueType) : L.cat := emptySchema.vobj L ⟨.value v, trivial⟩

/-- The conversion named `n` from `v` to `w`, as a morphism of the category of
value types. -/
def convMor (L : TypeList) {v w : ValueType} (n : String) (h : L.conv? v n = some w) :
    L.vobjOf v ⟶ L.vobjOf w :=
  Schema.vmor (Quiver.Hom.toPath (show @Quiver.Hom (emptySchema.VObj L) _
    ⟨.value v, trivial⟩ ⟨.value w, trivial⟩ from ⟨n, by simp [Schema.vstep?, h]⟩))

end TypeList

namespace Interp

variable {L : TypeList} (I : Interp L)

/-- The values of the value type `v`. -/
def K (v : ValueType) : Type := I.F.obj (L.vobjOf v)

end Interp

/-- The schema without entity types is well formed. -/
theorem emptySchema_wellFormed : emptySchema.WellFormed := by decide

namespace Schema

variable {L : TypeList} (I : Interp L) (S : Schema)

/-- A state of `S` that agrees with `I` on the value types: a functor out of the
category of `S` with conversions, with an isomorphism between its restriction to
the value types and `I`. -/
structure VState where
  F : S.vcat L ⥤ Type
  values : S.vvals L ⋙ F ≅ I.F

variable {I S}

/-- A morphism of states with conversions: a natural transformation that commutes
with the isomorphisms, so it is the identity on values. -/
@[ext]
structure VState.Hom (X Y : S.VState I) where
  α : X.F ⟶ Y.F
  values : Functor.whiskerLeft (S.vvals L) α ≫ Y.values.hom = X.values.hom

instance : Category (S.VState I) where
  Hom := VState.Hom
  id X := ⟨𝟙 X.F, by simp⟩
  comp f g := ⟨f.α ≫ g.α, by rw [Functor.whiskerLeft_comp, Category.assoc, g.values, f.values]⟩
  id_comp f := VState.Hom.ext (Category.id_comp f.α)
  comp_id f := VState.Hom.ext (Category.comp_id f.α)
  assoc f g h := VState.Hom.ext (Category.assoc f.α g.α h.α)

@[simp] theorem VState.id_α (X : S.VState I) : (𝟙 X : X ⟶ X).α = 𝟙 X.F := rfl

@[simp] theorem VState.comp_α {X Y Z : S.VState I} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).α = f.α ≫ g.α := rfl

/-! ## Restriction to `S.cat` -/

/-- The restriction of a state with conversions to `S.cat`: an attributed state with
values in `I.K`. -/
def VState.toState (X : S.VState I) : S.State I.K where
  F := S.vinc L ⋙ X.F
  values v := (X.values.app (L.vobjOf v)).toEquiv

variable (I S) in
/-- Restriction to `S.cat`, as a functor. -/
def VState.toStateFunctor : S.VState I ⥤ S.State I.K where
  obj := VState.toState
  map {X Y} f := ⟨Functor.whiskerLeft (S.vinc L) f.α, fun v x => by
    have h := congrArg (fun φ => φ.app (L.vobjOf v) x) f.values
    simpa using h⟩

/-! ## Extension to conversions -/

theorem conv?_of_vstep? {v w : ValueType} {n : String}
    (h : S.vstep? L (.value v) n = some (.value w)) : L.conv? v n = some w := by
  simp only [vstep?, Option.map_eq_some_iff, Ob.value.injEq] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact hu

theorem not_vstep?_value_entity {v : ValueType} {e n : String} :
    S.vstep? L (.value v) n ≠ some (.entity e) := by
  simp [vstep?]

/-- Out of a value type, the targets of the conversions are the same in every
schema. -/
theorem vtgt?_value_eq {S S' : Schema} {v : ValueType} :
    ∀ l : List String, S.vtgt? L (.value v) l = S'.vtgt? L (.value v) l
  | [] => rfl
  | n :: ns => by
    simp only [vtgt?_cons, vstep?]
    cases L.conv? v n with
    | none => rfl
    | some w => exact vtgt?_value_eq ns

/-- A path of conversions ends at a value type. -/
theorem vtgt?_value {v : ValueType} : ∀ {l : List String} {o : Ob},
    S.vtgt? L (.value v) l = some o → ∃ w, o = .value w
  | [], _, h => ⟨v, (Option.some.inj h).symm⟩
  | n :: ns, o, h => by
    simp only [vtgt?_cons, vstep?] at h
    cases hc : L.conv? v n with
    | none => simp [hc] at h
    | some w =>
      simp only [hc, Option.map_some, Option.bind_some] at h
      exact vtgt?_value h

variable (I) in
/-- The bijection of `X` at an object of the category of value types. -/
def valEquiv (X : S.State I.K) : ∀ (o : Ob) (ho : emptySchema.IsOb o),
    X.F.obj (S.obj ⟨o, isOb_of_empty ho⟩) ≃ I.F.obj (emptySchema.vobj L ⟨o, ho⟩)
  | .entity _, ho => absurd ho (by simp [IsOb, emptySchema])
  | .value v, _ => X.values v

/-- `I`, carried onto the sets of `X` at the value types by its bijections. -/
def conj (X : S.State I.K) : L.cat ⥤ Type where
  obj c := X.F.obj (S.obj ⟨c.as.1, isOb_of_empty c.as.2⟩)
  map {c d} g x := (valEquiv I X d.as.1 d.as.2).symm (I.F.map g (valEquiv I X c.as.1 c.as.2 x))
  map_id c := by
    funext x
    simp only [CategoryTheory.Functor.map_id, types_id_apply, Equiv.symm_apply_apply]
  map_comp f g := by
    funext x
    simp only [CategoryTheory.Functor.map_comp, types_comp_apply, Equiv.apply_symm_apply]

/-- The step of `X` along a generator or a conversion. -/
def vextStep (X : S.State I.K) : ∀ (a b : S.VObj L), (a ⟶ b) → X.F.obj (S.obj a) → X.F.obj (S.obj b)
  | ⟨.entity e, ha⟩, b, f => X.F.map (S.genMor (a := ⟨.entity e, ha⟩) (b := b) f.1 f.2)
  | ⟨.value v, _⟩, ⟨.value w, _⟩, f => fun x =>
    (X.values w).symm (I.F.map (L.convMor f.1 (conv?_of_vstep? f.2)) (X.values v x))
  | ⟨.value _, _⟩, ⟨.entity _, _⟩, f => absurd f.2 not_vstep?_value_entity

/-- The steps of `X` along generators and conversions. -/
def vextPre (X : S.State I.K) : S.VObj L ⥤q Type where
  obj a := X.F.obj (S.obj a)
  map {a b} f := vextStep X a b f

/-- On paths of `S`, the extension is `X`. -/
theorem vincPre_vextPre (X : S.State I.K) :
    Paths.lift (S.vincPre L) ⋙ Paths.lift (vextPre X) =
      CategoryTheory.Quotient.functor S.rel ⋙ X.F := by
  refine Paths.ext_functor rfl fun a b e => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map,
    Paths.lift_toPath]
  obtain ⟨⟨ea⟩ | ⟨v⟩, ha⟩ := a
  · rfl
  · exact absurd e.2 (by simp [step?])

/-- On paths of conversions, the extension is `I`, carried onto `X`. -/
theorem vvalsPre_vextPre (X : S.State I.K) :
    Paths.lift (S.vvalsPre L) ⋙ Paths.lift (vextPre X) =
      CategoryTheory.Quotient.functor (emptySchema.vrel L) ⋙ conj X := by
  refine Paths.ext_functor rfl fun a b e => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map,
    Paths.lift_toPath]
  obtain ⟨⟨ea⟩ | ⟨v⟩, ha⟩ := a
  · exact absurd ha (by simp [IsOb, emptySchema])
  obtain ⟨⟨eb⟩ | ⟨w⟩, hb⟩ := b
  · exact absurd hb (by simp [IsOb, emptySchema])
  rfl

/-- The extension of `X` respects the equations of `S` and the equations between
conversions. -/
theorem vext_resp (hS : S.WellFormed) (X : S.State I.K) :
    ∀ (a b : Paths (S.VObj L)) (f₁ f₂ : a ⟶ b), S.vrel L f₁ f₂ →
      (Paths.lift (vextPre X)).map f₁ = (Paths.lift (vextPre X)).map f₂ := by
  rintro ⟨ao, hao⟩ ⟨bo, hbo⟩ f₁ f₂ (⟨q, hq, ha, h₁, h₂⟩ | ⟨v, ha, h⟩)
  · simp only at ha
    subst ha
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
    have t₁ := vtgt?_vnames f₁
    simp only at t₁
    rw [h₁, vtgt?_of_tgt? hl] at t₁
    obtain rfl : o = bo := Option.some.inj t₁
    obtain ⟨⟨b₁, hb₁'⟩, p₁, hb₁, hp₁⟩ := exists_path hS ⟨.entity q.src, hao⟩ q.lhs hl
    obtain ⟨⟨b₂, hb₂'⟩, p₂, hb₂, hp₂⟩ := exists_path hS ⟨.entity q.src, hao⟩ q.rhs hr
    simp only at hb₁ hb₂
    subst hb₁ hb₂
    have e₁ : f₁ = (Paths.lift (S.vincPre L)).map p₁ :=
      vnames_injective _ _ (by rw [vnames_vincPath, hp₁, h₁])
    have e₂ : f₂ = (Paths.lift (S.vincPre L)).map p₂ :=
      vnames_injective _ _ (by rw [vnames_vincPath, hp₂, h₂])
    rw [e₁, e₂]
    have k₁ := Functor.congr_hom (vincPre_vextPre X) p₁
    have k₂ := Functor.congr_hom (vincPre_vextPre X) p₂
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map] at k₁ k₂
    rw [k₁, k₂]
    exact congrArg X.F.map (CategoryTheory.Quotient.sound _ ⟨q, hq, rfl, hp₁, hp₂⟩)
  · simp only at ha
    subst ha
    obtain ⟨w, rfl⟩ := vtgt?_value (vtgt?_vnames f₁)
    have t₁ : emptySchema.vtgt? L (.value v) (vnames f₁) = some (.value w) :=
      (vtgt?_value_eq _).trans (vtgt?_vnames f₁)
    have t₂ : emptySchema.vtgt? L (.value v) (vnames f₂) = some (.value w) :=
      (vtgt?_value_eq _).trans (vtgt?_vnames f₂)
    let g₁ := emptySchema.vpathOf emptySchema_wellFormed ⟨.value v, trivial⟩ ⟨.value w, trivial⟩
      (vnames f₁) t₁
    let g₂ := emptySchema.vpathOf emptySchema_wellFormed ⟨.value v, trivial⟩ ⟨.value w, trivial⟩
      (vnames f₂) t₂
    have e₁ : f₁ = (Paths.lift (S.vvalsPre L)).map g₁ :=
      vnames_injective _ _ (by rw [vnames_vvalsPath, vnames_vpathOf])
    have e₂ : f₂ = (Paths.lift (S.vvalsPre L)).map g₂ :=
      vnames_injective _ _ (by rw [vnames_vvalsPath, vnames_vpathOf])
    rw [e₁, e₂]
    have k₁ := Functor.congr_hom (vvalsPre_vextPre X) g₁
    have k₂ := Functor.congr_hom (vvalsPre_vextPre X) g₂
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map] at k₁ k₂
    rw [k₁, k₂]
    exact congrArg (conj X).map (CategoryTheory.Quotient.sound _
      (Or.inr ⟨v, rfl, by rw [vnames_vpathOf, vnames_vpathOf]; exact h⟩))

/-- The functor of the extension of `X`. -/
def vextF (hS : S.WellFormed) (X : S.State I.K) : S.vcat L ⥤ Type :=
  CategoryTheory.Quotient.lift (S.vrel L) (Paths.lift (vextPre X)) (vext_resp hS X)

theorem vvals_vextF (hS : S.WellFormed) (X : S.State I.K) : S.vvals L ⋙ vextF hS X = conj X := by
  apply CategoryTheory.Quotient.lift_unique'
  calc CategoryTheory.Quotient.functor (emptySchema.vrel L) ⋙ S.vvals L ⋙ vextF hS X
      = Paths.lift (S.vvalsPre L) ⋙ CategoryTheory.Quotient.functor (S.vrel L) ⋙ vextF hS X := by
        rw [← Functor.assoc, vvals, CategoryTheory.Quotient.lift_spec, Functor.assoc]
    _ = Paths.lift (S.vvalsPre L) ⋙ Paths.lift (vextPre X) := by
        rw [vextF, CategoryTheory.Quotient.lift_spec]
    _ = _ := vvalsPre_vextPre X

theorem vinc_vextF (hS : S.WellFormed) (X : S.State I.K) : S.vinc L ⋙ vextF hS X = X.F := by
  apply CategoryTheory.Quotient.lift_unique'
  calc CategoryTheory.Quotient.functor S.rel ⋙ S.vinc L ⋙ vextF hS X
      = Paths.lift (S.vincPre L) ⋙ CategoryTheory.Quotient.functor (S.vrel L) ⋙ vextF hS X := by
        rw [← Functor.assoc, vinc, CategoryTheory.Quotient.lift_spec, Functor.assoc]
    _ = Paths.lift (S.vincPre L) ⋙ Paths.lift (vextPre X) := by
        rw [vextF, CategoryTheory.Quotient.lift_spec]
    _ = _ := vincPre_vextPre X

/-- The values of the extension of `X` are those of `I`, by the bijections of
`X`. -/
def vextValues (hS : S.WellFormed) (X : S.State I.K) : S.vvals L ⋙ vextF hS X ≅ I.F :=
  NatIso.ofComponents (fun c => (valEquiv I X c.as.1 c.as.2).toIso) fun {c d} g => by
    rw [Functor.congr_hom (vvals_vextF hS X) g]
    funext x
    simp only [conj, eqToHom_refl, Category.id_comp, Category.comp_id, types_comp_apply,
      Equiv.toIso_hom]
    exact Equiv.apply_symm_apply _ _

variable (I) in
/-- The extension of an attributed state to a state with conversions: each
conversion acts through `I` and the bijections of the state. -/
def _root_.DDD.Schema.State.vext (hS : S.WellFormed) (X : S.State I.K) : S.VState I where
  F := vextF hS X
  values := vextValues hS X

/-- The restriction of the extension of `X` is `X`. -/
theorem toState_vext (hS : S.WellFormed) (X : S.State I.K) : (X.vext I hS).toState = X :=
  State.ext' (vinc_vextF hS X) fun _ _ => rfl

/-! ## The equivalence -/

/-- A family of maps between two functors out of `S.vcat L` is natural when it
commutes with the generators and the conversions. -/
theorem natural_of_vgen {F G : S.vcat L ⥤ Type} (app : ∀ c, F.obj c ⟶ G.obj c)
    (h : ∀ (a b : S.VObj L) (e : a ⟶ b),
      F.map (vmor e.toPath) ≫ app (S.vobj L b) = app (S.vobj L a) ≫ G.map (vmor e.toPath)) :
    ∀ {c d : S.vcat L} (g : c ⟶ d), F.map g ≫ app d = app c ≫ G.map g := by
  rintro ⟨a⟩ ⟨b⟩ g
  obtain ⟨p, rfl⟩ := vmor_surjective (a := a) (b := b) g
  induction p with
  | nil => erw [vmor_nil, F.map_id, G.map_id, Category.id_comp]
  | cons p e ih =>
    erw [vmor_cons, F.map_comp, G.map_comp, Category.assoc, h, ← Category.assoc, ih,
      Category.assoc]

instance : (VState.toStateFunctor I S).Faithful where
  map_injective {X Y} f g h := by
    apply VState.Hom.ext
    ext ⟨a⟩ x
    exact congrArg (fun φ : X.toState ⟶ Y.toState => φ.α.app (S.obj a) x) h

instance : (VState.toStateFunctor I S).Full where
  map_surjective {X Y} φ := by
    refine ⟨⟨⟨fun c => φ.α.app (S.obj c.as), fun _ _ g =>
      natural_of_vgen (F := X.F) (G := Y.F) (fun c => φ.α.app (S.obj c.as)) ?_ g⟩, ?_⟩, rfl⟩
    · rintro ⟨ao, hao⟩ b e
      cases ao with
      | entity ea => exact φ.α.naturality (S.genMor (a := ⟨.entity ea, hao⟩) (b := b) e.1 e.2)
      | value v =>
        obtain ⟨⟨eb⟩ | ⟨w⟩, hb⟩ := b
        · exact absurd e.2 not_vstep?_value_entity
        have hc := conv?_of_vstep? e.2
        have hX : X.F.map (vmor e.toPath) ≫ (X.values.app (L.vobjOf w)).hom =
            (X.values.app (L.vobjOf v)).hom ≫ I.F.map (L.convMor e.1 hc) :=
          X.values.hom.naturality (L.convMor e.1 hc)
        have hY : Y.F.map (vmor e.toPath) ≫ (Y.values.app (L.vobjOf w)).hom =
            (Y.values.app (L.vobjOf v)).hom ≫ I.F.map (L.convMor e.1 hc) :=
          Y.values.hom.naturality (L.convMor e.1 hc)
        have hφ : ∀ u (y : X.F.obj (S.vobj L ⟨.value u, trivial⟩)),
            (Y.values.app (L.vobjOf u)).hom (φ.α.app (S.obj ⟨.value u, trivial⟩) y) =
              (X.values.app (L.vobjOf u)).hom y := fun u y => φ.values u y
        funext x
        apply (Y.values.app (L.vobjOf w)).toEquiv.injective
        have hX' := congrFun hX x
        have hY' := congrFun hY (φ.α.app (S.obj ⟨.value v, trivial⟩) x)
        simp only [types_comp_apply] at hX' hY'
        change (Y.values.app (L.vobjOf w)).hom
            (φ.α.app (S.obj ⟨.value w, trivial⟩) (X.F.map (vmor e.toPath) x)) =
          (Y.values.app (L.vobjOf w)).hom
            (Y.F.map (vmor e.toPath) (φ.α.app (S.obj ⟨.value v, trivial⟩) x))
        rw [hφ, hX', hY', hφ]
    · ext ⟨⟨⟨eo⟩ | ⟨v⟩, ho⟩⟩ x
      · exact absurd ho (by simp [IsOb, emptySchema])
      · exact φ.values v x

/-- In a well-formed schema, every attributed state is the restriction of a state
with conversions. -/
theorem toStateFunctor_essSurj (hS : S.WellFormed) : (VState.toStateFunctor I S).EssSurj :=
  ⟨fun X => ⟨X.vext I hS, ⟨eqToIso (toState_vext hS X)⟩⟩⟩

theorem toStateFunctor_isEquivalence (hS : S.WellFormed) :
    (VState.toStateFunctor I S).IsEquivalence where
  essSurj := toStateFunctor_essSurj hS

variable (I) in
/-- In a well-formed schema, the states with conversions are equivalent to the
attributed states, by restriction to `S.cat`. -/
noncomputable def VState.equivalence (hS : S.WellFormed) : S.VState I ≌ S.State I.K :=
  @Functor.asEquivalence _ _ _ _ (VState.toStateFunctor I S) (toStateFunctor_isEquivalence hS)

/-- States with conversions have all small limits. -/
theorem VState.hasLimits (hS : S.WellFormed) : HasLimits (S.VState I) :=
  @Adjunction.has_limits_of_equivalence _ _ _ _ (VState.toStateFunctor I S)
    (toStateFunctor_isEquivalence hS) _

/-- States with conversions have all small colimits. -/
theorem VState.hasColimits (hS : S.WellFormed) : HasColimits (S.VState I) :=
  @Adjunction.has_colimits_of_equivalence _ _ _ _ (VState.toStateFunctor I S)
    (toStateFunctor_isEquivalence hS) _

/-! ## Objects -/

/-- Two states with conversions are equal when their functors are equal and their
isomorphisms agree along that equality. -/
theorem VState.ext' {X Y : S.VState I} (hF : X.F = Y.F)
    (hv : ∀ c (x : (S.vvals L ⋙ X.F).obj c),
      Y.values.hom.app c (cast (by rw [hF]) x) = X.values.hom.app c x) : X = Y := by
  obtain ⟨F, vX⟩ := X
  obtain ⟨G, vY⟩ := Y
  obtain rfl : F = G := hF
  congr
  ext c x
  exact (hv c x).symm

/-- The extension of the restriction of a state with conversions is the state. -/
theorem vext_toState (hS : S.WellFormed) (X : S.VState I) : X.toState.vext I hS = X := by
  have hF : vextF hS X.toState = X.F := by
    refine vext_functor (fun _ => rfl) fun a b e => ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    obtain ⟨⟨ea⟩ | ⟨v⟩, ha⟩ := a
    · rfl
    obtain ⟨⟨eb⟩ | ⟨w⟩, hb⟩ := b
    · exact absurd e.2 not_vstep?_value_entity
    have hc := conv?_of_vstep? e.2
    have hX : X.F.map (vmor e.toPath) ≫ (X.values.app (L.vobjOf w)).hom =
        (X.values.app (L.vobjOf v)).hom ≫ I.F.map (L.convMor e.1 hc) :=
      X.values.hom.naturality (L.convMor e.1 hc)
    funext x
    have hX' := congrFun hX x
    simp only [types_comp_apply] at hX'
    change (X.values.app (L.vobjOf w)).toEquiv.symm
        (I.F.map (L.convMor e.1 hc) ((X.values.app (L.vobjOf v)).toEquiv x)) =
      X.F.map (vmor e.toPath) x
    rw [Equiv.symm_apply_eq]
    exact hX'.symm
  refine VState.ext' hF fun c x => ?_
  obtain ⟨⟨⟨eo⟩ | ⟨v⟩, ho⟩⟩ := c
  · exact absurd ho (by simp [IsOb, emptySchema])
  · rfl

variable (I S) in
/-- In a well-formed schema, restriction to `S.cat` is a bijection between the
states with conversions and the attributed states. -/
def VState.equivState (hS : S.WellFormed) : S.VState I ≃ S.State I.K where
  toFun := VState.toState
  invFun X := X.vext I hS
  left_inv := vext_toState hS
  right_inv := toState_vext hS

end Schema

/-! ## Restriction along translations -/

namespace Schema

theorem State.comp_α' {K : ValueType → Type} {S : Schema} {X Y Z : S.State K} (f : X ⟶ Y)
    (g : Y ⟶ Z) : (f ≫ g).α = f.α ≫ g.α := rfl

theorem State.eqToHom_α {K : ValueType → Type} {S : Schema} {X Y : S.State K} (h : X = Y) :
    (eqToHom h).α = eqToHom (congrArg State.F h) := by
  subst h
  rfl

end Schema

namespace Translation

open Schema

variable {L : TypeList} {I : Interp L} {S S' : Schema} (T : Translation)

/-- Whiskering commutes with the equality of two functors. -/
theorem whiskerLeft_eqToHom {C D E : Type*} [Category C] [Category D] [Category E]
    {P Q : C ⥤ D} (h : P = Q) {F G : D ⥤ E} (α : F ⟶ G) :
    Functor.whiskerLeft P α ≫ eqToHom (congrArg (· ⋙ G) h) =
      eqToHom (congrArg (· ⋙ F) h) ≫ Functor.whiskerLeft Q α := by
  subst h
  simp

/-- `Δ_T` on states with conversions: precomposition with the functor of `T`, which
is the identity on the value types. -/
def vrestrictState (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    (X : S'.VState I) : S.VState I where
  F := T.vfunctor hS hS' hT ⋙ X.F
  values := eqToIso (by rw [← Functor.assoc, T.vvals_comp_vfunctor hS hS' hT]) ≪≫ X.values

/-- `Δ_T` on states with conversions, as a functor. -/
def vrestrictStateFunctor (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S'.VState I ⥤ S.VState I where
  obj := T.vrestrictState hS hS' hT
  map {X Y} f := ⟨Functor.whiskerLeft (T.vfunctor hS hS' hT) f.α, by
    ext ⟨⟨⟨eo⟩ | ⟨v⟩, ho⟩⟩ x
    · exact absurd ho (by simp [IsOb, emptySchema])
    · simpa [vrestrictState] using congrFun (congrArg (fun φ => φ.app (L.vobjOf v)) f.values) x⟩

/-- Restriction to `S.cat` commutes with `Δ_T`, on objects. -/
theorem toState_vrestrict (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    (X : S'.VState I) :
    (T.vrestrictState hS hS' hT X).toState = T.restrictState hS' hT X.toState :=
  State.ext' (congrArg (· ⋙ X.F) (T.vinc_comp_vfunctor hS hS' hT)) fun v x => by
    change X.values.hom.app (L.vobjOf v) x =
      X.values.hom.app (L.vobjOf v) ((eqToHom (by rw [← Functor.assoc,
        T.vvals_comp_vfunctor hS hS' hT]) : S.vvals L ⋙ T.vfunctor hS hS' hT ⋙ X.F ⟶
          S'.vvals L ⋙ X.F).app (L.vobjOf v) x)
    rw [eqToHom_app]
    rfl

/-- Restriction to `S.cat` commutes with `Δ_T`. -/
def toStateIso (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S') :
    T.vrestrictStateFunctor (I := I) hS hS' hT ⋙ VState.toStateFunctor I S ≅
      VState.toStateFunctor I S' ⋙ T.restrictStateFunctor hS' hT :=
  NatIso.ofComponents (fun X => eqToIso (T.toState_vrestrict hS hS' hT X)) fun {X Y} f => by
    apply State.Hom.ext
    simp only [State.comp_α', eqToIso.hom, State.eqToHom_α]
    exact whiskerLeft_eqToHom (T.vinc_comp_vfunctor hS hS' hT) f.α

/-- `Δ_T` on states with conversions has a left adjoint exactly when `T` is bijective
on paths into value types, when every `I.K v` has two elements. -/
theorem isRightAdjoint_vrestrict_iff (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.Valid S S') [∀ v, Nontrivial (I.K v)] :
    (T.vrestrictStateFunctor (I := I) hS hS' hT).IsRightAdjoint ↔ AttrBijective hS' hT := by
  haveI := toStateFunctor_isEquivalence (I := I) hS
  haveI := toStateFunctor_isEquivalence (I := I) hS'
  refine Iff.trans ?_ (isRightAdjoint_restrictStateFunctor_iff (K := I.K) (hS' := hS') (hT := hT))
  let R := T.vrestrictStateFunctor (I := I) hS hS' hT
  let E := VState.toStateFunctor I S
  let E' := VState.toStateFunctor I S'
  let D := T.restrictStateFunctor (K := I.K) hS' hT
  constructor
  · intro
    haveI : (E' ⋙ D).IsRightAdjoint := Functor.isRightAdjoint_of_iso (T.toStateIso hS hS' hT)
    haveI : E'.inv.IsRightAdjoint := E'.asEquivalence.toAdjunction.isRightAdjoint
    exact Functor.isRightAdjoint_of_iso (F := E'.inv ⋙ E' ⋙ D) ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E'.asEquivalence.counitIso D ≪≫ Functor.leftUnitor D)
  · intro
    haveI : (R ⋙ E).IsRightAdjoint := Functor.isRightAdjoint_of_iso (T.toStateIso hS hS' hT).symm
    haveI : E.inv.IsRightAdjoint := E.asEquivalence.toAdjunction.isRightAdjoint
    exact Functor.isRightAdjoint_of_iso (F := (R ⋙ E) ⋙ E.inv) (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor R)

/-- `Σ_T` on states with conversions, under `AttrBijective`: `Σ_T` on attributed
states, through the two equivalences. -/
noncomputable def vsigmaStateFunctor (hS' : S'.WellFormed) (hT : T.Valid S S')
    (hb : AttrBijective hS' hT) : S.VState I ⥤ S'.VState I :=
  VState.toStateFunctor I S ⋙ sigmaStateFunctor hb ⋙ (VState.equivalence I hS').inverse

/-- `Σ_T ⊣ Δ_T` on states with conversions, under `AttrBijective`. -/
noncomputable def vsigmaStateAdjunction (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.Valid S S') (hb : AttrBijective hS' hT) :
    T.vsigmaStateFunctor hS' hT hb ⊣ T.vrestrictStateFunctor (I := I) hS hS' hT :=
  let e := VState.equivalence I hS
  let e' := VState.equivalence I hS'
  Adjunction.ofNatIsoRight
    ((e.toAdjunction.comp (sigmaStateAdjunction hb)).comp e'.symm.toAdjunction)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (T.toStateIso hS hS' hT).symm e.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫
      Functor.rightUnitor _)

end Translation

/-! ## Data gluing -/

namespace Gluing

variable (D : Gluing) {L : TypeList} {I : Interp L}

/-- Data gluing for states with conversions: a state of the glued schema is a pair of
states of the two schemas with equal restrictions to the kernel. -/
def vstateEquiv :
    D.glued.VState I ≃ { P : D.left.VState I × D.right.VState I //
      Translation.vrestrictState {} D.wf_kernel D.wf_left D.gluable.left P.1 =
        Translation.vrestrictState {} D.wf_kernel D.wf_right D.gluable.right P.2 } :=
  (Schema.VState.equivState I D.glued D.wf_glued).trans <| D.stateEquiv.trans <|
    (Equiv.subtypeEquiv ((Schema.VState.equivState I D.left D.wf_left).prodCongr
      (Schema.VState.equivState I D.right D.wf_right)) fun P => by
        change _ ↔ Translation.restrictState D.wf_left D.gluable.left P.1.toState =
          Translation.restrictState D.wf_right D.gluable.right P.2.toState
        rw [← Translation.toState_vrestrict _ D.wf_kernel,
          ← Translation.toState_vrestrict _ D.wf_kernel]
        exact (Schema.VState.equivState I D.kernel D.wf_kernel).injective.eq_iff.symm).symm

/-- The two components of `vstateEquiv` are the restrictions to the two schemas. -/
theorem vstateEquiv_apply (X : D.glued.VState I) :
    (D.vstateEquiv X).1 = (Translation.vrestrictState {} D.wf_left D.wf_glued D.inl_valid X,
      Translation.vrestrictState {} D.wf_right D.wf_glued D.inr_valid X) := by
  refine Prod.ext ?_ ?_
  · change (Schema.VState.equivState I D.left D.wf_left).symm _ = _
    rw [Equiv.symm_apply_eq]
    exact (Translation.toState_vrestrict _ D.wf_left D.wf_glued D.inl_valid X).symm
  · change (Schema.VState.equivState I D.right D.wf_right).symm _ = _
    rw [Equiv.symm_apply_eq]
    exact (Translation.toState_vrestrict _ D.wf_right D.wf_glued D.inr_valid X).symm

end Gluing

end DDD
