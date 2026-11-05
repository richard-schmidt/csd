import DDD.VData
import DDD.LitInterp
import DDD.Json

/-!
# Finite states of literals through conversions

The finite states of the exchange format have literals as values (`FinState LitK`).
When every literal fits its value type (`FinState.LitsFit`), the state is a finite
state with values in the literal interpretation (`FinState.fit`), with the same
check (`check_fit`).

- `FinState.mapVals`: a finite state with its values mapped; `litVal` maps a
  state of the literal interpretation back to literals (`mapVals_fit`,
  `fit_mapVals`).
- `FinState.evalLit` follows generators through the columns and conversions with
  `TypeList.convLit`, as the Julia side does; it is `FinState.evalV` in the literal
  interpretation (`evalV_mapVals`).
- `FinState.vrestrictLit T S S' X`: `Δ_T X` along a translation valid with
  conversions, computed on literals. It is the restriction of the fitted state
  (`mapVals_vrestrict`), so its state in the literal interpretation is isomorphic
  to `Translation.vrestrictState` applied to the state of `X`
  (`vrestrictLit_iso`). `FinState.IsVRestriction` states it, and
  `isVRestriction_vrestrictLit` proves it.
-/

namespace DDD

open CategoryTheory Schema

/-- An element with its value mapped by `f`. -/
def Elem.map {K K' : ValueType → Type} (f : ∀ v, K v → K' v) : Elem K → Elem K'
  | .ent e i => .ent e i
  | .val v k => .val v (f v k)

theorem Elem.map_injective {K K' : ValueType → Type} {f : ∀ v, K v → K' v}
    (hf : ∀ v, Function.Injective (f v)) : Function.Injective (Elem.map f) := by
  rintro (⟨e, i⟩ | ⟨v, k⟩) (⟨e', i'⟩ | ⟨v', k'⟩) h <;> simp only [Elem.map] at h
  · injection h with h₁ h₂
    subst h₁ h₂
    rfl
  · cases h
  · cases h
  · injection h with h₁ h₂
    subst h₁
    rw [hf v (eq_of_heq h₂)]

theorem List.lookup_map_snd {α β γ : Type} [BEq α] (g : β → γ) :
    ∀ (l : List (α × β)) (a : α), (l.map fun c => (c.1, g c.2)).lookup a = (l.lookup a).map g
  | [], _ => rfl
  | (b, y) :: l, a => by
    simp only [List.map_cons, List.lookup]
    cases a == b
    · exact List.lookup_map_snd g l a
    · rfl

namespace FinState

variable {K K' : ValueType → Type} (f : ∀ v, K v → K' v)

/-- `X` with each value mapped by `f`. -/
def mapVals (X : FinState K) : FinState K' where
  sizes := X.sizes
  refs := X.refs
  attrs := X.attrs.map fun c => (c.1, c.2.map fun x => ⟨x.1, f x.1 x.2⟩)

variable {f} {X : FinState K}

theorem size_mapVals (e : String) : (X.mapVals f).size e = X.size e := rfl

theorem refCol_mapVals (e n : String) : (X.mapVals f).refCol e n = X.refCol e n := rfl

theorem attrCol_mapVals (e n : String) :
    (X.mapVals f).attrCol e n =
      (X.attrCol e n).map (List.map fun x => (⟨x.1, f x.1 x.2⟩ : Σ v, K' v)) :=
  List.lookup_map_snd _ X.attrs (e, n)

theorem has_mapVals {x : Elem K} {o : Ob} : (X.mapVals f).Has (x.map f) o ↔ X.Has x o := by
  cases x <;> cases o <;> exact Iff.rfl

theorem step_mapVals (S : Schema) (x : Elem K) (n : String) :
    (X.mapVals f).step S (x.map f) n = (X.step S x n).map (Elem.map f) := by
  cases x with
  | val => rfl
  | ent e i =>
    simp only [Elem.map, step]
    cases S.ref? e n with
    | some r =>
      simp only [refCol_mapVals]
      cases (X.refCol e n).bind (·[i]?) <;> rfl
    | none =>
      cases S.attr? e n with
      | none => rfl
      | some a =>
        simp only [attrCol_mapVals]
        cases X.attrCol e n with
        | none => rfl
        | some c =>
          simp only [Option.map_some, Option.bind_some, List.getElem?_map]
          cases c[i]? <;> rfl

theorem eval_mapVals (S : Schema) : ∀ (x : Elem K) (l : List String),
    (X.mapVals f).eval S (x.map f) l = (X.eval S x l).map (Elem.map f)
  | x, [] => rfl
  | x, n :: ns => by
    simp only [eval, step_mapVals]
    cases X.step S x n with
    | none => rfl
    | some y => exact eval_mapVals S y ns

/-- An injective map of values keeps the check. -/
theorem check_mapVals [∀ v, DecidableEq (K v)] [∀ v, DecidableEq (K' v)]
    (hf : ∀ v, Function.Injective (f v)) (S : Schema) :
    (X.mapVals f).check S = X.check S := by
  have hq : ∀ (q : Equation) (i : Nat),
      decide ((X.mapVals f).eval S (.ent q.src i) q.lhs =
          (X.mapVals f).eval S (.ent q.src i) q.rhs) =
        decide (X.eval S (.ent q.src i) q.lhs = X.eval S (.ent q.src i) q.rhs) := by
    intro q i
    have e₁ := eval_mapVals (X := X) (f := f) S (.ent q.src i) q.lhs
    have e₂ := eval_mapVals (X := X) (f := f) S (.ent q.src i) q.rhs
    simp only [Elem.map] at e₁ e₂
    rw [e₁, e₂]
    exact decide_eq_decide.mpr (Option.map_injective (Elem.map_injective hf)).eq_iff
  simp only [check, size_mapVals, refCol_mapVals]
  congr 1
  · congr 1
    congr 1
    funext a
    rw [attrCol_mapVals]
    cases X.attrCol a.src a.name with
    | none => rfl
    | some c => simp [Function.comp_def]
  · congr 1
    funext q
    congr 1
    funext i
    exact hq q i

/-! ## Literals that fit -/

variable {L : TypeList}

/-- Every literal of `X` fits its value type. -/
def LitsFit (L : TypeList) (X : FinState LitK) : Prop :=
  ∀ c ∈ X.attrs, ∀ x ∈ c.2, L.Fits x.1 x.2

/-- Literals in normal form fit. -/
theorem litsFit_of_check (hL : L.Sound) {X : FinState LitK} (h : X.litsFit L = true) :
    X.LitsFit L := by
  intro c hc x hx
  simp only [litsFit, List.all_eq_true] at h
  have h' := h c hc x hx
  split at h'
  · rename_i l hl
    obtain rfl : l = x.2 := by simpa using h'
    exact TypeList.fits_of_normalize hL hl
  · exact absurd h' (by simp)

instance (hL : L.Sound) (v : ValueType) : DecidableEq ((L.litInterp hL).K v) :=
  inferInstanceAs (DecidableEq { x : Lit // L.Fits v x })

/-- The literal of a value of the literal interpretation. -/
def litVal (hL : L.Sound) (v : ValueType) (x : (L.litInterp hL).K v) : Lit :=
  (x : { y : Lit // L.Fits v y }).1

theorem litVal_injective (hL : L.Sound) (v : ValueType) : Function.Injective (litVal hL v) :=
  Subtype.val_injective

/-- A column whose literals fit, with values in the literal interpretation. -/
def fitCol (hL : L.Sound) (col : List (Σ v, LitK v)) (h : ∀ x ∈ col, L.Fits x.1 x.2) :
    List (Σ v, (L.litInterp hL).K v) :=
  col.pmap (fun (x : Σ v, LitK v) (hx : L.Fits x.1 x.2) =>
    Sigma.mk (β := fun v => (L.litInterp hL).K v) x.1
    (show (L.litInterp hL).K x.1 from (⟨x.2, hx⟩ : { y : Lit // L.Fits x.1 y }))) h

theorem map_fitCol (hL : L.Sound) :
    ∀ (col : List (Σ v, LitK v)) (h : ∀ x ∈ col, L.Fits x.1 x.2),
    (fitCol hL col h).map (fun x => (⟨x.1, litVal hL x.1 x.2⟩ : Σ v, LitK v)) = col
  | [], _ => rfl
  | x :: xs, h => by
    change _ :: _ = x :: xs
    congr 1
    exact map_fitCol hL xs _

theorem fitCol_map (hL : L.Sound) : ∀ (col : List (Σ v, (L.litInterp hL).K v))
    (h : ∀ x ∈ col.map (fun x => (⟨x.1, litVal hL x.1 x.2⟩ : Σ v, LitK v)),
      L.Fits x.1 x.2),
    fitCol hL (col.map fun x => (⟨x.1, litVal hL x.1 x.2⟩ : Σ v, LitK v)) h = col
  | [], _ => rfl
  | x :: xs, h => by
    change _ :: _ = x :: xs
    congr 1
    exact fitCol_map hL xs _

/-- A finite state whose literals fit, with values in the literal interpretation. -/
def fit (hL : L.Sound) (X : FinState LitK) (h : X.LitsFit L) : FinState (L.litInterp hL).K where
  sizes := X.sizes
  refs := X.refs
  attrs := X.attrs.pmap (fun c hc => (c.1, fitCol hL c.2 hc)) h

theorem mapVals_fit (hL : L.Sound) (X : FinState LitK) (h : X.LitsFit L) :
    (X.fit hL h).mapVals (litVal hL) = X := by
  obtain ⟨sizes, refs, attrs⟩ := X
  simp only [fit, mapVals, FinState.mk.injEq, true_and]
  induction attrs with
  | nil => rfl
  | cons c l ih =>
    change _ :: _ = c :: l
    congr 1
    · exact Prod.ext rfl (map_fitCol hL c.2 _)
    · exact ih fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem litsFit_mapVals (hL : L.Sound) (Y : FinState (L.litInterp hL).K) :
    (Y.mapVals (litVal hL)).LitsFit L := by
  intro c hc x hx
  simp only [mapVals, List.mem_map] at hc
  obtain ⟨c', -, rfl⟩ := hc
  simp only [List.mem_map] at hx
  obtain ⟨x', -, rfl⟩ := hx
  exact x'.2.2

theorem fit_mapVals (hL : L.Sound) (Y : FinState (L.litInterp hL).K)
    (h : (Y.mapVals (litVal hL)).LitsFit L) :
    (Y.mapVals (litVal hL)).fit hL h = Y := by
  obtain ⟨sizes, refs, attrs⟩ := Y
  simp only [fit, mapVals, FinState.mk.injEq, true_and]
  induction attrs with
  | nil => rfl
  | cons c l ih =>
    change _ :: _ = c :: l
    congr 1
    · exact Prod.ext rfl (fitCol_map hL c.2 _)
    · exact ih fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem check_fit (hL : L.Sound) (X : FinState LitK)
    (h : X.LitsFit L) (S : Schema) : (X.fit hL h).check S = X.check S := by
  conv_rhs => rw [← mapVals_fit hL X h]
  exact (check_mapVals (litVal_injective hL) S).symm

/-! ## Following conversions on literals -/

section Lit

variable (L) (S : Schema) (X : FinState LitK)

/-- One step along a generator, through the columns, or along a conversion, with
`TypeList.convLit`. -/
def stepLit : Elem LitK → String → Option (Elem LitK)
  | .ent e i, n => X.step S (.ent e i) n
  | .val v x, n => match L.conv? v n, L.convLit v n x with
    | some w, .ok y => some (.val w y)
    | _, _ => none

/-- Following a list of names of generators and conversions on literals. -/
def evalLit : Elem LitK → List String → Option (Elem LitK)
  | x, [] => some x
  | x, n :: ns => (X.stepLit L S x n).bind fun y => evalLit y ns

variable {L S}

/-- On a state of the literal interpretation, following conversions on literals is
following them in the interpretation. -/
theorem evalV_mapVals (hL : L.Sound) (Y : FinState (L.litInterp hL).K) :
    ∀ (x : Elem (L.litInterp hL).K) (l : List String),
      (Y.evalV (L.litInterp hL) S x l).map (Elem.map (litVal hL)) =
        (Y.mapVals (litVal hL)).evalLit L S (x.map (litVal hL)) l
  | x, [] => rfl
  | x, n :: ns => by
    have hs : (Y.vstep (L.litInterp hL) S x n).map (Elem.map (litVal hL)) =
        (Y.mapVals (litVal hL)).stepLit L S (x.map (litVal hL)) n := by
      cases x with
      | ent e i => exact (step_mapVals S (.ent e i) n).symm
      | val v k =>
        cases hc : L.conv? v n with
        | none =>
          rw [vstep_val_none (L.litInterp hL) Y hc]
          simp [Elem.map, stepLit, hc]
        | some w =>
          rw [vstep_val (L.litInterp hL) Y hc]
          have hcl : L.convLit v n (litVal hL v k) =
              .ok (litVal hL w ((L.litInterp hL).F.map (L.convMor n hc) k)) :=
            TypeList.convLit_litInterp hL hc k
          simp only [Elem.map, stepLit, hc, hcl, Option.map_some]
    simp only [evalV, evalLit, ← hs]
    cases Y.vstep (L.litInterp hL) S x n with
    | none => rfl
    | some y => exact evalV_mapVals hL Y y ns

end Lit

/-! ## Restriction on literals -/

section RestrictLit

variable (L) (T : Translation) (S S' : Schema) (X : FinState LitK)

/-- The column of the attribute named `n` out of `e` in `Δ_T X`, on literals. -/
def vattrColumnLit (e n : String) : List (Σ v, LitK v) :=
  (List.range (X.size (T.ent e))).filterMap fun i =>
    match X.evalLit L S' (.ent (T.ent e) i) (T.gen (.entity e) n) with
    | some (.val v k) => some ⟨v, k⟩
    | _ => none

/-- Restriction `Δ_T X` along a translation valid with conversions, computed on
literals. -/
def vrestrictLit : FinState LitK where
  sizes := S.entities.map fun e => (e, X.size (T.ent e))
  refs := S.refs.map fun r => ((r.src, r.name), X.refColumn T S' r.src r.name)
  attrs := S.attrs.map fun a => ((a.src, a.name), X.vattrColumnLit L T S' a.src a.name)

variable {L T S S' X}

/-- Restriction on literals is restriction in the literal interpretation. -/
theorem mapVals_vrestrict (hL : L.Sound) (Y : FinState (L.litInterp hL).K) :
    (Y.vrestrict (L.litInterp hL) T S S').mapVals (litVal hL) =
      (Y.mapVals (litVal hL)).vrestrictLit L T S S' := by
  have hr : ∀ e n, (Y.mapVals (litVal hL)).refColumn T S' e n = Y.refColumn T S' e n := by
    intro e n
    simp only [refColumn, size_mapVals]
    congr 1
    funext i
    have := eval_mapVals (X := Y) (f := litVal hL) S' (.ent (T.ent e) i)
      (T.gen (.entity e) n)
    simp only [Elem.map] at this
    rw [this]
    cases Y.eval S' (.ent (T.ent e) i) (T.gen (.entity e) n) with
    | none => rfl
    | some z => cases z <;> rfl
  have ha : ∀ e n, (Y.vattrColumn (L.litInterp hL) T S' e n).map
      (fun x => (⟨x.1, litVal hL x.1 x.2⟩ : Σ v, LitK v)) =
        (Y.mapVals (litVal hL)).vattrColumnLit L T S' e n := by
    intro e n
    simp only [vattrColumn, vattrColumnLit, size_mapVals, List.map_filterMap]
    congr 1
    funext i
    have := evalV_mapVals hL Y (S := S') (.ent (T.ent e) i) (T.gen (.entity e) n)
    simp only [Elem.map] at this
    rw [← this]
    cases Y.evalV (L.litInterp hL) S' (.ent (T.ent e) i) (T.gen (.entity e) n) with
    | none => rfl
    | some z => cases z <;> rfl
  change FinState.mk _ _ _ = FinState.mk _ _ _
  congr 1
  · exact List.map_congr_left fun r _ => by rw [hr]
  · simp only [vrestrict, List.map_map]
    exact List.map_congr_left fun a _ => by simp only [Function.comp_apply, ha]

/-- Two equal finite states that pass the check have isomorphic states. -/
def toStateIsoOfEq [∀ v, DecidableEq (K v)] {S : Schema} {A B : FinState K} (h : A = B)
    (hA : A.check S = true) (hB : B.check S = true) : A.toState hA ≅ B.toState hB := by
  subst h
  exact Iso.refl _

/-- `Δ_T X` on literals: when the literals of `X` fit, those of the result fit, and
its state in the literal interpretation is isomorphic to `Δ_T` applied to the
state with conversions of `X`. -/
theorem vrestrictLit_iso (hL : L.Sound) (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.VValid L S S') (hfit : X.LitsFit L) (hX : (X.fit hL hfit).check S' = true) :
    ∃ (hY : (X.vrestrictLit L T S S').LitsFit L)
      (hY' : ((X.vrestrictLit L T S S').fit hL hY).check S = true),
      Nonempty (((X.vrestrictLit L T S S').fit hL hY).toState hY' ≅
        (T.vrestrictState hS hS' hT
          (((X.fit hL hfit).toState hX).vext (L.litInterp hL) hS')).toState) := by
  have e : X.vrestrictLit L T S S' =
      ((X.fit hL hfit).vrestrict (L.litInterp hL) T S S').mapVals (litVal hL) := by
    rw [mapVals_vrestrict, mapVals_fit]
  have hY : (X.vrestrictLit L T S S').LitsFit L := e ▸ litsFit_mapVals hL _
  have e' : (X.vrestrictLit L T S S').fit hL hY =
      (X.fit hL hfit).vrestrict (L.litInterp hL) T S S' := by
    have := fit_mapVals hL ((X.fit hL hfit).vrestrict (L.litInterp hL) T S S') (e ▸ hY)
    rw [← this]
    congr 1
  have hc := FinState.vrestrict_check (I := L.litInterp hL) hS hS' hX hT
  have hY' : ((X.vrestrictLit L T S S').fit hL hY).check S = true := e' ▸ hc
  exact ⟨hY, hY', ⟨toStateIsoOfEq e' hY' hc ≪≫ FinState.vrestrictIso hS hS' hX hT⟩⟩

variable (L T S S') in
/-- `Y` is the restriction of `X` along `T`, valid with the conversions of `L`: the
literals of both fit their types, both pass the check, and the state of `Y` in the
literal interpretation is isomorphic to `Δ_T` applied to the state with conversions
of `X`. -/
def IsVRestriction (X Y : FinState LitK) : Prop :=
  ∃ (hL : L.Sound) (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.VValid L S S')
    (hfit : X.LitsFit L) (hX : (X.fit hL hfit).check S' = true) (hY : Y.LitsFit L)
    (hY' : (Y.fit hL hY).check S = true),
    Nonempty ((Y.fit hL hY).toState hY' ≅
      (T.vrestrictState hS hS' hT
        (((X.fit hL hfit).toState hX).vext (L.litInterp hL) hS')).toState)

/-- `vrestrictLit` computes the restriction along a translation valid with
conversions. -/
theorem isVRestriction_vrestrictLit (hL : L.Sound) (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.VValid L S S') (hfit : X.LitsFit L) (hX : X.check S' = true) :
    IsVRestriction L T S S' X (X.vrestrictLit L T S S') := by
  have hX' : (X.fit hL hfit).check S' = true := (check_fit hL X hfit S').trans hX
  obtain ⟨hY, hY', e⟩ := vrestrictLit_iso hL hS hS' hT hfit hX'
  exact ⟨hL, hS, hS', hT, hfit, hX', hY, hY', e⟩

end RestrictLit

end FinState

end DDD
