import DDD.Data
import DDD.VStates

/-!
# Finite states with conversions

A finite state of `S` with values in an interpretation `I` (`FinState I.K`)
extends to a state with conversions (`Schema.State.vext`). `FinState.evalV`
follows a path of `S.vcat L`: generators through the columns of the state,
conversions through `I`. `FinState.evalV_vmor`: following the names of a path is
applying the state with conversions to the path.
-/

namespace DDD

open CategoryTheory Schema

namespace FinState

variable {L : TypeList} (I : Interp L) {S : Schema} (X : FinState I.K)

/-- One step along a generator of `S`, through the columns, or along a conversion,
through `I`. -/
def vstep (S : Schema) : Elem I.K → String → Option (Elem I.K)
  | .ent e i, n => X.step S (.ent e i) n
  | .val v k, n =>
    match h : L.conv? v n with
    | some w => some (.val w (I.F.map (L.convMor n h) k))
    | none => none

/-- Following a list of names of generators and conversions. -/
def evalV (S : Schema) : Elem I.K → List String → Option (Elem I.K)
  | x, [] => some x
  | x, n :: ns => (X.vstep I S x n).bind fun y => evalV S y ns

theorem evalV_append (x : Elem I.K) (l m : List String) :
    X.evalV I S x (l ++ m) = (X.evalV I S x l).bind fun y => X.evalV I S y m := by
  induction l generalizing x with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.cons_append, evalV]
    cases X.vstep I S x n with
    | none => rfl
    | some y => exact ih y

theorem evalV_singleton (x : Elem I.K) (n : String) : X.evalV I S x [n] = X.vstep I S x n := by
  simp only [evalV]
  cases X.vstep I S x n <;> rfl

theorem vstep_val {v w : ValueType} {n : String} (h : L.conv? v n = some w) (k : I.K v) :
    X.vstep I S (.val v k) n = some (.val w (I.F.map (L.convMor n h) k)) := by
  change (match h : L.conv? v n with
    | some w' => some (Elem.val w' (I.F.map (L.convMor n h) k))
    | none => none) = _
  split
  · rename_i u' h'
    obtain rfl : u' = w := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    exact absurd (h'.symm.trans h) (by simp)

theorem vstep_val_none {v : ValueType} {n : String} (h : L.conv? v n = none) (k : I.K v) :
    X.vstep I S (.val v k) n = none := by
  change (match h : L.conv? v n with
    | some w' => some (Elem.val w' (I.F.map (L.convMor n h) k))
    | none => none) = _
  split
  · rename_i u' h'
    exact absurd (h'.symm.trans h) (by simp)
  · rfl

variable [∀ v, DecidableEq (I.K v)]

/-- Applying the state with conversions of `X` to the morphism of a path is following
its names through the columns of `X` and the conversions of `I`. -/
theorem evalV_vmor (hS : S.WellFormed) (hX : X.check S = true) {a b : S.VObj L}
    (p : Quiver.Path a b) (x : X.Carrier ⟨a.1, a.2⟩) :
    X.evalV I S x.1 (vnames p) =
      some (((X.toState hX).vext I hS).F.map (vmor p) x : X.Carrier ⟨b.1, b.2⟩).1 := by
  induction p with
  | nil =>
    change some x.1 = some (((X.toState hX).vext I hS).F.map (𝟙 _) x : X.Carrier _).1
    rw [CategoryTheory.Functor.map_id]
    rfl
  | cons p e ih =>
    rename_i c d
    rw [vnames_cons, evalV_append, ih, Option.bind_some, evalV_singleton, vmor_cons,
      CategoryTheory.Functor.map_comp, types_comp_apply]
    generalize (((X.toState hX).vext I hS).F.map (vmor p) x : X.Carrier ⟨c.1, c.2⟩) = y
    obtain ⟨⟨e₀⟩ | ⟨v⟩, hc⟩ := c
    · obtain ⟨_ | _, hy⟩ := y
      · exact step_stepIn hX (show S.step? (.entity e₀) e.1 = some d.1 from e.2) ⟨_, hy⟩
      · exact absurd (show X.Has _ (.entity e₀) from hy) (by simp [Has])
    · obtain ⟨⟨_⟩ | ⟨w⟩, hd⟩ := d
      · exact absurd e.2 not_vstep?_value_entity
      obtain ⟨_ | ⟨v', k⟩, hy⟩ := y
      · exact absurd (show X.Has _ (.value v) from hy) (by simp [Has])
      have hv : v' = v := hy
      subst hv
      have hc' := conv?_of_vstep? e.2
      change (match h : L.conv? v' e.1 with
        | some w => some (Elem.val w (I.F.map (L.convMor e.1 h) k))
        | none => none) = _
      split
      · rename_i w' h'
        obtain rfl : w' = w := Option.some.inj (h'.symm.trans hc')
        rfl
      · rename_i h'
        exact absurd (h'.symm.trans hc') (by simp)

/-- A step along a generator or a conversion from an element at its source gives an
element at its target. -/
theorem vstep_has (hX : X.check S = true) {x : Elem I.K} {o o' : Ob} {n : String}
    (hx : X.Has x o) (h : S.vstep? L o n = some o') :
    ∃ y, X.vstep I S x n = some y ∧ X.Has y o' := by
  cases o with
  | entity e =>
    cases x with
    | val => exact absurd hx (by simp [Has])
    | ent e₀ i => exact step_has hX hx h
  | value v =>
    cases x with
    | ent => exact absurd hx (by simp [Has])
    | val w k =>
      change w = v at hx
      subst hx
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨.val u (I.F.map (L.convMor n hu) k), ?_, rfl⟩
      change (match h : L.conv? w n with
        | some w' => some (Elem.val w' (I.F.map (L.convMor n h) k))
        | none => none) = _
      split
      · rename_i u' h'
        obtain rfl : u' = u := Option.some.inj (h'.symm.trans hu)
        rfl
      · rename_i h'
        exact absurd (h'.symm.trans hu) (by simp)

/-- Following a path of generators and conversions from an element at its source
gives an element at its target. -/
theorem evalV_has (hX : X.check S = true) :
    ∀ {x : Elem I.K} {o o' : Ob} {l : List String}, X.Has x o → S.vtgt? L o l = some o' →
      ∃ y, X.evalV I S x l = some y ∧ X.Has y o'
  | x, _, _, [], hx, h => ⟨x, rfl, Option.some.inj h ▸ hx⟩
  | x, o, o', n :: ns, hx, h => by
    cases hs : S.vstep? L o n with
    | none => simp [hs] at h
    | some o₁ =>
      simp only [vtgt?_cons, hs, Option.bind_some] at h
      obtain ⟨y, hy, hy'⟩ := vstep_has I X hX hx hs
      obtain ⟨z, hz, hz'⟩ := evalV_has hX hy' h
      exact ⟨z, by simp [evalV, hy, hz], hz'⟩

/-- On a path of `S`, following generators and conversions is following generators. -/
theorem evalV_of_tgt? (hX : X.check S = true) :
    ∀ {x : Elem I.K} {o o' : Ob} {l : List String}, X.Has x o → S.tgt? o l = some o' →
      X.evalV I S x l = X.eval S x l
  | _, _, _, [], _, _ => rfl
  | x, o, o', n :: ns, hx, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o₁ =>
      simp only [tgt?_cons, hs, Option.bind_some] at h
      obtain ⟨y, hy, hy'⟩ := step_has hX hx hs
      have hv : X.vstep I S x n = X.step S x n := by
        cases o with
        | value => simp [step?] at hs
        | entity e =>
          cases x with
          | val => exact absurd hx (by simp [Has])
          | ent => rfl
      simp only [evalV, eval, hv, hy, Option.bind_some]
      exact evalV_of_tgt? hX hy' h

end FinState

/-! ## Restriction along a translation with conversions -/

namespace FinState

section VRestrict

variable {L : TypeList} (I : Interp L) (T : Translation) (S S' : Schema) (X : FinState I.K)

/-- The column of the attribute named `n` out of `e` in `Δ_T X`: the value of each
entity along the image path, through the columns of `X` and the conversions of
`I`. -/
def vattrColumn (e n : String) : List (Σ v, I.K v) :=
  (List.range (X.size (T.ent e))).filterMap fun i =>
    match X.evalV I S' (.ent (T.ent e) i) (T.gen (.entity e) n) with
    | some (.val v k) => some ⟨v, k⟩
    | _ => none

/-- Restriction `Δ_T X` of a finite state of `S'` along a translation from `S` valid
with conversions, as data: as `restrict`, with the attribute columns through the
conversions of `I`. -/
def vrestrict : FinState I.K where
  sizes := S.entities.map fun e => (e, X.size (T.ent e))
  refs := S.refs.map fun r => ((r.src, r.name), X.refColumn T S' r.src r.name)
  attrs := S.attrs.map fun a => ((a.src, a.name), X.vattrColumn I T S' a.src a.name)

variable {I T S S' X}

/-- `vrestrict` and `restrict` have the same entities. -/
theorem vrestrict_has {x : Elem I.K} {o : Ob} :
    (X.vrestrict I T S S').Has x o ↔ (X.restrict T S S').Has x o := Iff.rfl

theorem size_vrestrict {e : String} (he : e ∈ S.entities) :
    (X.vrestrict I T S S').size e = X.size (T.ent e) :=
  size_restrict (S' := S') he

theorem refCol_vrestrict {r : Ref} (hr : r ∈ S.refs) :
    (X.vrestrict I T S S').refCol r.src r.name = some (X.refColumn T S' r.src r.name) :=
  refCol_restrict hr

theorem attrCol_vrestrict {a : Attr} (ha : a ∈ S.attrs) :
    (X.vrestrict I T S S').attrCol a.src a.name = some (X.vattrColumn I T S' a.src a.name) :=
  lookup_map_key (fun a : Attr => (a.src, a.name)) (fun k => X.vattrColumn I T S' k.1 k.2)
    S.attrs (List.mem_map.mpr ⟨a, ha, rfl⟩)

variable [∀ v, DecidableEq (I.K v)]

/-- A step of `Δ_T X` along a generator is the image path in `X`, through the
conversions of `I`. -/
theorem vrestrict_step (hS : S.WellFormed) (hX : X.check S' = true) (hT : T.VValid L S S')
    {x : Elem I.K} {o o' : Ob} {n : String} (ho : S.IsOb o)
    (hx : (X.vrestrict I T S S').Has x o) (hs : S.step? o n = some o') :
    ∃ y, (X.vrestrict I T S S').step S x n = some y ∧ (X.vrestrict I T S S').Has y o' ∧
      X.evalV I S' (rename T x) (T.gen o n) = some (rename T y) := by
  cases o with
  | value => simp [Schema.step?] at hs
  | entity e =>
  cases x with
  | val => exact hx.elim
  | ent e₀ i =>
  obtain ⟨rfl, hi⟩ := hx
  have hi' : i < X.size (T.ent e₀) := size_vrestrict ho ▸ hi
  have hs₀ := hs
  have hx₀ : X.Has (.ent (T.ent e₀) i) (T.ob (.entity e₀)) := ⟨rfl, hi'⟩
  simp only [Schema.step?] at hs
  cases hr : S.ref? e₀ n with
  | some r =>
    rw [hr] at hs
    cases hs
    obtain ⟨hrm, hrs, hrn⟩ := ref?_spec hr
    have ht := hT.ref r hrm
    rw [hrs, hrn] at ht
    obtain ⟨z, hz, hz₁⟩ := eval_has hX hx₀ ht
    cases z with
    | val => exact hz₁.elim
    | ent e₁ j =>
      obtain ⟨he₁, hj⟩ := hz₁
      have hcol : (X.refColumn T S' e₀ n)[i]? = some j := by
        simp only [refColumn, List.getElem?_map, List.getElem?_range hi', Option.map_some]
        rw [hz]
      refine ⟨.ent r.tgt j, ?_, ⟨rfl, ?_⟩, ?_⟩
      · have := refCol_vrestrict (X := X) (I := I) (T := T) (S' := S') hrm
        rw [hrs, hrn] at this
        simp [step, hr, this, hcol]
      · rw [size_vrestrict (Schema.isOb_of_step? hS hs₀)]
        exact he₁ ▸ hj
      · simp only [rename]
        rw [evalV_of_tgt? I X hX hx₀ ht, hz, he₁]
  | none =>
    rw [hr] at hs
    cases ha : S.attr? e₀ n with
    | none => simp [ha] at hs
    | some a =>
      rw [ha] at hs
      cases hs
      obtain ⟨ham, has, han⟩ := attr?_spec ha
      have ht := hT.attr a ham
      rw [has, han] at ht
      obtain ⟨z, hz, hz₁⟩ := evalV_has I X hX hx₀ ht
      cases z with
      | ent => exact hz₁.elim
      | val v k =>
        have hall : ∀ m < X.size (T.ent e₀),
            (match X.evalV I S' (.ent (T.ent e₀) m) (T.gen (.entity e₀) n) with
              | some (.val v k) => some (⟨v, k⟩ : Σ v, I.K v)
              | _ => none).isSome := by
          intro m hm
          obtain ⟨z', hz', hz₂⟩ := evalV_has I X hX
            (show X.Has (.ent (T.ent e₀) m) (T.ob (.entity e₀)) from ⟨rfl, hm⟩) ht
          cases z' with
          | ent => exact hz₂.elim
          | val => simp [hz']
        have hcol : (X.vattrColumn I T S' e₀ n)[i]? = some ⟨v, k⟩ := by
          rw [vattrColumn, (filterMap_range _ _ hall).2 i hi', hz]
        refine ⟨.val v k, ?_, hz₁, ?_⟩
        · have := attrCol_vrestrict (X := X) (I := I) (T := T) (S' := S') ham
          rw [has, han] at this
          simp [step, hr, ha, this, hcol]
        · simpa [rename] using hz

/-- Following a path of `S` in `Δ_T X` is following its image in `X`, through the
conversions of `I`. -/
theorem vrestrict_eval (hS : S.WellFormed) (hX : X.check S' = true) (hT : T.VValid L S S') :
    ∀ {x : Elem I.K} {o o' : Ob} {l : List String}, S.IsOb o →
      (X.vrestrict I T S S').Has x o → S.tgt? o l = some o' →
      ∃ y, (X.vrestrict I T S S').eval S x l = some y ∧ (X.vrestrict I T S S').Has y o' ∧
        X.evalV I S' (rename T x) (T.mapPath S o l) = some (rename T y)
  | x, _, _, [], _, hx, h => ⟨x, rfl, Option.some.inj h ▸ hx, rfl⟩
  | x, o, o', n :: ns, ho, hx, hl => by
    cases hs : S.step? o n with
    | none => simp [hs] at hl
    | some o₁ =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at hl
      obtain ⟨y, hy, hy', hey⟩ := vrestrict_step hS hX hT ho hx hs
      obtain ⟨z, hz, hz', hez⟩ :=
        vrestrict_eval hS hX hT (Schema.isOb_of_step? hS hs) hy' hl
      refine ⟨z, by simp [eval, hy, hz], hz', ?_⟩
      simp only [Translation.mapPath, hs]
      rw [evalV_append, hey, Option.bind_some, hez]

/-- `Δ_T X` passes the check. -/
theorem vrestrict_check (hS : S.WellFormed) (hS' : S'.WellFormed) (hX : X.check S' = true)
    (hT : T.VValid L S S') : (X.vrestrict I T S S').check S = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨fun r hr => ?_, fun a ha => ?_⟩, fun q hq i hi => ?_⟩
  · rw [refCol_vrestrict hr]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    refine ⟨by simp [refColumn, size_vrestrict (hS.ref_src r hr)], fun j hj => ?_⟩
    simp only [refColumn, List.mem_map, List.mem_range] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    obtain ⟨z, hz, hz₁⟩ := eval_has hX
      (show X.Has (.ent (T.ent r.src) i) (T.ob (.entity r.src)) from ⟨rfl, hi⟩) (hT.ref r hr)
    cases z with
    | val => exact hz₁.elim
    | ent e₁ j =>
      obtain ⟨he₁, hj'⟩ := hz₁
      rw [hz]
      change j < (X.restrict T S S').size r.tgt
      rw [size_restrict (hS.ref_tgt r hr)]
      exact he₁ ▸ hj'
  · rw [attrCol_vrestrict ha]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    have hall : ∀ m < X.size (T.ent a.src),
        (match X.evalV I S' (.ent (T.ent a.src) m) (T.gen (.entity a.src) a.name) with
          | some (.val v k) => some (⟨v, k⟩ : Σ v, I.K v)
          | _ => none).isSome := by
      intro m hm
      obtain ⟨z, hz, hz₁⟩ := evalV_has I X hX
        (show X.Has (.ent (T.ent a.src) m) (T.ob (.entity a.src)) from ⟨rfl, hm⟩) (hT.attr a ha)
      cases z with
      | ent => exact hz₁.elim
      | val => simp [hz]
    refine ⟨by
      rw [vattrColumn, (filterMap_range _ _ hall).1]
      exact (size_vrestrict (hS.attr_src a ha)).symm, fun x hx => ?_⟩
    obtain ⟨m, hm, hmx⟩ := List.mem_filterMap.mp hx
    rw [List.mem_range] at hm
    obtain ⟨z, hz, hz₁⟩ := evalV_has I X hX
      (show X.Has (.ent (T.ent a.src) m) (T.ob (.entity a.src)) from ⟨rfl, hm⟩) (hT.attr a ha)
    rw [hz] at hmx
    cases z with
    | ent => exact hz₁.elim
    | val v k =>
      cases hmx
      exact hz₁
  · have hsrc := hS.eqn_src q hq
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
    have hx : (X.vrestrict I T S S').Has (.ent q.src i) (.entity q.src) := ⟨rfl, hi⟩
    obtain ⟨y₁, h₁, h₁', e₁⟩ :=
      vrestrict_eval hS hX hT (show S.IsOb (.entity q.src) from hsrc) hx hl
    obtain ⟨y₂, h₂, h₂', e₂⟩ :=
      vrestrict_eval hS hX hT (show S.IsOb (.entity q.src) from hsrc) hx hr
    rw [h₁, h₂]
    congr 1
    apply rename_injective (X := X) (T := T) (S := S) (S' := S') h₁' h₂'
    obtain ⟨hm, b, p, p', hp, hp', hpp⟩ := hT.eqn q hq
    have hx' : X.Has (.ent (T.ent q.src) i) (.entity (T.ent q.src)) :=
      ⟨rfl, size_vrestrict hsrc ▸ hi⟩
    have m₁ := evalV_vmor I X hS' hX p ⟨.ent (T.ent q.src) i, hx'⟩
    have m₂ := evalV_vmor I X hS' hX p' ⟨.ent (T.ent q.src) i, hx'⟩
    rw [hp] at m₁
    rw [hp'] at m₂
    change X.evalV I S' (.ent (T.ent q.src) i) _ = _ at e₁ e₂
    rw [e₁] at m₁
    rw [e₂] at m₂
    rw [Option.some.inj m₁, Option.some.inj m₂, hpp]

/-- The elements of `Δ_T X` at `a` are the elements of `X` at the image of `a`. -/
def vrestrictEquiv (hT : T.VValid L S S') (a : S.Obj) :
    (X.vrestrict I T S S').Carrier a ≃ X.Carrier (S := S') ⟨T.ob a.1, hT.isOb_ob a.2⟩ where
  toFun x := ⟨rename T x.1, rename_has (X := X) (S' := S') a.2 x.2⟩
  invFun z := ⟨unrename a.1 z.1, unrename_has (X := X) (S' := S') a.2 z.2⟩
  left_inv x := Subtype.ext (unrename_rename (X := X) (S' := S') x.2)
  right_inv z := Subtype.ext (rename_unrename (X := X) z.2)

/-- `Δ_T X` computed on data is isomorphic to `Δ_T` applied to the state with
conversions of `X`, restricted to `S.cat`. -/
def vrestrictIso (hS : S.WellFormed) (hS' : S'.WellFormed) (hX : X.check S' = true)
    (hT : T.VValid L S S') :
    (X.vrestrict I T S S').toState (vrestrict_check hS hS' hX hT) ≅
      (T.vrestrictState hS hS' hT ((X.toState hX).vext I hS')).toState :=
  let N : (X.vrestrict I T S S').functor (vrestrict_check hS hS' hX hT) ≅
      S.vinc L ⋙ T.vfunctor hS hS' hT ⋙ vextF hS' (X.toState hX) :=
    NatIso.ofComponents (fun c => (vrestrictEquiv hT c.as).toIso) (by
      intro c d f
      obtain ⟨a, rfl⟩ := Schema.obj_surjective c
      obtain ⟨b, rfl⟩ := Schema.obj_surjective d
      obtain ⟨p, rfl⟩ := Schema.mor_surjective f
      funext x
      apply Subtype.ext
      change rename T ((X.vrestrict I T S S').functor (vrestrict_check hS hS' hX hT)
          |>.map (Schema.mor p) x).1 =
        ((vextF hS' (X.toState hX)).map
          (vmor (T.vfunctorPath hS' hT ((Paths.lift (S.vincPre L)).map p)))
          ⟨rename T x.1, rename_has (X := X) (S' := S') a.2 x.2⟩).1
      have e₁ := eval_map (vrestrict_check hS hS' hX hT) p x
      have e₂ := evalV_vmor I X hS' hX (T.vfunctorPath hS' hT ((Paths.lift (S.vincPre L)).map p))
        ⟨rename T x.1, rename_has (X := X) (S' := S') a.2 x.2⟩
      rw [T.vnames_vfunctorPath, vnames_vincPath, show T.vmapPath S L
        ((Paths.lift (S.vincPre L)).obj a).1 (names p) = T.mapPath S a.1 (names p) from
          T.vmapPath_of_tgt? (Schema.tgt?_names p)] at e₂
      obtain ⟨y, hy, -, hey⟩ := vrestrict_eval hS hX hT a.2 x.2 (Schema.tgt?_names p)
      rw [hey] at e₂
      rw [hy] at e₁
      rw [← Option.some.inj e₁]
      exact Option.some.inj e₂)
  { hom := ⟨N.hom, fun v x => by
      obtain ⟨x, hx⟩ := x
      cases x with
      | ent => exact hx.elim
      | val w k =>
        change w = v at hx
        subst hx
        change (vextValues hS' (X.toState hX)).hom.app (L.vobjOf w)
          ((eqToHom (by rw [← Functor.assoc, T.vvals_comp_vfunctor hS hS' hT]) :
            S.vvals L ⋙ T.vfunctor hS hS' hT ⋙ vextF hS' (X.toState hX) ⟶
            S'.vvals L ⋙ vextF hS' (X.toState hX)).app (L.vobjOf w) ⟨.val w k, rfl⟩) = k
        rw [eqToHom_app]
        rfl⟩
    inv := ⟨N.inv, fun v x => by
      obtain ⟨x, hx⟩ := x
      cases x with
      | ent => exact hx.elim
      | val w k =>
        change w = v at hx
        subst hx
        change _ = (vextValues hS' (X.toState hX)).hom.app (L.vobjOf w)
          ((eqToHom (by rw [← Functor.assoc, T.vvals_comp_vfunctor hS hS' hT]) :
            S.vvals L ⋙ T.vfunctor hS hS' hT ⋙ vextF hS' (X.toState hX) ⟶
            S'.vvals L ⋙ vextF hS' (X.toState hX)).app (L.vobjOf w) ⟨.val w k, rfl⟩)
        rw [eqToHom_app]
        rfl⟩
    hom_inv_id := Schema.State.Hom.ext N.hom_inv_id
    inv_hom_id := Schema.State.Hom.ext N.inv_hom_id }

end VRestrict

end FinState


end DDD
