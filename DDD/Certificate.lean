import DDD.Compose
import DDD.LitData
import DDD.Keys

/-!
# Certificates

A certificate is a document produced outside Lean, by the Julia side: named
schemas, named finite states, and claims about them. Each kind of claim has a
check (`Certificate.checkClaim`) and a meaning (`Certificate.Holds`), and a
claim that passes its check holds (`Certificate.checkClaim_sound`).

- `wellFormed`, `acyclic`: a schema is well formed, and acyclic.
- `translation`: a translation between two schemas is valid with the conversions
  of the list of value types (`Translation.VValid`), checked with
  `Schema.pathEqV`; an attribute may go to a path that ends in conversions.
- `gluing`: a schema computed outside Lean is the gluing of two schemas along a
  kernel, up to the order of its lists (`Schema.checkSameUpToOrder`). Its
  schema category is then the pushout in `Cat` of the kernel span, with the
  inclusions as legs (`Gluing.isPushout_of_perm`). Optionally, the strict
  non-interference check is expected to give the stated results; a result `true`
  proves that the leg is full and faithful.
- `keysKept`: a translation between two schemas keeps the keys of its source
  (`Translation.KeysKept`), so restriction along it keeps keys
  (`Translation.restrictState_keys`, `FinState.restrict_checkKeys`).
- `valueTypes`: the list of value types of the certificate is sound
  (`TypeList.Sound`).
- `declared`: the list of value types admits the value type of every attribute of
  a schema.
- `state`: a finite state is a state of its schema, its values are literals of
  the declared types in normal form, and it satisfies the keys of its schema:
  declared keys, value objects and subtypes (`Schema.State.Keys`). The reader
  puts the literals of each state in normal form (`FinState.normalize`), so a
  literal written in another form passes, and one that is not a value of its
  type fails.
- `restriction`: a finite state is the restriction of another along a
  translation. Along a valid translation, its state is isomorphic to
  `Translation.restrictState` (`FinState.IsRestriction`); along a translation
  that converts, for a sound list, its state in the literal interpretation is
  isomorphic to `Translation.vrestrictState` (`FinState.IsVRestriction`), and the
  check computes it with `FinState.vrestrictLit`.
- `homomorphism`: a homomorphism of finite states that is a morphism of their
  states.
- `pathEquality`: two paths out of an object of a schema present the same
  morphism of the category with conversions (`Schema.VPathEq`), checked by
  `Schema.pathEqV`.
- `conversion`: a path of conversions out of a value type, applied to a literal
  in normal form (`TypeList.applyLit`), gives a literal; the Julia side computes
  it on its own.

Presentations that list the same things in another order present isomorphic
categories (`Schema.isoOfPerm`).
-/

namespace DDD

open CategoryTheory Lean

/-! ## Presentations up to the order of their lists -/

namespace Schema

/-- `S` and `S'` list the same entity types, references, attributes, equations,
value objects, keys and subtypes, possibly in another order, and the same
aggregates, with members possibly in another order. -/
def checkSameUpToOrder (S S' : Schema) : Bool :=
  S.entities.isPerm S'.entities && S.refs.isPerm S'.refs && S.attrs.isPerm S'.attrs &&
  S.eqns.isPerm S'.eqns && S.valueObjects.isPerm S'.valueObjects &&
  S.keys.isPerm S'.keys && S.subtypes.isPerm S'.subtypes &&
  S.aggregates.length == S'.aggregates.length &&
  S.aggregates.all fun A => S'.aggregates.any fun A' =>
    A'.root == A.root && A.members.isPerm A'.members

variable {S S' : Schema}

theorem perm_of_checkSameUpToOrder (h : S.checkSameUpToOrder S' = true) :
    S.entities.Perm S'.entities ∧ S.refs.Perm S'.refs ∧ S.attrs.Perm S'.attrs ∧
      S.eqns.Perm S'.eqns := by
  simp only [checkSameUpToOrder, Bool.and_eq_true, List.isPerm_iff, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The empty translation from `S` to a schema that lists the same entity types,
generators and equations is valid. -/
theorem valid_empty_of_perm (hS : S.WellFormed) (hS' : S'.WellFormed)
    (he : S.entities.Perm S'.entities) (hr : S.refs.Perm S'.refs) (ha : S.attrs.Perm S'.attrs)
    (hq : S.eqns.Perm S'.eqns) : ({} : Translation).Valid S S' where
  entity _ h := he.subset h
  ref r h := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    exact step?_of_mem_refs hS' (hr.subset h)
  attr a h := by
    simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
    exact step?_of_mem_attrs hS' (ha.subset h)
  eqn q h := by
    obtain ⟨o, hl, hr'⟩ := hS.eqn_parallel q h
    rw [Translation.mapPath_empty hl, Translation.mapPath_empty hr']
    exact ⟨he.subset (hS.eqn_src q h), pathEq_of_mem_eqns hS' (hq.subset h)⟩

/-- Presentations that list the same entity types, generators and equations
present isomorphic categories. -/
def isoOfPerm (hS : S.WellFormed) (hS' : S'.WellFormed) (he : S.entities.Perm S'.entities)
    (hr : S.refs.Perm S'.refs) (ha : S.attrs.Perm S'.attrs) (hq : S.eqns.Perm S'.eqns) :
    S.cat ≅ S'.cat where
  hom := Translation.functor hS' (valid_empty_of_perm hS hS' he hr ha hq)
  inv := Translation.functor hS (valid_empty_of_perm hS' hS he.symm hr.symm ha.symm hq.symm)
  hom_inv_id := (Translation.functor_empty_comp_empty hS' hS _ _
    (Translation.empty_valid_self hS)).trans (Translation.functor_empty_self hS _)
  inv_hom_id := (Translation.functor_empty_comp_empty hS hS' _ _
    (Translation.empty_valid_self hS')).trans (Translation.functor_empty_self hS' _)

end Schema

/-- A schema that lists the same things as the glued schema, in another order, is
also a pushout of the kernel span, with the inclusions as legs. -/
theorem Gluing.isPushout_of_perm (D : Gluing) {G : Schema} (hG : G.WellFormed)
    (he : D.glued.entities.Perm G.entities) (hr : D.glued.refs.Perm G.refs)
    (ha : D.glued.attrs.Perm G.attrs) (hq : D.glued.eqns.Perm G.eqns)
    (hl : ({} : Translation).Valid D.left G) (hr' : ({} : Translation).Valid D.right G) :
    IsPushout (C := Cat.{0, 0}) D.ι₁ D.ι₂ (Translation.functor hG hl)
      (Translation.functor hG hr') :=
  D.isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Schema.isoOfPerm D.wf_glued hG he hr ha hq) (by simp) (by simp)
    (by
      rw [Iso.refl_hom, Category.id_comp]
      exact Translation.functor_empty_comp_empty D.wf_glued hG _ _ _)
    (by
      rw [Iso.refl_hom, Category.id_comp]
      exact Translation.functor_empty_comp_empty D.wf_glued hG _ _ _)

/-- `Y` is the restriction of `X` along the valid translation `T`: both pass the
check, and the state of `Y` is isomorphic to `Δ_T` applied to the state of `X`. -/
def FinState.IsRestriction (T : Translation) (S S' : Schema) (X Y : FinState LitK) : Prop :=
  ∃ (hS' : S'.WellFormed) (hT : T.Valid S S') (hX : X.check S' = true) (hY : Y.check S = true),
    Nonempty (Y.toState hY ≅ Translation.restrictState hS' hT (X.toState hX))

/-! ## Certificates -/

/-- A claim of a certificate, about named schemas and named states. -/
inductive Claim where
  | wellFormed (schema : String)
  | acyclic (schema : String)
  | translation (source target : String) (T : Translation)
  | keysKept (source target : String) (T : Translation)
  | gluing (kernel left right glued : String) (fullyFaithful : Option (Bool × Bool))
  | state (state : String)
  | valueTypes
  | declared (schema : String)
  | restriction (source target : String) (T : Translation) (state result : String)
  | homomorphism (source target : String) (h : FinHom)
  | pathEquality (schema : String) (src : Ob) (lhs rhs : List String)
  | conversion (type : ValueType) (path : List String) (value result : Lit)

/-- A certificate: the list of value types, named schemas, named finite states with
the name of their schema, and claims. -/
structure Certificate where
  producer : String := ""
  valueTypes : TypeList := {}
  schemas : List (String × Schema)
  states : List (String × String × FinState LitK)
  claims : List Claim

namespace Certificate

variable (c : Certificate)

def schema? (n : String) : Option Schema := c.schemas.lookup n

def state? (n : String) : Option (String × FinState LitK) := c.states.lookup n

/-- The check of a claim. -/
def checkClaim : Claim → Bool
  | .wellFormed s => match c.schema? s with
    | some S => S.checkWellFormed
    | none => false
  | .acyclic s => match c.schema? s with
    | some S => S.checkWellFormed && S.checkAcyclic
    | none => false
  | .translation s t T => match c.schema? s, c.schema? t with
    | some S, some S' =>
      S'.checkWellFormed && T.checkVValid c.valueTypes S S' (S'.pathEqV c.valueTypes)
    | _, _ => false
  | .keysKept s t T => match c.schema? s, c.schema? t with
    | some S, some S' => decide (T.KeysKept S S')
    | _, _ => false
  | .gluing k l r g ff => match c.schema? k, c.schema? l, c.schema? r, c.schema? g with
    | some K, some L, some R, some G =>
      K.checkWellFormed && L.checkWellFormed && R.checkWellFormed && G.checkWellFormed &&
      (Schema.glue L R).checkWellFormed && Schema.checkGluable K L R &&
      (Schema.glue L R).checkSameUpToOrder G &&
      ({} : Translation).checkValid L G G.pathEq && ({} : Translation).checkValid R G G.pathEq &&
      match ff with
      | none => true
      | some (b₁, b₂) => L.checkAcyclic && R.checkAcyclic && G.checkAcyclic &&
        ({} : Translation).checkFullyFaithful L G == b₁ &&
        ({} : Translation).checkFullyFaithful R G == b₂
    | _, _, _, _ => false
  | .state x => match c.state? x with
    | some (s, X) => match c.schema? s with
      | some S => S.checkWellFormed && X.check S && X.litsFit c.valueTypes &&
        X.checkKeys S
      | none => false
    | none => false
  | .valueTypes => c.valueTypes.checkSound
  | .declared s => match c.schema? s with
    | some S => S.attrs.all fun a => c.valueTypes.admits a.tgt
    | none => false
  | .restriction s t T x y => match c.schema? s, c.schema? t, c.state? x, c.state? y with
    | some S, some S', some (sx, X), some (sy, Y) =>
      sx == t && sy == s && S.checkWellFormed && S'.checkWellFormed && X.check S' &&
        ((T.checkValid S S' S'.pathEq && decide (Y = X.restrict T S S')) ||
          (c.valueTypes.checkSound &&
            T.checkVValid c.valueTypes S S' (S'.pathEqV c.valueTypes) &&
            X.litsFit c.valueTypes && decide (Y = X.vrestrictLit c.valueTypes T S S')))
    | _, _, _, _ => false
  | .homomorphism x y h => match c.state? x, c.state? y with
    | some (sx, X), some (sy, Y) => sx == sy && match c.schema? sx with
      | some S => S.checkWellFormed && X.check S && Y.check S && h.check S X Y
      | none => false
    | _, _ => false
  | .pathEquality s o l r => match c.schema? s with
    | some S => S.checkWellFormed && decide (S.IsOb o) && S.pathEqV c.valueTypes o l r
    | none => false
  | .conversion v l x y => match c.valueTypes.convTgt? v l, c.valueTypes.applyLit v l x with
    | some _, .ok z => z == y && (c.valueTypes.normalize v x).toOption == some x
    | _, _ => false

/-- The meaning of a claim. -/
def Holds : Claim → Prop
  | .wellFormed s => ∃ S, c.schema? s = some S ∧ S.WellFormed
  | .acyclic s => ∃ S, c.schema? s = some S ∧ S.WellFormed ∧ S.Acyclic
  | .translation s t T => ∃ S S', c.schema? s = some S ∧ c.schema? t = some S' ∧
      T.VValid c.valueTypes S S'
  | .keysKept s t T => ∃ S S', c.schema? s = some S ∧ c.schema? t = some S' ∧
      T.KeysKept S S'
  | .gluing k l r g ff => ∃ (D : Gluing) (G : Schema) (hG : G.WellFormed)
      (hl : ({} : Translation).Valid D.left G) (hr : ({} : Translation).Valid D.right G),
      c.schema? k = some D.kernel ∧ c.schema? l = some D.left ∧ c.schema? r = some D.right ∧
      c.schema? g = some G ∧
      IsPushout (C := Cat.{0, 0}) D.ι₁ D.ι₂ (Translation.functor hG hl)
        (Translation.functor hG hr) ∧
      (ff.map (·.1) = some true →
        (Translation.functor hG hl).Full ∧ (Translation.functor hG hl).Faithful) ∧
      (ff.map (·.2) = some true →
        (Translation.functor hG hr).Full ∧ (Translation.functor hG hr).Faithful)
  | .state x => ∃ (s : String) (S : Schema) (X : FinState LitK) (_ : S.WellFormed)
      (hX : X.check S = true),
      c.state? x = some (s, X) ∧ c.schema? s = some S ∧ (X.toState hX).Keys
  | .valueTypes => c.valueTypes.Sound
  | .declared s =>
    ∃ S, c.schema? s = some S ∧ ∀ a ∈ S.attrs, c.valueTypes.admits a.tgt = true
  | .restriction s t T x y => ∃ (S S' : Schema) (X Y : FinState LitK),
      c.schema? s = some S ∧ c.schema? t = some S' ∧ c.state? x = some (t, X) ∧
      c.state? y = some (s, Y) ∧
      (FinState.IsRestriction T S S' X Y ∨ FinState.IsVRestriction c.valueTypes T S S' X Y)
  | .homomorphism x y _ => ∃ (s : String) (S : Schema) (X Y : FinState LitK)
      (hX : X.check S = true) (hY : Y.check S = true),
      c.state? x = some (s, X) ∧ c.state? y = some (s, Y) ∧ c.schema? s = some S ∧
      Nonempty (X.toState hX ⟶ Y.toState hY)
  | .pathEquality s o l r => ∃ (S : Schema) (_ : S.WellFormed) (ho : S.IsOb o),
      c.schema? s = some S ∧ S.VPathEq c.valueTypes ⟨o, ho⟩ l r
  | .conversion v l x y => (c.valueTypes.convTgt? v l).isSome ∧
      c.valueTypes.normalize v x = .ok x ∧ c.valueTypes.applyLit v l x = .ok y

/-- A claim that passes its check holds. -/
theorem checkClaim_sound (cl : Claim) (h : c.checkClaim cl = true) : c.Holds cl := by
  cases cl with
  | wellFormed s =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
      simp only [hs] at h
      exact ⟨S, hs, (Schema.checkWellFormed_iff S).mp h⟩
  | acyclic s =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
      simp only [hs, Bool.and_eq_true] at h
      exact ⟨S, hs, (Schema.checkWellFormed_iff S).mp h.1, Schema.checkAcyclic_iff.mp h.2⟩
  | translation s t T =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
    cases ht : c.schema? t with
    | none => simp [hs, ht] at h
    | some S' =>
      simp only [hs, ht, Bool.and_eq_true] at h
      have hw := (Schema.checkWellFormed_iff S').mp h.1
      exact ⟨S, S', hs, ht, Translation.checkVValid_sound
        (fun a _ _ hp => Schema.pathEqV_sound hw a hp) h.2⟩
  | keysKept s t T =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
    cases ht : c.schema? t with
    | none => simp [hs, ht] at h
    | some S' =>
      simp only [hs, ht, decide_eq_true_eq] at h
      exact ⟨S, S', hs, ht, h⟩
  | gluing k l r g ff =>
    simp only [checkClaim] at h
    cases hK : c.schema? k with
    | none => simp [hK] at h
    | some K =>
    cases hL : c.schema? l with
    | none => simp [hK, hL] at h
    | some L =>
    cases hR : c.schema? r with
    | none => simp [hK, hL, hR] at h
    | some R =>
    cases hG : c.schema? g with
    | none => simp [hK, hL, hR, hG] at h
    | some G =>
    simp only [hK, hL, hR, hG, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨wK, wL⟩, wR⟩, wG⟩, wglue⟩, hgl⟩, hsame⟩, hvl⟩, hvr⟩, hff⟩ := h
    have wK' := (Schema.checkWellFormed_iff K).mp wK
    have wL' := (Schema.checkWellFormed_iff L).mp wL
    have wR' := (Schema.checkWellFormed_iff R).mp wR
    have wG' := (Schema.checkWellFormed_iff G).mp wG
    have wglue' := (Schema.checkWellFormed_iff _).mp wglue
    let D : Gluing := ⟨K, L, R, wK', wL', wR', wglue', Schema.checkGluable_sound wL' wR' hgl⟩
    have hl : ({} : Translation).Valid D.left G :=
      Translation.checkValid_sound (fun a _ _ hp => Schema.pathEq_sound wG' a hp) hvl
    have hr : ({} : Translation).Valid D.right G :=
      Translation.checkValid_sound (fun a _ _ hp => Schema.pathEq_sound wG' a hp) hvr
    obtain ⟨he, hrf, ha, hq⟩ := Schema.perm_of_checkSameUpToOrder hsame
    refine ⟨D, G, wG', hl, hr, hK, hL, hR, hG,
      D.isPushout_of_perm wG' he hrf ha hq hl hr, ?_, ?_⟩
    · intro hb
      cases ff with
      | none => simp at hb
      | some b =>
        obtain ⟨b₁, b₂⟩ := b
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hff
        exact Translation.checkFullyFaithful_sound wL' wG'
          (Schema.checkAcyclic_iff.mp hff.1.1.1.1) (Schema.checkAcyclic_iff.mp hff.1.1.2) hl
          hff.1.2
    · intro hb
      cases ff with
      | none => simp at hb
      | some b =>
        obtain ⟨b₁, b₂⟩ := b
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hff
        exact Translation.checkFullyFaithful_sound wR' wG'
          (Schema.checkAcyclic_iff.mp hff.1.1.1.2) (Schema.checkAcyclic_iff.mp hff.1.1.2) hr
          hff.2
  | state x =>
    simp only [checkClaim] at h
    cases hx : c.state? x with
    | none => simp [hx] at h
    | some p =>
    obtain ⟨s, X⟩ := p
    cases hs : c.schema? s with
    | none => simp [hx, hs] at h
    | some S =>
    simp only [hx, hs, Bool.and_eq_true] at h
    obtain ⟨⟨⟨wS, hX⟩, -⟩, hv⟩ := h
    have wS' := (Schema.checkWellFormed_iff S).mp wS
    exact ⟨s, S, X, wS', hX, hx, hs, FinState.toState_keys wS' hX hv⟩
  | valueTypes =>
    simp only [checkClaim] at h
    exact (TypeList.checkSound_iff _).mp h
  | declared s =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
      simp only [hs, List.all_eq_true] at h
      exact ⟨S, hs, h⟩
  | restriction s t T x y =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
    cases ht : c.schema? t with
    | none => simp [hs, ht] at h
    | some S' =>
    cases hx : c.state? x with
    | none => simp [hs, ht, hx] at h
    | some p =>
    obtain ⟨sx, X⟩ := p
    cases hy : c.state? y with
    | none => simp [hs, ht, hx, hy] at h
    | some q =>
    obtain ⟨sy, Y⟩ := q
    simp only [hs, ht, hx, hy, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, wS⟩, wS'⟩, hX⟩, h⟩ := h
    have wS₁ := (Schema.checkWellFormed_iff S).mp wS
    have wS'₁ := (Schema.checkWellFormed_iff S').mp wS'
    refine ⟨S, S', X, Y, hs, ht, hx, hy, ?_⟩
    rcases h with ⟨hT, rfl⟩ | ⟨⟨⟨hL, hT⟩, hfit⟩, rfl⟩
    · have hT' := Translation.checkValid_sound (fun a _ _ hp => Schema.pathEq_sound wS'₁ a hp) hT
      exact Or.inl ⟨wS'₁, hT', hX, FinState.restrict_check wS₁ hX hT',
        ⟨FinState.restrictIso wS₁ wS'₁ hX hT'⟩⟩
    · have hT' := Translation.checkVValid_sound
        (fun a _ _ hp => Schema.pathEqV_sound wS'₁ a hp) hT
      have hL' := (TypeList.checkSound_iff _).mp hL
      exact Or.inr (FinState.isVRestriction_vrestrictLit hL' wS₁ wS'₁ hT'
        (FinState.litsFit_of_check hL' hfit) hX)
  | homomorphism x y hh =>
    simp only [checkClaim] at h
    cases hx : c.state? x with
    | none => simp [hx] at h
    | some p =>
    obtain ⟨sx, X⟩ := p
    cases hy : c.state? y with
    | none => simp [hx, hy] at h
    | some q =>
    obtain ⟨sy, Y⟩ := q
    simp only [hx, hy, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    cases hs : c.schema? sx with
    | none => simp [hs] at h
    | some S =>
    simp only [hs, Bool.and_eq_true] at h
    obtain ⟨⟨⟨wS, hX⟩, hY⟩, hc⟩ := h
    exact ⟨sx, S, X, Y, hX, hY, hx, hy, hs,
      ⟨FinHom.toHom ((Schema.checkWellFormed_iff S).mp wS) hX hY hc⟩⟩
  | pathEquality s o l r =>
    simp only [checkClaim] at h
    cases hs : c.schema? s with
    | none => simp [hs] at h
    | some S =>
      simp only [hs, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨wS, ho⟩, hp⟩ := h
      have hw := (Schema.checkWellFormed_iff S).mp wS
      exact ⟨S, hw, ho, hs, Schema.pathEqV_sound hw ⟨o, ho⟩ hp⟩
  | conversion v l x y =>
    simp only [checkClaim] at h
    split at h
    · rename_i w z hw hz
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hx⟩ := h
      refine ⟨by simp [hw], ?_, hz⟩
      cases hn : c.valueTypes.normalize v x with
      | error => simp [hn, Except.toOption] at hx
      | ok x' =>
        simp only [hn, Except.toOption, Option.some.injEq] at hx
        rw [hx]
    · exact absurd h (by simp)

/-- The check of a certificate: every claim passes. -/
def check : Bool := c.claims.all c.checkClaim

theorem check_sound (h : c.check = true) : ∀ cl ∈ c.claims, c.Holds cl := fun cl hcl =>
  c.checkClaim_sound cl (List.all_eq_true.mp h cl hcl)

end Certificate

/-! ## Reading certificates -/

/-- A short description of a claim, for reports. -/
def Claim.describe : Claim → String
  | .wellFormed s => s!"{s} is well formed"
  | .acyclic s => s!"{s} is acyclic"
  | .translation s t _ => s!"the translation {s} → {t} is valid"
  | .keysKept s t _ => s!"the translation {s} → {t} keeps the keys of {s}"
  | .gluing k l r g ff =>
    let base := s!"{g} is {l} and {r} glued along {k}"
    match ff with
    | none => base
    | some (b₁, b₂) => base ++ s!"; strict non-interference: {l} {b₁}, {r} {b₂}"
  | .state x => s!"{x} is a state of its schema"
  | .valueTypes => "the list of value types is sound"
  | .declared s => s!"the value types of {s} are declared"
  | .restriction s t _ x y => s!"{y} is the restriction of {x} along {s} → {t}"
  | .homomorphism x y _ => s!"a homomorphism {x} → {y}"
  | .pathEquality s o l r =>
    s!"in {s}, the paths {String.intercalate "." l} and {String.intercalate "." r} out of \
      {match o with | .entity e => e | .value v => v.text} are equal"
  | .conversion v l x y =>
    s!"{String.intercalate "." l} out of {v.text} sends {x.render} to {y.render}"

def Claim.fromJson (j : Json) : Except String Claim := do
  match ← j.getObjValAs? String "claim" with
  | "wellFormed" => .wellFormed <$> j.getObjValAs? String "schema"
  | "acyclic" => .acyclic <$> j.getObjValAs? String "schema"
  | "translation" => do
    let s ← j.getObjValAs? String "source"
    let t ← j.getObjValAs? String "target"
    let T ← Translation.fromJson (← j.getObjVal? "translation")
    pure (.translation s t T)
  | "keysKept" => do
    let s ← j.getObjValAs? String "source"
    let t ← j.getObjValAs? String "target"
    let T ← Translation.fromJson (← j.getObjVal? "translation")
    pure (.keysKept s t T)
  | "gluing" => do
    let k ← j.getObjValAs? String "kernel"
    let l ← j.getObjValAs? String "left"
    let r ← j.getObjValAs? String "right"
    let g ← j.getObjValAs? String "glued"
    let ff ← match j.getObjVal? "fullyFaithful" with
      | .ok v => do
        let bs ← v.getArr?
        match bs.toList with
        | [b₁, b₂] => pure (some (← b₁.getBool?, ← b₂.getBool?))
        | _ => throw "fullyFaithful takes two booleans"
      | .error _ => pure none
    pure (.gluing k l r g ff)
  | "state" => .state <$> j.getObjValAs? String "state"
  | "valueTypes" => pure .valueTypes
  | "declared" => .declared <$> j.getObjValAs? String "schema"
  | "restriction" => do
    let s ← j.getObjValAs? String "source"
    let t ← j.getObjValAs? String "target"
    let T ← Translation.fromJson (← j.getObjVal? "translation")
    let x ← j.getObjValAs? String "state"
    let y ← j.getObjValAs? String "result"
    pure (.restriction s t T x y)
  | "homomorphism" => do
    let x ← j.getObjValAs? String "from"
    let y ← j.getObjValAs? String "to"
    let h ← FinHom.fromJson (← j.getObjVal? "homomorphism")
    pure (.homomorphism x y h)
  | "pathEquality" => do
    let s ← j.getObjValAs? String "schema"
    let src ← j.getObjVal? "from"
    let o ← match src.getObjVal? "entity", src.getObjVal? "value" with
      | .ok e, _ => Ob.entity <$> e.getStr?
      | _, .ok v => Ob.value <$> ValueType.fromJson v
      | _, _ => throw "from takes an entity or a value type"
    let l ← j.getObjValAs? (List String) "lhs"
    let r ← j.getObjValAs? (List String) "rhs"
    pure (.pathEquality s o l r)
  | "conversion" => do
    let v ← ValueType.fromJson (← j.getObjVal? "type")
    let l ← j.getObjValAs? (List String) "path"
    let x ← Lit.fromJson (← j.getObjVal? "value")
    let y ← Lit.fromJson (← j.getObjVal? "result")
    pure (.conversion v l x y)
  | other => throw s!"unknown claim {other}"

def Certificate.fromJson (j : Json) : Except String Certificate := do
  let fmt ← j.getObjValAs? String "format"
  unless fmt == formatVersion do throw s!"unsupported format {fmt}"
  let kind ← j.getObjValAs? String "kind"
  unless kind == "certificate" do throw s!"expected a certificate, found {kind}"
  let producer := (j.getObjValAs? String "producer").toOption.getD ""
  let valueTypes ← match j.getObjVal? "valueTypes" with
    | .ok v => TypeList.fromJson v
    | .error _ => pure {}
  let schemas ← (← getList j "schemas").mapM fun s => do
    pure (← s.getObjValAs? String "name", ← Schema.fromJson (← s.getObjVal? "schema"))
  let states ← (← getList j "states").mapM fun x => do
    let name ← x.getObjValAs? String "name"
    let sname ← x.getObjValAs? String "schema"
    let some S := schemas.lookup sname | throw s!"state {name}: unknown schema {sname}"
    pure (name, sname, (← FinState.fromJson S (← x.getObjVal? "state")).normalize valueTypes)
  let claims ← (← getList j "claims").mapM Claim.fromJson
  pure { producer, valueTypes, schemas, states, claims }

end DDD
