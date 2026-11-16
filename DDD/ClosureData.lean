import DDD.Closure
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# The closure of a finite state

`FinState.closure S X` computes the closure of a finite state under the keys of
`S` (`Schema.State.closure`): it identifies the entities that agree on a key, then
what they reference, until nothing changes, and fails when two entities it
identifies have different values.

- `FinState.reps S X`: a representative for each entity. One step merges the
  classes of two entities that agree on every field of a key, up to the classes so
  far, or that two entities of one class refer to (`justified`). The classes are
  contained in the relation of the keys (`inv_reps`).
- `FinState.quotient`, `quotientHom`: the finite state of the classes, and the
  homomorphism onto it.
- `FinState.closure`: the quotient, when it passes its checks (`closedOk`): it is a
  state that satisfies the keys, the homomorphism is one, onto, and identifies
  entities of one class only. Otherwise two entities of one class with different
  values of an attribute, when there are two.
- `closure_closed`: a result `closed Y h` is the closure of the state of `X`: the
  state is consistent, `Y` satisfies the keys, and its state is isomorphic to the
  closure. `closure_inconsistent`: a result `inconsistent` shows that the state is
  not consistent, so no state that satisfies the keys receives it.
- `FinState.sum`: two finite states side by side. When `checkSum` passes, its state
  is the coproduct of the two states (`sumIsColimit`).
- Merges by keys: `merge_closed`, the closure of the sum is the coproduct among the
  states that satisfy the keys; `merge_inconsistent`, when the closure fails no
  state that satisfies the keys receives both.

The result `undetermined` is returned when neither holds; that it does not occur
is not proved.
-/

namespace DDD

open CategoryTheory Limits Schema

namespace FinState

variable {K : ValueType → Type} [∀ v, DecidableEq (K v)]

/-- A representative for each entity, by entity type. An entity without an entry
represents itself. -/
abbrev Reps : Type := List (String × List Nat)

/-- The representative of the entity `i` of `e`. -/
def rep (R : Reps) (e : String) (i : Nat) : Nat := ((R.lookup e).getD []).getD i i

variable (S : Schema) (X : FinState K)

/-- The representatives with the classes of `i` and `j` of `e` merged. -/
def mergeReps (R : Reps) (e : String) (i j : Nat) : Reps :=
  (e, (List.range (X.size e)).map fun k =>
    if rep R e k = rep R e j then rep R e i else rep R e k) :: R

omit [∀ v, DecidableEq (K v)] in
theorem rep_mergeReps (R : Reps) (e : String) (i j : Nat) (e' : String) (k : Nat) :
    rep (X.mergeReps R e i j) e' k =
      if e' = e then
        if k < X.size e then (if rep R e k = rep R e j then rep R e i else rep R e k) else k
      else rep R e' k := by
  by_cases he : e' = e
  · subst he
    by_cases hk : k < X.size e'
    · simp [rep, mergeReps, hk]
    · simp [rep, mergeReps, hk]
  · have : (e' == e) = false := by simpa using he
    simp [rep, mergeReps, List.lookup_cons, this, he]

/-- Two results of a step are the same up to the classes: no step twice, two values
that are equal, or two entities of one class. -/
def same (R : Reps) : Option (Elem K) → Option (Elem K) → Bool
  | some (.ent e a), some (.ent e' b) => e == e' && rep R e a == rep R e b
  | some (.val v x), some (.val w y) => decide (Elem.val v x = Elem.val w y)
  | none, none => true
  | _, _ => false

/-- The entities `i` and `j` of `e` agree on every field of a key of `e`, up to the
classes. -/
def keyJust (R : Reps) (e : String) (i j : Nat) : Bool :=
  S.allKeys.any fun k => k.entity == e && k.fields.all fun n =>
    same R (X.step S (.ent e i) n) (X.step S (.ent e j) n)

/-- The entities `i` and `j` of `e` are the targets of a reference from two entities
of one class. -/
def refJust (R : Reps) (e : String) (i j : Nat) : Bool :=
  S.refs.any fun r => r.tgt == e && (List.range (X.size r.src)).any fun a =>
    (List.range (X.size r.src)).any fun b => rep R r.src a == rep R r.src b &&
      decide (X.step S (.ent r.src a) r.name = some (.ent e i)) &&
      decide (X.step S (.ent r.src b) r.name = some (.ent e j))

/-- The keys force the entities `i` and `j` of `e` to be equal, given the classes. -/
def justified (R : Reps) (c : String × Nat × Nat) : Bool :=
  decide (c.1 ∈ S.entities) && decide (c.2.1 < X.size c.1) && decide (c.2.2 < X.size c.1) &&
    (keyJust S X R c.1 c.2.1 c.2.2 || refJust S X R c.1 c.2.1 c.2.2)

/-- The pairs of distinct entities of one entity type. -/
def candidates : List (String × Nat × Nat) :=
  S.entities.flatMap fun e => (List.range (X.size e)).flatMap fun i =>
    (List.range (X.size e)).filterMap fun j => if i < j then some (e, i, j) else none

/-- A pair of entities of two classes that the keys force to be equal. -/
def findStep (R : Reps) : Option (String × Nat × Nat) :=
  (candidates S X).find? fun c => rep R c.1 c.2.1 != rep R c.1 c.2.2 && justified S X R c

/-- Merging classes, at most `fuel` times. -/
def closeReps : Nat → Reps → Reps
  | 0, R => R
  | fuel + 1, R =>
    match findStep S X R with
    | none => R
    | some c => closeReps fuel (X.mergeReps R c.1 c.2.1 c.2.2)

/-- The classes of the closure: each merge leaves one class fewer, so there are at
most as many merges as entities. -/
def reps : Reps := closeReps S X (S.entities.map X.size).sum []

/-! ## The classes are contained in the relation of the keys -/

variable {S X}

/-- The entities `i` and `j` of `e` are related by the keys. -/
def Rel (hX : X.check S = true) (e : String) (i j : Nat) : Prop :=
  ∃ (he : e ∈ S.entities) (hi : i < X.size e) (hj : j < X.size e),
    (X.toState hX).KeyRel (S.obj ⟨.entity e, he⟩) ⟨.ent e i, ⟨rfl, hi⟩⟩ ⟨.ent e j, ⟨rfl, hj⟩⟩

variable {hX : X.check S = true}

theorem Rel.refl {e : String} {i : Nat} (he : e ∈ S.entities) (hi : i < X.size e) :
    Rel hX e i i :=
  ⟨he, hi, hi, .refl _⟩

theorem Rel.symm {e : String} {i j : Nat} (h : Rel hX e i j) : Rel hX e j i := by
  obtain ⟨he, hi, hj, r⟩ := h
  exact ⟨he, hj, hi, r.symm⟩

theorem Rel.trans {e : String} {i j k : Nat} (h : Rel hX e i j) (h' : Rel hX e j k) :
    Rel hX e i k := by
  obtain ⟨he, hi, hj, r⟩ := h
  obtain ⟨_, _, hk, r'⟩ := h'
  exact ⟨he, hi, hk, r.trans r'⟩

variable (hX) in
/-- Each entity is related to its representative. -/
def Inv (R : Reps) : Prop :=
  ∀ e ∈ S.entities, ∀ k, k < X.size e → Rel hX e k (rep R e k)

theorem inv_nil : Inv hX ([] : Reps) := fun e he k hk => by
  have : rep ([] : Reps) e k = k := by simp [rep]
  rw [this]
  exact Rel.refl he hk

variable {R : Reps}

theorem rel_of_rep_eq (hR : Inv hX R) {e : String} (he : e ∈ S.entities) {a c : Nat}
    (ha : a < X.size e) (hc : c < X.size e) (h : rep R e a = rep R e c) : Rel hX e a c :=
  (hR e he a ha).trans (h ▸ (hR e he c hc).symm)

theorem inv_merge (hR : Inv hX R) {e : String} {i j : Nat} (h : Rel hX e i j) :
    Inv hX (X.mergeReps R e i j) := by
  intro e' he' k hk
  have hh := h
  obtain ⟨he, hi, hj, _⟩ := hh
  rw [rep_mergeReps]
  split_ifs with h₁ h₂ h₃
  · subst h₁
    exact (rel_of_rep_eq hR he hk hj h₃).trans (h.symm.trans (hR e' he i hi))
  · subst h₁
    exact hR e' he k hk
  · subst h₁
    exact absurd hk h₂
  · exact hR e' he' k hk

/-- Two elements that are the same up to the classes are related by the keys. -/
theorem keyRel_of_same (hR : Inv hX R) (b : S.Obj) (u w : X.Carrier b)
    (h : same R (some u.1) (some w.1) = true) : (X.toState hX).KeyRel (S.obj b) u w := by
  obtain ⟨o, ho⟩ := b
  obtain ⟨u, hu⟩ := u
  obtain ⟨w, hw⟩ := w
  cases u with
  | ent e a =>
    cases w with
    | ent e' c =>
      simp only [same, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hr⟩ := h
      cases o with
      | value v => exact hu.elim
      | entity e₀ =>
        obtain ⟨rfl, ha⟩ := hu
        obtain ⟨_, _, _, r⟩ := rel_of_rep_eq hR ho ha hw.2 hr
        exact r
    | val w' y => simp [same] at h
  | val v x =>
    cases w with
    | ent e' c => simp [same] at h
    | val w' y =>
      simp only [same, decide_eq_true_eq] at h
      have e : (⟨.val v x, hu⟩ : X.Carrier ⟨o, ho⟩) = ⟨.val w' y, hw⟩ := Subtype.ext h
      rw [e]
      exact .refl _

/-- Two entities that agree on every field of a key, up to the classes, are related
by the keys. -/
theorem rel_of_key (hR : Inv hX R) {k : Key} (hk : k ∈ S.allKeys) (he : k.entity ∈ S.entities)
    {i j : Nat} (hi : i < X.size k.entity) (hj : j < X.size k.entity)
    (h : ∀ n ∈ k.fields,
      same R (X.step S (.ent k.entity i) n) (X.step S (.ent k.entity j) n) = true) :
    Rel hX k.entity i j := by
  refine ⟨he, hi, hj, State.KeyRel.key k hk he _ _ fun n hn b hb => ?_⟩
  have sx : X.step S (.ent k.entity i) n = some (stepIn hX hb ⟨.ent k.entity i, ⟨rfl, hi⟩⟩).1 :=
    step_stepIn hX hb ⟨.ent k.entity i, ⟨rfl, hi⟩⟩
  have sy : X.step S (.ent k.entity j) n = some (stepIn hX hb ⟨.ent k.entity j, ⟨rfl, hj⟩⟩).1 :=
    step_stepIn hX hb ⟨.ent k.entity j, ⟨rfl, hj⟩⟩
  have hs := h n hn
  rw [sx, sy] at hs
  exact keyRel_of_same hR b _ _ hs

/-- The targets of a reference from two entities of one class are related by the
keys. -/
theorem rel_of_ref (hS : S.WellFormed) (hR : Inv hX R) {r : Ref} (hr : r ∈ S.refs)
    {a b i j : Nat} (ha : a < X.size r.src) (hb : b < X.size r.src)
    (hab : rep R r.src a = rep R r.src b)
    (hi : X.step S (.ent r.src a) r.name = some (.ent r.tgt i))
    (hj : X.step S (.ent r.src b) r.name = some (.ent r.tgt j)) : Rel hX r.tgt i j := by
  have hsrc := hS.ref_src r hr
  have htgt := hS.ref_tgt r hr
  obtain ⟨_, _, _, rab⟩ := rel_of_rep_eq hR hsrc ha hb hab
  have hstep := Schema.step?_of_mem_refs hS hr
  have m := State.KeyRel.map (S.genMor (a := ⟨.entity r.src, hsrc⟩) (b := ⟨.entity r.tgt, htgt⟩)
    r.name hstep) rab
  have sa : X.step S (.ent r.src a) r.name =
      some (stepIn hX hstep ⟨.ent r.src a, ⟨rfl, ha⟩⟩).1 :=
    step_stepIn hX hstep ⟨.ent r.src a, ⟨rfl, ha⟩⟩
  have sb : X.step S (.ent r.src b) r.name =
      some (stepIn hX hstep ⟨.ent r.src b, ⟨rfl, hb⟩⟩).1 :=
    step_stepIn hX hstep ⟨.ent r.src b, ⟨rfl, hb⟩⟩
  rw [hi] at sa
  rw [hj] at sb
  have ea := Option.some.inj sa
  have eb := Option.some.inj sb
  have hi' : i < X.size r.tgt := by
    have := (stepIn hX hstep ⟨.ent r.src a, ⟨rfl, ha⟩⟩).2
    rw [← ea] at this
    exact this.2
  have hj' : j < X.size r.tgt := by
    have := (stepIn hX hstep ⟨.ent r.src b, ⟨rfl, hb⟩⟩).2
    rw [← eb] at this
    exact this.2
  refine ⟨htgt, hi', hj', ?_⟩
  have e₁ : (⟨.ent r.tgt i, ⟨rfl, hi'⟩⟩ : X.Carrier ⟨.entity r.tgt, htgt⟩) =
      stepIn hX hstep ⟨.ent r.src a, ⟨rfl, ha⟩⟩ := Subtype.ext ea
  have e₂ : (⟨.ent r.tgt j, ⟨rfl, hj'⟩⟩ : X.Carrier ⟨.entity r.tgt, htgt⟩) =
      stepIn hX hstep ⟨.ent r.src b, ⟨rfl, hb⟩⟩ := Subtype.ext eb
  rw [e₁, e₂]
  exact m

/-- A justified pair is related by the keys. -/
theorem rel_of_justified (hS : S.WellFormed) (hR : Inv hX R) {c : String × Nat × Nat}
    (h : justified S X R c = true) : Rel hX c.1 c.2.1 c.2.2 := by
  obtain ⟨e, i, j⟩ := c
  simp only [justified, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨he, hi⟩, hj⟩, hk | hr⟩ := h
  · simp only [keyJust, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hk
    obtain ⟨k, hk, rfl, hf⟩ := hk
    exact rel_of_key hR hk he hi hj hf
  · simp only [refJust, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_range,
      decide_eq_true_eq] at hr
    obtain ⟨r, hr, rfl, a, ha, b, hb, ⟨hab, hsa⟩, hsb⟩ := hr
    exact rel_of_ref hS hR hr ha hb hab hsa hsb

theorem inv_closeReps (hS : S.WellFormed) :
    ∀ (fuel : Nat) (R : Reps), Inv hX R → Inv hX (closeReps S X fuel R)
  | 0, _, hR => hR
  | fuel + 1, R, hR => by
    unfold closeReps
    cases hf : findStep S X R with
    | none => exact hR
    | some c =>
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true] at hp
      exact inv_closeReps hS fuel _ (inv_merge hR (rel_of_justified hS hR hp.2))

/-- The classes of the closure are contained in the relation of the keys. -/
theorem inv_reps (hS : S.WellFormed) : Inv hX (reps S X) := inv_closeReps hS _ _ inv_nil

/-! ## The quotient and the result -/

variable (S X)

/-- The entities of `e` that represent themselves, one per class. -/
def classReps (R : Reps) (e : String) : List Nat :=
  (List.range (X.size e)).filter fun k => rep R e k == k

/-- The number of the class of the entity `k` of `e`. -/
def classOf (R : Reps) (e : String) (k : Nat) : Nat := (X.classReps R e).idxOf (rep R e k)

/-- The finite state of the classes: an entity per class, with the references and
the values of its representative. -/
def quotient (R : Reps) : FinState K where
  sizes := S.entities.map fun e => (e, (X.classReps R e).length)
  refs := S.refs.map fun r => ((r.src, r.name), (X.classReps R r.src).map fun k =>
    X.classOf R r.tgt (((X.refCol r.src r.name).getD []).getD k 0))
  attrs := S.attrs.map fun a => ((a.src, a.name), (X.classReps R a.src).filterMap fun k =>
    ((X.attrCol a.src a.name).getD [])[k]?)

/-- Each entity to its class. -/
def quotientHom (R : Reps) : FinHom :=
  ⟨S.entities.map fun e => (e, (List.range (X.size e)).map (X.classOf R e))⟩

/-- The checks of a result: `Y` is a state that satisfies the keys, `h` is a
homomorphism from `X` onto it, and it identifies entities of one class only. -/
def closedOk (R : Reps) (Y : FinState K) (h : FinHom) : Bool :=
  Y.check S && Y.checkKeys S && h.check S X Y &&
  (S.entities.all fun e => (List.range (Y.size e)).all fun c =>
    (List.range (X.size e)).any fun i => (h.comp e).getD i 0 == c) &&
  (S.entities.all fun e => (List.range (X.size e)).all fun i =>
    (List.range (X.size e)).all fun j =>
      (h.comp e).getD i 0 != (h.comp e).getD j 0 || rep R e i == rep R e j)

/-- Two entities of one class with different values of the attribute `n`. -/
def conflict (R : Reps) (e n : String) (i j : Nat) : Bool :=
  decide (e ∈ S.entities) && decide (i < X.size e) && decide (j < X.size e) &&
    rep R e i == rep R e j && (S.attr? e n).isSome &&
    decide (X.step S (.ent e i) n ≠ X.step S (.ent e j) n)

def findConflict (R : Reps) : Option (String × String × Nat × Nat) :=
  (S.attrs.flatMap fun a => (List.range (X.size a.src)).flatMap fun i =>
    (List.range (X.size a.src)).map fun j => (a.src, a.name, i, j)).find? fun c =>
      conflict S X R c.1 c.2.1 c.2.2.1 c.2.2.2

end FinState

/-- The result of the closure of a finite state: the state of the classes with the
homomorphism onto it, or two entities that the keys identify with different values
of an attribute, or neither. -/
inductive ClosureResult (K : ValueType → Type) where
  | closed (Y : FinState K) (h : FinHom)
  | inconsistent (e n : String) (i j : Nat)
  | undetermined

deriving instance DecidableEq for FinHom

instance {K : ValueType → Type} [∀ v, DecidableEq (K v)] : DecidableEq (ClosureResult K)
  | .closed Y h, .closed Y' h' =>
    if q : Y = Y' ∧ h = h' then isTrue (by obtain ⟨rfl, rfl⟩ := q; rfl)
    else isFalse (by intro r; cases r; exact q ⟨rfl, rfl⟩)
  | .inconsistent e n i j, .inconsistent e' n' i' j' =>
    if q : e = e' ∧ n = n' ∧ i = i' ∧ j = j' then isTrue (by obtain ⟨rfl, rfl, rfl, rfl⟩ := q; rfl)
    else isFalse (by intro r; cases r; exact q ⟨rfl, rfl, rfl, rfl⟩)
  | .undetermined, .undetermined => isTrue rfl
  | .closed .., .inconsistent .. => isFalse (by intro r; cases r)
  | .closed .., .undetermined => isFalse (by intro r; cases r)
  | .inconsistent .., .closed .. => isFalse (by intro r; cases r)
  | .inconsistent .., .undetermined => isFalse (by intro r; cases r)
  | .undetermined, .closed .. => isFalse (by intro r; cases r)
  | .undetermined, .inconsistent .. => isFalse (by intro r; cases r)

namespace FinState

variable {K : ValueType → Type} [∀ v, DecidableEq (K v)] (S : Schema) (X : FinState K)

/-- The closure of a finite state under the keys of `S`. -/
def closure : ClosureResult K :=
  if closedOk S X (reps S X) (quotient S X (reps S X)) (quotientHom S X (reps S X)) then
    .closed (quotient S X (reps S X)) (quotientHom S X (reps S X))
  else
    match findConflict S X (reps S X) with
    | some (e, n, i, j) => .inconsistent e n i j
    | none => .undetermined

variable {S X} {hX : X.check S = true} {R : Reps}

/-- A result that passes its checks is the closure: the state of `X` is consistent,
`Y` satisfies the keys, and its state is isomorphic to the closure. -/
theorem closedOk_sound (hS : S.WellFormed) (hR : Inv hX R) {Y : FinState K} {h : FinHom}
    (hok : closedOk S X R Y h = true) :
    ∃ (hY : Y.check S = true) (hc : (X.toState hX).Consistent), (Y.toState hY).Keys ∧
      Nonempty ((X.toState hX).closure hc ≅ Y.toState hY) := by
  simp only [closedOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨hY, hkeys⟩, hhom⟩, hsec⟩, hker⟩ := hok
  have keys := toState_keys hS hY hkeys
  let m : X.toState hX ⟶ Y.toState hY := FinHom.toHom hS hX hY hhom
  have hc : (X.toState hX).Consistent := State.consistent_of_hom m keys
  refine ⟨hY, hc, keys, ⟨State.isoOfBijectiveEntities (State.lift hc keys m) fun e he => ⟨?_, ?_⟩⟩⟩
  · intro q q' hq
    induction q using Quotient.inductionOn with
    | h x =>
    induction q' using Quotient.inductionOn with
    | h x' =>
      obtain ⟨x, hx⟩ := x
      obtain ⟨x', hx'⟩ := x'
      cases x with
      | val => exact hx.elim
      | ent e₁ i =>
        cases x' with
        | val => exact hx'.elim
        | ent e₂ j =>
          obtain ⟨rfl, hi⟩ := hx
          obtain ⟨rfl, hj⟩ := hx'
          have hm : h.mapElem (K := K) (.ent _ i) = h.mapElem (.ent _ j) :=
            congrArg Subtype.val hq
          simp only [FinHom.mapElem, Elem.ent.injEq, true_and] at hm
          rcases hker _ he i hi j hj with hne | heq
          · exact absurd hm hne
          · obtain ⟨_, _, _, r⟩ := rel_of_rep_eq hR he hi hj heq
            exact Quotient.sound r
  · rintro ⟨y, hy⟩
    cases y with
    | val => exact hy.elim
    | ent e₁ c =>
      obtain ⟨rfl, hc'⟩ := hy
      obtain ⟨i, hi, hic⟩ := hsec _ he c hc'
      refine ⟨Quotient.mk _ ⟨.ent _ i, ⟨rfl, hi⟩⟩, Subtype.ext ?_⟩
      change h.mapElem (K := K) (.ent _ i) = .ent _ c
      simp only [FinHom.mapElem, hic]

/-- A result `closed` is the closure of the state of `X`. -/
theorem closure_closed (hS : S.WellFormed) (hX : X.check S = true) {Y : FinState K} {h : FinHom}
    (hc : X.closure S = .closed Y h) :
    ∃ (hY : Y.check S = true) (hc : (X.toState hX).Consistent), (Y.toState hY).Keys ∧
      Nonempty ((X.toState hX).closure hc ≅ Y.toState hY) := by
  unfold closure at hc
  split at hc
  · rename_i hok
    injection hc with h₁ h₂
    subst h₁ h₂
    exact closedOk_sound hS (inv_reps hS) hok
  · split at hc <;> cases hc

/-- Two entities of one class with different values of an attribute show that the
state is not consistent. -/
theorem conflict_sound (hS : S.WellFormed) (hR : Inv hX R) {e n : String} {i j : Nat}
    (h : conflict S X R e n i j = true) : ¬ (X.toState hX).Consistent := by
  intro hc
  simp only [conflict, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isSome_iff_exists]
    at h
  obtain ⟨⟨⟨⟨⟨he, hi⟩, hj⟩, hrep⟩, ⟨a, ha⟩⟩, hne⟩ := h
  obtain ⟨ham, rfl, rfl⟩ := attr?_spec ha
  obtain ⟨_, _, _, r⟩ := rel_of_rep_eq hR he hi hj hrep
  have hstep := Schema.step?_of_mem_attrs hS ham
  have m := State.KeyRel.map (S.genMor (a := ⟨.entity a.src, he⟩) (b := ⟨.value a.tgt, trivial⟩)
    a.name hstep) r
  have e := hc a.tgt _ _ m
  have sa : X.step S (.ent a.src i) a.name =
      some (stepIn hX hstep ⟨.ent a.src i, ⟨rfl, hi⟩⟩).1 :=
    step_stepIn hX hstep ⟨.ent a.src i, ⟨rfl, hi⟩⟩
  have sb : X.step S (.ent a.src j) a.name =
      some (stepIn hX hstep ⟨.ent a.src j, ⟨rfl, hj⟩⟩).1 :=
    step_stepIn hX hstep ⟨.ent a.src j, ⟨rfl, hj⟩⟩
  apply hne
  rw [sa, sb]
  exact congrArg (fun z : X.Carrier ⟨.value a.tgt, trivial⟩ => some z.1) e

/-- A result `inconsistent` shows that the state of `X` is not consistent: no state
that satisfies the keys receives it. -/
theorem closure_inconsistent (hS : S.WellFormed) (hX : X.check S = true) {e n : String}
    {i j : Nat} (hc : X.closure S = .inconsistent e n i j) : ¬ (X.toState hX).Consistent := by
  unfold closure at hc
  split at hc
  · cases hc
  · split at hc
    · rename_i hf
      injection hc with h₁ h₂ h₃ h₄
      subst h₁ h₂ h₃ h₄
      unfold findConflict at hf
      have hcf := List.find?_some hf
      exact conflict_sound hS (inv_reps hS) hcf
    · cases hc

/-! ## The sum of two finite states, and merges -/

variable (S X) (Y : FinState K)

/-- Two finite states side by side: the entities of `X`, then those of `Y`. -/
def sum : FinState K where
  sizes := S.entities.map fun e => (e, X.size e + Y.size e)
  refs := S.refs.map fun r => ((r.src, r.name), (X.refCol r.src r.name).getD [] ++
    ((Y.refCol r.src r.name).getD []).map (X.size r.tgt + ·))
  attrs := S.attrs.map fun a => ((a.src, a.name), (X.attrCol a.src a.name).getD [] ++
    (Y.attrCol a.src a.name).getD [])

/-- The entities of `X` in the sum. -/
def sumInl : FinHom := ⟨S.entities.map fun e => (e, List.range (X.size e))⟩

/-- The entities of `Y` in the sum, after those of `X`. -/
def sumInr : FinHom := ⟨S.entities.map fun e => (e, (List.range (Y.size e)).map (X.size e + ·))⟩

/-- The checks of the sum: it is a state, the two inclusions are homomorphisms, and
each entity type has the entities of `X`, then those of `Y`. -/
def checkSum : Bool :=
  (X.sum S Y).check S && (sumInl S X).check S X (X.sum S Y) &&
    (sumInr S X Y).check S Y (X.sum S Y) &&
    S.entities.all fun e => (X.sum S Y).size e == X.size e + Y.size e &&
      (sumInl S X).comp e == List.range (X.size e) &&
      (sumInr S X Y).comp e == (List.range (Y.size e)).map (X.size e + ·)

variable {S X Y}

theorem checkSum_check (h : checkSum S X Y = true) : (X.sum S Y).check S = true := by
  simp only [checkSum, Bool.and_eq_true] at h
  exact h.1.1.1

theorem checkSum_inl (h : checkSum S X Y = true) :
    (sumInl S X).check S X (X.sum S Y) = true := by
  simp only [checkSum, Bool.and_eq_true] at h
  exact h.1.1.2

theorem checkSum_inr (h : checkSum S X Y = true) :
    (sumInr S X Y).check S Y (X.sum S Y) = true := by
  simp only [checkSum, Bool.and_eq_true] at h
  exact h.1.2

omit [∀ v, DecidableEq (K v)] in
/-- An element at an entity type is an entity of that type. -/
theorem carrier_ent {e : String} {he : S.IsOb (.entity e)} (x : X.Carrier ⟨.entity e, he⟩) :
    ∃ (i : Nat) (hi : i < X.size e), x = ⟨.ent e i, ⟨rfl, hi⟩⟩ := by
  obtain ⟨x, hx⟩ := x
  cases x with
  | val => exact hx.elim
  | ent e₁ i =>
    obtain ⟨h₁, hi⟩ := hx
    cases h₁
    exact ⟨i, hi, rfl⟩

theorem getD_range {n i : Nat} (h : i < n) : (List.range n).getD i 0 = i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range h]

theorem getD_map_range {n m i : Nat} (h : i < n) :
    ((List.range n).map (m + ·)).getD i 0 = m + i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range h]

omit [∀ v, DecidableEq (K v)] in
theorem sumInl_mapElem {e : String} {i : Nat}
    (hcl : (sumInl S X).comp e = List.range (X.size e)) (hi : i < X.size e) :
    (sumInl S X).mapElem (K := K) (.ent e i) = .ent e i := by
  simp only [FinHom.mapElem, hcl, getD_range hi]

omit [∀ v, DecidableEq (K v)] in
theorem sumInr_mapElem {e : String} {i : Nat}
    (hcr : (sumInr S X Y).comp e = (List.range (Y.size e)).map (X.size e + ·))
    (hi : i < Y.size e) :
    (sumInr S X Y).mapElem (K := K) (.ent e i) = .ent e (X.size e + i) := by
  simp only [FinHom.mapElem, hcr, getD_map_range hi]

/-- The state of the sum is the coproduct of the two states. -/
noncomputable def sumIsColimit (hS : S.WellFormed) (hX : X.check S = true)
    (hY : Y.check S = true) (h : checkSum S X Y = true) :
    IsColimit (BinaryCofan.mk (FinHom.toHom hS hX (checkSum_check h) (checkSum_inl h))
      (FinHom.toHom hS hY (checkSum_check h) (checkSum_inr h))) := by
  refine State.isColimitOfEntities _ fun e he => ?_
  have hall := h
  simp only [checkSum, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hall
  obtain ⟨⟨hsize, hcl⟩, hcr⟩ := hall.2 e he
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm
    (Classical.choice ((Types.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩))
  · intro x x' hq
    obtain ⟨i, hi, rfl⟩ := carrier_ent x
    obtain ⟨j, hj, rfl⟩ := carrier_ent x'
    have hm : (sumInl S X).mapElem (K := K) (.ent e i) = (sumInl S X).mapElem (.ent e j) :=
      congrArg Subtype.val hq
    rw [sumInl_mapElem hcl hi, sumInl_mapElem hcl hj] at hm
    injection hm with _ hij
    subst hij
    rfl
  · intro x x' hq
    obtain ⟨i, hi, rfl⟩ := carrier_ent x
    obtain ⟨j, hj, rfl⟩ := carrier_ent x'
    have hm : (sumInr S X Y).mapElem (K := K) (.ent e i) = (sumInr S X Y).mapElem (.ent e j) :=
      congrArg Subtype.val hq
    rw [sumInr_mapElem hcr hi, sumInr_mapElem hcr hj] at hm
    injection hm with _ hij
    obtain rfl : i = j := by omega
    rfl
  · refine ⟨Set.disjoint_left.mpr ?_, codisjoint_iff.mpr (Set.eq_univ_of_forall ?_)⟩
    · rintro _ ⟨x, rfl⟩ ⟨x', hq⟩
      obtain ⟨i, hi, rfl⟩ := carrier_ent x
      obtain ⟨j, hj, rfl⟩ := carrier_ent x'
      have hm : (sumInr S X Y).mapElem (K := K) (.ent e j) = (sumInl S X).mapElem (.ent e i) :=
        congrArg Subtype.val hq
      rw [sumInr_mapElem hcr hj, sumInl_mapElem hcl hi] at hm
      injection hm with _ hij
      omega
    · intro z
      obtain ⟨c, hc, rfl⟩ := carrier_ent z
      rw [hsize] at hc
      by_cases hlt : c < X.size e
      · exact Or.inl ⟨⟨.ent e c, ⟨rfl, hlt⟩⟩, Subtype.ext (sumInl_mapElem hcl hlt)⟩
      · have hc' : c - X.size e < Y.size e := by omega
        refine Or.inr ⟨⟨.ent e (c - X.size e), ⟨rfl, hc'⟩⟩, Subtype.ext ?_⟩
        change (sumInr S X Y).mapElem (K := K) (.ent e (c - X.size e)) = .ent e c
        rw [sumInr_mapElem hcr hc']
        congr 1
        omega

/-- The merge of two finite states by the keys: when the closure of their sum is
`closed M h`, the state of `M` satisfies the keys, receives the two states, and is
their coproduct among the states that satisfy the keys. -/
theorem merge_closed (hS : S.WellFormed) (hX : X.check S = true) (hY : Y.check S = true)
    (hs : checkSum S X Y = true) {M : FinState K} {h : FinHom}
    (hc : (X.sum S Y).closure S = .closed M h) :
    ∃ (hM : M.check S = true) (i₁ : X.toState hX ⟶ M.toState hM)
      (i₂ : Y.toState hY ⟶ M.toState hM), (M.toState hM).Keys ∧
      ∀ {W : S.State K}, W.Keys → ∀ (a : X.toState hX ⟶ W) (b : Y.toState hY ⟶ W),
        ∃! m : M.toState hM ⟶ W, i₁ ≫ m = a ∧ i₂ ≫ m = b := by
  obtain ⟨hM, hcons, hkeys, ⟨iso⟩⟩ := closure_closed hS (checkSum_check hs) hc
  have hP := IsPushout.of_is_coproduct' (sumIsColimit hS hX hY hs) (State.initialIsInitial S K)
  refine ⟨hM, FinHom.toHom hS hX (checkSum_check hs) (checkSum_inl hs) ≫ State.unit hcons ≫ iso.hom,
    FinHom.toHom hS hY (checkSum_check hs) (checkSum_inr hs) ≫ State.unit hcons ≫ iso.hom,
    hkeys, ?_⟩
  intro W hW a b
  obtain ⟨m, ⟨hm₁, hm₂⟩, huniq⟩ := State.merge_existsUnique hP hcons hW a b
    ((State.initialIsInitial S K).hom_ext _ _)
  refine ⟨iso.inv ≫ m, ⟨?_, ?_⟩, fun m' hm' => ?_⟩
  · simpa using hm₁
  · simpa using hm₂
  · have := huniq (iso.hom ≫ m') ⟨by simpa using hm'.1, by simpa using hm'.2⟩
    rw [← this, Iso.inv_hom_id_assoc]

/-- When the closure of the sum fails, no state that satisfies the keys receives
the two states. -/
theorem merge_inconsistent (hS : S.WellFormed) (hX : X.check S = true) (hY : Y.check S = true)
    (hs : checkSum S X Y = true) {e n : String} {i j : Nat}
    (hc : (X.sum S Y).closure S = .inconsistent e n i j) {W : S.State K} (hW : W.Keys)
    (a : X.toState hX ⟶ W) (b : Y.toState hY ⟶ W) : False :=
  closure_inconsistent hS (checkSum_check hs) hc
    (State.consistent_of_isPushout
      (IsPushout.of_is_coproduct' (sumIsColimit hS hX hY hs) (State.initialIsInitial S K)) hW a b
      ((State.initialIsInitial S K).hom_ext _ _))

end FinState

end DDD
