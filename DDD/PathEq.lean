import DDD.Semantics

/-!
# Path equality

Decision procedures for `Schema.PathEq`: do two lists of names, out of the same
object, name paths that present the same morphism of `Schema.cat`?

- Free schemas, without equations: two paths present the same morphism of
  `Schema.cat` only if they are equal (`eq_of_mor_eq`), so `pathEqFree` compares
  the names (`pathEqFree_iff`).
- Acyclic schemas, in which no path has more generators than there are entity
  types (`Acyclic`, decided by `checkAcyclic`): there are finitely many paths,
  listed by `paths`. Two paths present the same morphism exactly when one turns
  into the other by a sequence of rewrites, each replacing one side of an
  equation by the other (`Rewrite`, `reflTransGen_of_mor_eq`,
  `Rewrite.exists_mor_eq`). `classOf` computes the class of a path in rounds of
  one rewrite until a round adds nothing, and `pathEqAcyclic` looks the second
  path up in it (`pathEqAcyclic_iff`).

`pathEqFree` and `pathEqAcyclic` are sound in every well-formed schema; the
hypotheses `eqns = []` and `Acyclic` are needed for the converse only. A schema
with both cycles and equations needs a rewriting system, supplied as a
certificate.
-/

namespace DDD

/-- The two ways to use an equation: left to right and right to left. -/
def Equation.sides (q : Equation) : List (List String × List String) :=
  [(q.lhs, q.rhs), (q.rhs, q.lhs)]

namespace Schema

open CategoryTheory

variable (S : Schema)

/-! ## Free schemas -/

/-- Path equality without equations: the two lists agree and name a path. -/
def pathEqFree (o : Ob) (l l' : List String) : Bool :=
  l == l' && (S.tgt? o l).isSome

variable {S}

theorem pathEqFree_sound (hS : S.WellFormed) (a : S.Obj) {l l' : List String}
    (h : S.pathEqFree a.1 l l' = true) : S.PathEq a l l' := by
  simp only [pathEqFree, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨rfl, o, ho⟩ := h
  obtain ⟨b, p, -, hp⟩ := exists_path hS a l ho
  exact ⟨b, p, p, hp, hp, rfl⟩

/-- Without equations, two paths present the same morphism only if they are equal. -/
theorem eq_of_mor_eq (hfree : S.eqns = []) {a b : S.Obj} {p q : Quiver.Path a b}
    (h : mor p = mor q) : p = q := by
  rw [mor_eq_iff] at h
  induction h with
  | rel _ _ h =>
    obtain ⟨_, _, _, _, ⟨_, hq, -⟩⟩ := h
    simp [hfree] at hq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem pathEqFree_complete (hfree : S.eqns = []) (a : S.Obj) {l l' : List String}
    (h : S.PathEq a l l') : S.pathEqFree a.1 l l' = true := by
  obtain ⟨b, p, q, rfl, rfl, h⟩ := h
  obtain rfl := eq_of_mor_eq hfree h
  simp [pathEqFree, tgt?_names]

theorem pathEqFree_iff (hS : S.WellFormed) (hfree : S.eqns = []) (a : S.Obj)
    (l l' : List String) : S.pathEqFree a.1 l l' = true ↔ S.PathEq a l l' :=
  ⟨pathEqFree_sound hS a, pathEqFree_complete hfree a⟩

/-! ## Enumerating paths -/

variable (S)

/-- The generators out of `o`, by name, with their targets. -/
def out : Ob → List (String × Ob)
  | .value _ => []
  | .entity e => (S.outNames e).filterMap fun n => (S.step? (.entity e) n).map (n, ·)

/-- The lists of names of the paths out of `o` with at most `k` generators. -/
def paths : Ob → Nat → List (List String)
  | _, 0 => [[]]
  | o, k + 1 => [] :: (S.out o).flatMap fun g => (paths g.2 k).map (g.1 :: ·)

variable {S}

theorem mem_out {o o' : Ob} {n : String} : (n, o') ∈ S.out o ↔ S.step? o n = some o' := by
  cases o with
  | value => simp [out, step?]
  | entity e =>
    simp only [out, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨n', -, o'', h, rfl, rfl⟩
      exact h
    · intro h
      refine ⟨n, ?_, o', h, rfl, rfl⟩
      simp only [step?] at h
      unfold outNames
      split at h
      · rename_i r hr
        unfold ref? at hr
        have hp := List.find?_some hr
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact List.mem_append_left _ (List.mem_map.mpr
          ⟨r, List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hr, by simp [hp.1]⟩, hp.2⟩)
      · obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.mp h
        unfold attr? at ht
        have hp := List.find?_some ht
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact List.mem_append_right _ (List.mem_map.mpr
          ⟨t, List.mem_filter.mpr ⟨List.mem_of_find?_eq_some ht, by simp [hp.1]⟩, hp.2⟩)

theorem mem_paths : ∀ (k : Nat) (o : Ob) (l : List String),
    l ∈ S.paths o k ↔ (S.tgt? o l).isSome ∧ l.length ≤ k
  | 0, o, l => by cases l <;> simp [paths]
  | k + 1, o, [] => by simp [paths]
  | k + 1, o, n :: ns => by
    simp only [paths, List.mem_cons, reduceCtorEq, false_or, List.mem_flatMap, List.mem_map,
      List.cons.injEq, Prod.exists, tgt?_cons, List.length_cons, Nat.add_le_add_iff_right]
    constructor
    · rintro ⟨n', o', hout, ns', hns', rfl, rfl⟩
      rw [mem_out] at hout
      rw [mem_paths k o' ns'] at hns'
      simp [hout, hns']
    · rintro ⟨h, hlen⟩
      cases hs : S.step? o n with
      | none => simp [hs] at h
      | some o' =>
        simp only [hs, Option.bind_some] at h
        exact ⟨n, o', mem_out.mpr hs, ns, (mem_paths k o' ns).mpr ⟨h, hlen⟩, rfl, rfl⟩

/-! ## Acyclic schemas -/

variable (S)

/-- Every path out of an object of `S` has at most as many generators as `S` has
entity types, so there are finitely many paths. A cycle of references gives paths
of every length; without one, a path passes each entity type at most once. -/
def Acyclic : Prop :=
  ∀ (a : S.Obj) (l : List String), (S.tgt? a.1 l).isSome → l.length ≤ S.entities.length

/-- The check for `Acyclic`: no path out of an entity type has one generator more
than there are entity types. -/
def checkAcyclic : Bool :=
  S.entities.all fun e => (S.paths (.entity e) (S.entities.length + 1)).all fun l =>
    decide (l.length ≤ S.entities.length)

variable {S}

theorem checkAcyclic_iff : S.checkAcyclic = true ↔ S.Acyclic := by
  simp only [checkAcyclic, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro h ⟨o, ho⟩ l hl
    by_contra hlen
    cases o with
    | value v => cases l <;> simp_all [step?]
    | entity e =>
      have hsplit := S.tgt?_append (.entity e) (l.take (S.entities.length + 1))
        (l.drop (S.entities.length + 1))
      rw [List.take_append_drop] at hsplit
      have htake : (S.tgt? (.entity e) (l.take (S.entities.length + 1))).isSome := by
        cases ht : S.tgt? (.entity e) (l.take (S.entities.length + 1)) <;> simp_all
      have := h e ho _ ((mem_paths _ _ _).mpr ⟨htake, List.length_take_le _ _⟩)
      rw [List.length_take] at this
      omega
  · intro h e he l hl
    exact h ⟨.entity e, he⟩ l ((mem_paths _ _ _).mp hl).1

instance : Decidable S.Acyclic := decidable_of_iff _ checkAcyclic_iff

/-! ## Rewriting -/

variable (S)

/-- `w'` is `w` with one side of an equation replaced by the other, at a position
where `w` has reached the source of the equation. -/
def Rewrite (o : Ob) (w w' : List String) : Prop :=
  ∃ q ∈ S.eqns, ∃ s ∈ q.sides, ∃ u v, S.tgt? o u = some (.entity q.src) ∧
    w = u ++ s.1 ++ v ∧ w' = u ++ s.2 ++ v

/-- The check for `Rewrite`. -/
def rewrite (o : Ob) (w w' : List String) : Bool :=
  (List.range (w.length + 1)).any fun i => S.eqns.any fun q => q.sides.any fun s =>
    S.tgt? o (w.take i) == some (.entity q.src) && s.1.isPrefixOf (w.drop i) &&
      w' == w.take i ++ s.2 ++ (w.drop i).drop s.1.length

variable {S}

theorem rewrite_iff (o : Ob) (w w' : List String) : S.rewrite o w w' = true ↔ S.Rewrite o w w' := by
  simp only [rewrite, Rewrite, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨i, -, q, hq, s, hs, ⟨hu, hpre⟩, rfl⟩
    refine ⟨q, hq, s, hs, w.take i, (w.drop i).drop s.1.length, hu, ?_, rfl⟩
    rw [List.append_assoc, List.prefix_iff_eq_append.mp hpre, List.take_append_drop]
  · rintro ⟨q, hq, s, hs, u, v, hu, rfl, rfl⟩
    refine ⟨u.length, by simp; omega, q, hq, s, hs, ?_⟩
    simp [List.append_assoc, hu]

theorem Rewrite.symm {o : Ob} {w w' : List String} (h : S.Rewrite o w w') : S.Rewrite o w' w := by
  obtain ⟨q, hq, s, hs, u, v, hu, rfl, rfl⟩ := h
  refine ⟨q, hq, (s.2, s.1), ?_, u, v, hu, rfl, rfl⟩
  simp only [Equation.sides, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with rfl | rfl <;> simp

/-- In a well-formed schema, rewriting the names of a path gives the names of a
path that presents the same morphism. -/
theorem Rewrite.exists_mor_eq (hS : S.WellFormed) {a b : S.Obj} {p : Quiver.Path a b}
    {w' : List String} (h : S.Rewrite a.1 (names p) w') :
    ∃ p' : Quiver.Path a b, names p' = w' ∧ mor p = mor p' := by
  obtain ⟨q, hq, s, hs, u, v, hu, hw, rfl⟩ := h
  obtain ⟨x, p₁, p₂₃, rfl, h₁, h₂₃⟩ := exists_split p u (s.1 ++ v) (by rw [hw, List.append_assoc])
  obtain ⟨y, p₂, p₃, rfl, h₂, h₃⟩ := exists_split p₂₃ s.1 v h₂₃
  have hx : x.1 = .entity q.src := Option.some.inj ((tgt?_names p₁).symm.trans (h₁ ▸ hu))
  have hy : S.tgt? x.1 s.1 = some y.1 := h₂ ▸ tgt?_names p₂
  obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
  simp only [Equation.sides, List.mem_cons, List.not_mem_nil, or_false] at hs
  have hs₂ : S.tgt? x.1 s.2 = some y.1 := by
    rw [hx] at hy ⊢
    rcases hs with rfl | rfl
    · rw [hl] at hy; rw [hr, hy]
    · rw [hr] at hy; rw [hl, hy]
  obtain ⟨y', p₂', hy', h₂'⟩ := exists_path hS x s.2 hs₂
  obtain rfl : y = y' := Subtype.ext hy'.symm
  have hrel : mor p₂ = mor p₂' := by
    rcases hs with rfl | rfl
    · exact CategoryTheory.Quotient.sound _ ⟨q, hq, hx, h₂, h₂'⟩
    · exact (CategoryTheory.Quotient.sound _ ⟨q, hq, hx, h₂', h₂⟩).symm
  refine ⟨p₁.comp (p₂'.comp p₃), by simp [h₁, h₂', h₃], ?_⟩
  simp only [mor_comp, hrel]

/-- One step of the congruence generated by the equations is a rewrite. -/
theorem rewrite_of_compClosure {a b : S.Obj} {p q : Quiver.Path a b}
    (h : Quotient.CompClosure S.rel (s := a) (t := b) p q) :
    S.Rewrite a.1 (names p) (names q) := by
  obtain ⟨f, m₁, m₂, g, ⟨e, he, hsrc, h₁, h₂⟩⟩ := h
  refine ⟨e, he, (e.lhs, e.rhs), by simp [Equation.sides], names f, names g, ?_, ?_, ?_⟩
  · rw [← hsrc]
    exact tgt?_names f
  · simp [h₁]
  · simp [h₂]

/-- Two paths that present the same morphism rewrite into each other. -/
theorem reflTransGen_of_mor_eq {a b : S.Obj} {p q : Quiver.Path a b} (h : mor p = mor q) :
    Relation.ReflTransGen (S.Rewrite a.1) (names p) (names q) := by
  rw [mor_eq_iff] at h
  induction h with
  | rel _ _ h => exact .single (rewrite_of_compClosure h)
  | refl => exact .refl
  | symm _ _ _ ih =>
    exact Relation.ReflTransGen.symmetric (fun _ _ h => Rewrite.symm h) ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The class of a path -/

variable (S)

/-- One round: the lists in `P` that are in `C` or one rewrite away from a list in
`C`. -/
def grow (o : Ob) (P C : List (List String)) : List (List String) :=
  P.filter fun w => decide (w ∈ C) || C.any fun w' => S.rewrite o w' w

/-- Rounds of `grow`, at most `k`, until a round adds nothing. -/
def close (o : Ob) (P : List (List String)) : Nat → List (List String) → List (List String)
  | 0, C => C
  | k + 1, C => if (S.grow o P C).length = C.length then C else close o P k (S.grow o P C)

/-- The paths out of `o`, with at most as many generators as there are entity types,
that rewrite into `l`. -/
def classOf (o : Ob) (l : List String) : List (List String) :=
  S.close o (S.paths o S.entities.length) ((S.paths o S.entities.length).length + 1)
    ((S.paths o S.entities.length).filter fun w => decide (w = l))

/-- Path equality in an acyclic schema: `l'` is in the class of `l`. -/
def pathEqAcyclic (o : Ob) (l l' : List String) : Bool :=
  decide (l' ∈ S.classOf o l)

variable {S}

theorem grow_subset {o : Ob} {P C : List (List String)} : ∀ w ∈ S.grow o P C, w ∈ P :=
  fun _ hw => (List.mem_filter.mp hw).1

theorem close_subset {o : Ob} {P : List (List String)} :
    ∀ (k : Nat) (C : List (List String)), (∀ w ∈ C, w ∈ P) → ∀ w ∈ S.close o P k C, w ∈ P
  | 0, _, hC => hC
  | k + 1, C, hC => by
    unfold close
    split
    · exact hC
    · exact close_subset k _ grow_subset

theorem subset_close {o : Ob} {P : List (List String)} :
    ∀ (k : Nat) (C : List (List String)), (∀ w ∈ C, w ∈ P) → ∀ w ∈ C, w ∈ S.close o P k C
  | 0, _, _ => fun _ h => h
  | k + 1, C, hC => by
    unfold close
    split
    · exact fun _ h => h
    · intro w hw
      exact subset_close k _ grow_subset w
        (List.mem_filter.mpr ⟨hC w hw, by simp [hw]⟩)

/-- A property of lists that rewriting preserves holds on the whole closure. -/
theorem close_induction {o : Ob} {P : List (List String)} (Q : List String → Prop)
    (hQ : ∀ w w', Q w → S.Rewrite o w w' → Q w') :
    ∀ (k : Nat) (C : List (List String)), (∀ w ∈ C, Q w) → ∀ w ∈ S.close o P k C, Q w
  | 0, _, hC => hC
  | k + 1, C, hC => by
    unfold close
    split
    · exact hC
    · refine close_induction Q hQ k _ fun w hw => ?_
      simp only [grow, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
        rewrite_iff] at hw
      rcases hw.2 with h | ⟨w', hw', h⟩
      · exact hC w h
      · exact hQ w' w (hC w' hw') h

/-- If `p` implies `q` on `l` and both hold equally often, `q` implies `p` on `l`. -/
theorem countP_eq_imp {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x → q x) → l.countP p = l.countP q → ∀ x ∈ l, q x → p x
  | [], _, _ => by simp
  | x :: l, himp, hcount => by
    have hmono : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun y hy => himp y (List.mem_cons_of_mem _ hy)
    simp only [List.countP_cons] at hcount
    have hl : l.countP p = l.countP q := by
      by_cases hpx : p x <;> by_cases hqx : q x <;> simp_all
    intro y hy hqy
    rcases List.mem_cons.mp hy with rfl | hy
    · by_contra hpy
      simp [hpy, hqy] at hcount
      omega
    · exact countP_eq_imp (fun z hz => himp z (List.mem_cons_of_mem _ hz)) hl y hy hqy

/-- With enough rounds, the closure is closed under rewriting inside `P`. -/
theorem close_closed {o : Ob} {P : List (List String)} :
    ∀ (k : Nat) (C : List (List String)), C = P.filter (fun w => decide (w ∈ C)) →
      P.length + 1 ≤ k + C.length →
      ∀ w ∈ S.close o P k C, ∀ w' ∈ P, S.Rewrite o w w' → w' ∈ S.close o P k C
  | 0, C, hC, hk => by
    have : C.length ≤ P.length := hC ▸ List.length_filter_le _ _
    omega
  | k + 1, C, hC, hk => by
    have hlenC : C.length = P.countP (fun w => decide (w ∈ C)) := by
      rw [List.countP_eq_length_filter]
      exact congrArg List.length hC
    have hlenG : (S.grow o P C).length =
        P.countP (fun w => decide (w ∈ C) || C.any fun w' => S.rewrite o w' w) := by
      rw [List.countP_eq_length_filter]
      rfl
    have hmono : ∀ w ∈ P, decide (w ∈ C) = true →
        (decide (w ∈ C) || C.any fun w' => S.rewrite o w' w) = true := by
      intro w _ h
      simp [h]
    by_cases hc : (S.grow o P C).length = C.length
    · simp only [close, hc, if_true]
      intro w hw w' hw' hr
      have hback := countP_eq_imp hmono (by rw [← hlenC, ← hlenG, hc]) w' hw' (by
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨w, hw, (rewrite_iff _ _ _).mpr hr⟩)
      simpa using hback
    · simp only [close, hc, if_false]
      apply close_closed k
      · change P.filter _ = P.filter _
        refine List.filter_congr fun w hw => ?_
        simp only [grow, List.mem_filter, hw, true_and, Bool.decide_eq_true]
      · have := List.countP_mono_left hmono
        omega

theorem pathEqAcyclic_sound (hS : S.WellFormed) (a : S.Obj) {l l' : List String}
    (h : S.pathEqAcyclic a.1 l l' = true) : S.PathEq a l l' := by
  simp only [pathEqAcyclic, classOf, decide_eq_true_eq] at h
  refine close_induction (S.PathEq a l) ?_ _ _ ?_ l' h
  · rintro w w' ⟨b, p, q, hp, rfl, hpq⟩ hr
    obtain ⟨q', hq', hqq'⟩ := Rewrite.exists_mor_eq hS hr
    exact ⟨b, p, q', hp, hq', hpq.trans hqq'⟩
  · intro w hw
    obtain ⟨hwP, hwl⟩ := List.mem_filter.mp hw
    obtain rfl : w = l := by simpa using hwl
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ((mem_paths _ _ _).mp hwP).1
    obtain ⟨b, p, -, hp⟩ := exists_path hS a w ho
    exact ⟨b, p, p, hp, hp, rfl⟩

theorem pathEqAcyclic_complete (hS : S.WellFormed) (hA : S.Acyclic) (a : S.Obj)
    {l l' : List String} (h : S.PathEq a l l') : S.pathEqAcyclic a.1 l l' = true := by
  obtain ⟨b, p, q, rfl, rfl, h⟩ := h
  simp only [pathEqAcyclic, classOf, decide_eq_true_eq]
  generalize hPdef : S.paths a.1 S.entities.length = P
  have hP : ∀ {w : List String}, (S.tgt? a.1 w).isSome → w ∈ P := fun hw =>
    hPdef ▸ (mem_paths _ _ _).mpr ⟨hw, hA a _ hw⟩
  generalize hC₀def : P.filter (fun w => decide (w = names p)) = C₀
  have hC₀P : ∀ w ∈ C₀, w ∈ P := fun w hw => (List.mem_filter.mp (hC₀def ▸ hw)).1
  have hpC₀ : names p ∈ C₀ := hC₀def ▸ List.mem_filter.mpr ⟨hP (by simp [tgt?_names]), by simp⟩
  have hC₀ : C₀ = P.filter (fun w => decide (w ∈ C₀)) := by
    subst hC₀def
    refine List.filter_congr fun w hw => ?_
    simp [List.mem_filter, hw]
  have hclosed := close_closed (S := S) (o := a.1) (P.length + 1) C₀ hC₀ (by omega)
  have hsub := close_subset (S := S) (o := a.1) (P.length + 1) C₀ hC₀P
  have hr := reflTransGen_of_mor_eq h
  generalize names q = w at hr ⊢
  induction hr with
  | refl => exact subset_close _ _ hC₀P _ hpC₀
  | tail _ hr ih =>
    refine hclosed _ ih _ ?_ hr
    have hw := hsub _ ih
    rw [← hPdef] at hw
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ((mem_paths _ _ _).mp hw).1
    obtain ⟨c, pw, -, rfl⟩ := exists_path hS a _ ho
    obtain ⟨pw', rfl, -⟩ := Rewrite.exists_mor_eq hS hr
    exact hP (by simp [tgt?_names])

theorem pathEqAcyclic_iff (hS : S.WellFormed) (hA : S.Acyclic) (a : S.Obj)
    (l l' : List String) : S.pathEqAcyclic a.1 l l' = true ↔ S.PathEq a l l' :=
  ⟨pathEqAcyclic_sound hS a, pathEqAcyclic_complete hS hA a⟩

end Schema

end DDD
