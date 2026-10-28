import DDD.Compose
import DDD.States

/-!
# Finite states as data

A finite state in the shape of an acset (`FinState`): for each entity type a
number of entities, numbered from 0; for each reference a column with the number
of the target of each entity; for each attribute a column with the value of each
entity. Columns are found by the source entity type and the name of their
generator.

- `FinState.check S X`: every reference and attribute of `S` has a column of the
  right length, references point to existing entities, attribute values have
  the declared value type, and every equation of `S` holds at every entity.
- `FinState.toState`: a finite state that passes the check is a state of `S`
  with values in `K` (`Schema.State K S`). Its set at an entity type `e` is the
  elements `Elem.ent e i` with `i` below the number of entities, and at a value
  type `v` the values `Elem.val v k`.
- `FinState.eval_lift`: following the names of a path through the columns is
  applying the state to the path.
- Value objects: `checkValueObjects` is sound for `Schema.State.ValueObjects`,
  the condition that two entities of a value object with equal attribute values
  are equal (`toState_valueObjects`).
- Homomorphisms: `FinHom` gives, for each entity type, the image of each entity.
  `FinHom.check` asks that it commute with every generator; a homomorphism that
  passes is a morphism of states (`FinHom.toHom`).
- Restriction: `FinState.restrict T S S' X` computes `Δ_T X` on data, following
  the image path of each generator. It passes the check (`restrict_check`), and
  its state is isomorphic to `Translation.restrictState` applied to the state of
  `X` (`restrictIso`).
-/

namespace DDD

open CategoryTheory

/-- An element of a finite state: entity number `i` of the entity type `e`, or a
value. -/
inductive Elem (K : ValueType → Type) where
  | ent (e : String) (i : Nat)
  | val (v : ValueType) (k : K v)

variable {K : ValueType → Type}

instance [∀ v, DecidableEq (K v)] : DecidableEq (Elem K)
  | .ent e i, .ent e' i' =>
    if h : e = e' ∧ i = i' then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else isFalse (by intro h'; cases h'; exact h ⟨rfl, rfl⟩)
  | .val v k, .val v' k' =>
    if h : v = v' then by
      subst h
      exact if hk : k = k' then isTrue (by rw [hk])
        else isFalse (by intro h'; cases h'; exact hk rfl)
    else isFalse (by intro h'; cases h'; exact h rfl)
  | .ent .., .val .. => isFalse (by intro h; cases h)
  | .val .., .ent .. => isFalse (by intro h; cases h)

/-- A finite state as data: the number of entities of each entity type, the column
of each reference (the number of the target of each entity), and the column of
each attribute (the value of each entity). -/
structure FinState (K : ValueType → Type) where
  sizes : List (String × Nat)
  refs : List ((String × String) × List Nat)
  attrs : List ((String × String) × List (Σ v, K v))

namespace FinState

variable (X : FinState K)

/-- The number of entities of the entity type `e`. -/
def size (e : String) : Nat := (X.sizes.lookup e).getD 0

/-- The column of the reference named `n` out of `e`. -/
def refCol (e n : String) : Option (List Nat) := X.refs.lookup (e, n)

/-- The column of the attribute named `n` out of `e`. -/
def attrCol (e n : String) : Option (List (Σ v, K v)) := X.attrs.lookup (e, n)

/-- One step along the generator named `n` of `S`. -/
def step (S : Schema) : Elem K → String → Option (Elem K)
  | .ent e i, n =>
    match S.ref? e n with
    | some r => ((X.refCol e n).bind (·[i]?)).map (.ent r.tgt)
    | none =>
      match S.attr? e n with
      | some _ => ((X.attrCol e n).bind (·[i]?)).map fun x => .val x.1 x.2
      | none => none
  | .val _ _, _ => none

/-- Following a list of generator names. -/
def eval (S : Schema) : Elem K → List String → Option (Elem K)
  | x, [] => some x
  | x, n :: ns => (X.step S x n).bind fun y => eval S y ns

theorem eval_append (S : Schema) (x : Elem K) (l m : List String) :
    X.eval S x (l ++ m) = (X.eval S x l).bind fun y => X.eval S y m := by
  induction l generalizing x with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.cons_append, eval]
    cases X.step S x n with
    | none => rfl
    | some y => exact ih y

theorem eval_singleton (S : Schema) (x : Elem K) (n : String) :
    X.eval S x [n] = X.step S x n := by
  simp only [eval]
  cases X.step S x n <;> rfl

variable [∀ v, DecidableEq (K v)]

/-- The check that `X` is a state of `S`: columns of the right length for every
generator, references to existing entities, values of the declared value types,
and every equation of `S` at every entity of its source. -/
def check (S : Schema) : Bool :=
  S.refs.all (fun r => match X.refCol r.src r.name with
    | some c => c.length == X.size r.src && c.all (· < X.size r.tgt)
    | none => false) &&
  S.attrs.all (fun a => match X.attrCol a.src a.name with
    | some c => c.length == X.size a.src && c.all (·.1 == a.tgt)
    | none => false) &&
  S.eqns.all fun q => (List.range (X.size q.src)).all fun i =>
    decide (X.eval S (.ent q.src i) q.lhs = X.eval S (.ent q.src i) q.rhs)

variable {X} {S : Schema}

theorem check_ref (h : X.check S = true) {r : Ref} (hr : r ∈ S.refs) :
    ∃ c, X.refCol r.src r.name = some c ∧ c.length = X.size r.src ∧
      ∀ j ∈ c, j < X.size r.tgt := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.1 r hr
  split at this
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨c, hc, this⟩
  · exact absurd this (by simp)

theorem check_attr (h : X.check S = true) {a : Attr} (ha : a ∈ S.attrs) :
    ∃ c, X.attrCol a.src a.name = some c ∧ c.length = X.size a.src ∧ ∀ x ∈ c, x.1 = a.tgt := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 a ha
  split at this
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
    exact ⟨c, hc, this⟩
  · exact absurd this (by simp)

theorem check_eqn (h : X.check S = true) {q : Equation} (hq : q ∈ S.eqns) {i : Nat}
    (hi : i < X.size q.src) :
    X.eval S (.ent q.src i) q.lhs = X.eval S (.ent q.src i) q.rhs := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.2 q hq i hi

variable (X) in
/-- `x` is an element of `X` at the object `o`. -/
def Has : Elem K → Ob → Prop
  | .ent e i, .entity e' => e = e' ∧ i < X.size e'
  | .val v _, .value w => v = w
  | _, _ => False

theorem ref?_spec {e n : String} {r : Ref} (h : S.ref? e n = some r) :
    r ∈ S.refs ∧ r.src = e ∧ r.name = n := by
  unfold Schema.ref? at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

theorem attr?_spec {e n : String} {a : Attr} (h : S.attr? e n = some a) :
    a ∈ S.attrs ∧ a.src = e ∧ a.name = n := by
  unfold Schema.attr? at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- A step along a generator from an element at its source gives an element at its
target. -/
theorem step_has (hX : X.check S = true) {x : Elem K} {o o' : Ob} {n : String}
    (hx : X.Has x o) (h : S.step? o n = some o') :
    ∃ y, X.step S x n = some y ∧ X.Has y o' := by
  cases o with
  | value => simp [Schema.step?] at h
  | entity e =>
    cases x with
    | val => exact absurd hx (by simp [Has])
    | ent e₀ i =>
      obtain ⟨rfl, hi⟩ := hx
      simp only [Schema.step?] at h
      cases hr : S.ref? e₀ n with
      | some r =>
        rw [hr] at h
        cases h
        obtain ⟨hrm, hrs, hrn⟩ := ref?_spec hr
        obtain ⟨c, hc, hlen, hlt⟩ := check_ref hX hrm
        rw [hrs, hrn] at hc
        have hi' : i < c.length := hlen ▸ hrs ▸ hi
        refine ⟨.ent r.tgt c[i], ?_, rfl, hlt _ (List.getElem_mem hi')⟩
        simp [step, hr, hc, List.getElem?_eq_getElem hi']
      | none =>
        rw [hr] at h
        cases ha : S.attr? e₀ n with
        | none => simp [ha] at h
        | some a =>
          rw [ha] at h
          cases h
          obtain ⟨ham, has, han⟩ := attr?_spec ha
          obtain ⟨c, hc, hlen, hty⟩ := check_attr hX ham
          rw [has, han] at hc
          have hi' : i < c.length := hlen ▸ has ▸ hi
          refine ⟨.val c[i].1 c[i].2, ?_, hty _ (List.getElem_mem hi')⟩
          simp [step, hr, ha, hc, List.getElem?_eq_getElem hi']

/-- Following a path of `S` from an element at its source gives an element at its
target. -/
theorem eval_has (hX : X.check S = true) :
    ∀ {x : Elem K} {o o' : Ob} {l : List String}, X.Has x o → S.tgt? o l = some o' →
      ∃ y, X.eval S x l = some y ∧ X.Has y o'
  | x, _, _, [], hx, h => ⟨x, rfl, Option.some.inj h ▸ hx⟩
  | x, o, o', n :: ns, hx, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o₁ =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      obtain ⟨y, hy, hy'⟩ := step_has hX hx hs
      obtain ⟨z, hz, hz'⟩ := eval_has hX hy' h
      exact ⟨z, by simp [eval, hy, hz], hz'⟩

/-! ## The state -/

variable (X) in
/-- The elements of `X` at the object `a`. -/
abbrev Carrier (a : S.Obj) : Type := { x : Elem K // X.Has x a.1 }

/-- The step along a generator, between carriers. -/
def stepIn (hX : X.check S = true) {o o' : Ob} {n : String} (h : S.step? o n = some o')
    (x : { x : Elem K // X.Has x o }) : { y : Elem K // X.Has y o' } :=
  match hs : X.step S x.1 n with
  | some y => ⟨y, by
      obtain ⟨y', hy', hy''⟩ := step_has hX x.2 h
      rw [hs] at hy'
      cases hy'
      exact hy''⟩
  | none => absurd hs (by
      obtain ⟨y', hy', -⟩ := step_has hX x.2 h
      rw [hy']
      simp)

theorem step_stepIn (hX : X.check S = true) {o o' : Ob} {n : String}
    (h : S.step? o n = some o') (x : { x : Elem K // X.Has x o }) :
    X.step S x.1 n = some (stepIn hX h x).1 := by
  unfold stepIn
  split
  · rename_i y hy
    exact hy
  · rename_i hn
    obtain ⟨y', hy', -⟩ := step_has hX x.2 h
    rw [hn] at hy'
    cases hy'

variable (X) in
/-- The prefunctor of the state: each generator to its step. -/
def prefunctor (hX : X.check S = true) : S.Obj ⥤q Type where
  obj a := X.Carrier a
  map e := stepIn hX e.2

/-- Applying the state to a path is following its names. -/
theorem eval_lift (hX : X.check S = true) {a b : S.Obj} (p : Quiver.Path a b)
    (x : X.Carrier a) :
    X.eval S x.1 (Schema.names p) = some ((Paths.lift (X.prefunctor hX)).map p x).1 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Schema.names_cons, eval_append, ih, Option.bind_some, eval_singleton, Paths.lift_cons,
      types_comp_apply]
    exact step_stepIn hX e.2 _

variable (X) in
/-- The functor of a finite state that passes the check. -/
def functor (hX : X.check S = true) : S.cat ⥤ Type :=
  CategoryTheory.Quotient.lift S.rel (Paths.lift (X.prefunctor hX)) (by
    rintro a b f g ⟨q, hq, ha, hf, hg⟩
    funext x
    apply Subtype.ext
    have h₁ := eval_lift hX f x
    have h₂ := eval_lift hX g x
    rw [hf] at h₁
    rw [hg] at h₂
    obtain ⟨x, hx⟩ := x
    obtain ⟨o, ho⟩ := a
    simp only at ha
    subst ha
    cases x with
    | val => exact absurd hx (by simp [Has])
    | ent e i =>
      obtain ⟨rfl, hi⟩ := hx
      rw [check_eqn hX hq hi] at h₁
      exact Option.some.inj (h₁.symm.trans h₂))

theorem functor_obj (hX : X.check S = true) (a : S.Obj) :
    (X.functor hX).obj (S.obj a) = X.Carrier a := rfl

/-- Applying the functor to the morphism of a path is following its names. -/
theorem eval_map (hX : X.check S = true) {a b : S.Obj} (p : Quiver.Path a b)
    (x : X.Carrier a) :
    X.eval S x.1 (Schema.names p) = some ((X.functor hX).map (Schema.mor p) x).1 :=
  eval_lift hX p x

variable (X) in
/-- The values of `X` at the value type `v` are the values of `K v`. -/
def valueEquiv (v : ValueType) : X.Carrier (S := S) ⟨.value v, trivial⟩ ≃ K v where
  toFun x := match x with
    | ⟨.val w k, h⟩ => cast (congrArg K h) k
    | ⟨.ent _ _, h⟩ => False.elim h
  invFun k := ⟨.val v k, rfl⟩
  left_inv := by
    rintro ⟨x, h⟩
    cases x with
    | ent => exact h.elim
    | val w k =>
      change w = v at h
      subst h
      rfl
  right_inv _ := rfl

variable (X) in
/-- A finite state that passes the check, as a state of `S` with values in `K`. -/
def toState (hX : X.check S = true) : S.State K where
  F := X.functor hX
  values v := X.valueEquiv v

theorem toState_values (hX : X.check S = true) (v : ValueType) (k : K v) :
    (X.toState hX).values v ⟨.val v k, rfl⟩ = k := rfl

/-- On the morphism of a generator, the state is the step. -/
theorem functor_map_genMor (hX : X.check S = true) {a b : S.Obj} (n : String)
    (h : S.step? a.1 n = some b.1) (x : X.Carrier a) :
    (X.functor hX).map (S.genMor n h) x = stepIn hX h x := rfl

/-! ## Value objects -/

variable (S X) in
/-- Two entities of a value object with equal attribute values are equal. -/
def checkValueObjects : Bool :=
  S.valueObjects.all fun e => (List.range (X.size e)).all fun i =>
    (List.range (X.size e)).all fun j => i == j || !(S.attrs.all fun a =>
      a.src != e || decide ((X.attrCol a.src a.name).bind (·[i]?) =
        (X.attrCol a.src a.name).bind (·[j]?)))

end FinState

/-- An attribute is a generator out of its source entity type. -/
theorem Schema.step?_attr {S : Schema} (hS : S.WellFormed) {a : Attr} (ha : a ∈ S.attrs)
    {e : String} (hae : a.src = e) : S.step? (.entity e) a.name = some (.value a.tgt) :=
  hae ▸ Schema.step?_of_mem_attrs hS ha

/-- The value-object condition on a state: two entities of a value object whose
attributes have equal values are equal. -/
def Schema.State.ValueObjects {S : Schema} (hS : S.WellFormed) (Y : S.State K) : Prop :=
  ∀ e (he : e ∈ S.entities), e ∈ S.valueObjects → ∀ x y : Y.F.obj (S.obj ⟨.entity e, he⟩),
    (∀ a (ha : a ∈ S.attrs) (hae : a.src = e),
      Y.values a.tgt (Y.F.map (S.genMor (a := ⟨.entity e, he⟩) (b := ⟨.value a.tgt, trivial⟩)
        a.name (Schema.step?_attr hS ha hae)) x) =
      Y.values a.tgt (Y.F.map (S.genMor (a := ⟨.entity e, he⟩) (b := ⟨.value a.tgt, trivial⟩)
        a.name (Schema.step?_attr hS ha hae)) y)) → x = y

namespace FinState

variable {X : FinState K} {S : Schema}

/-- The step along an attribute from entity `i` reads the column of the attribute. -/
theorem step_attr (hS : S.WellFormed) {a : Attr} (ha : a ∈ S.attrs) (i : Nat) :
    X.step S (.ent a.src i) a.name =
      ((X.attrCol a.src a.name).bind (·[i]?)).map fun x => .val x.1 x.2 := by
  have hs := Schema.step?_of_mem_attrs hS ha
  simp only [Schema.step?] at hs
  cases hr : S.ref? a.src a.name with
  | some r => simp [hr] at hs
  | none =>
    rw [hr] at hs
    cases hat : S.attr? a.src a.name with
    | none => simp [hat] at hs
    | some a' => simp [step, hr, hat]

variable [∀ v, DecidableEq (K v)]

/-- The value of an attribute at entity `i` is the entry `i` of its column. -/
theorem values_attr (hS : S.WellFormed) (hX : X.check S = true) {a : Attr} (ha : a ∈ S.attrs)
    {e : String} (hae : a.src = e) (he : e ∈ S.entities) {i : Nat} (hi : i < X.size e)
    {c : List (Σ v, K v)} (hc : X.attrCol a.src a.name = some c) (hi' : i < c.length) :
    ∃ h : c[i].1 = a.tgt, (X.toState hX).values a.tgt ((X.functor hX).map
      (S.genMor (a := ⟨.entity e, he⟩) (b := ⟨.value a.tgt, trivial⟩) a.name
        (Schema.step?_attr hS ha hae)) ⟨.ent e i, ⟨rfl, hi⟩⟩) = cast (congrArg K h) c[i].2 := by
  subst hae
  rw [functor_map_genMor]
  have sz := step_stepIn hX (Schema.step?_attr hS ha rfl)
    (⟨.ent a.src i, ⟨rfl, hi⟩⟩ : { x : Elem K // X.Has x (.entity a.src) })
  rw [step_attr hS ha, hc, Option.bind_some, List.getElem?_eq_getElem hi', Option.map_some,
    Option.some.injEq] at sz
  generalize stepIn hX (Schema.step?_attr hS ha rfl) _ = z at sz ⊢
  obtain ⟨z, hz⟩ := z
  subst sz
  exact ⟨hz, rfl⟩

/-- The value-object check is sound. -/
theorem toState_valueObjects (hS : S.WellFormed) (hX : X.check S = true)
    (hv : X.checkValueObjects S = true) : (X.toState hX).ValueObjects hS := by
  intro e he hvo x y hxy
  obtain ⟨⟨e₁, i⟩ | ⟨_, _⟩, hx⟩ := x
  swap
  · exact hx.elim
  obtain ⟨⟨e₂, j⟩ | ⟨_, _⟩, hy⟩ := y
  swap
  · exact hy.elim
  obtain ⟨h₁, hi⟩ := hx
  obtain ⟨h₂, hj⟩ := hy
  subst e₁ e₂
  simp only [checkValueObjects, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hv
  rcases hv e hvo i hi j hj with rfl | hne
  · rfl
  exfalso
  have hall : (S.attrs.all fun a => a.src != e ||
      decide ((X.attrCol a.src a.name).bind (·[i]?) =
        (X.attrCol a.src a.name).bind (·[j]?))) = true := by
    simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    intro a ha
    by_cases hae : a.src = e
    · right
      obtain ⟨c, hc, hlen, -⟩ := check_attr hX ha
      have hi' : i < c.length := by rw [hlen, hae]; exact hi
      have hj' : j < c.length := by rw [hlen, hae]; exact hj
      obtain ⟨h₁, v₁⟩ := values_attr hS hX ha hae he hi hc hi'
      obtain ⟨h₂, v₂⟩ := values_attr hS hX ha hae he hj hc hj'
      have hxa := v₁.symm.trans ((hxy a ha hae).trans v₂)
      rw [hc, Option.bind_some, Option.bind_some, List.getElem?_eq_getElem hi',
        List.getElem?_eq_getElem hj']
      congr 1
      exact Sigma.ext (h₁.trans h₂.symm)
        (((cast_heq _ _).symm.trans (heq_of_eq hxa)).trans (cast_heq _ _))
    · left
      exact hae
  rw [hall] at hne
  exact absurd hne (by simp)


/-! ## Homomorphisms -/

end FinState

/-- A homomorphism between finite states, as data: for each entity type, the
number of the image of each entity. -/
structure FinHom where
  comps : List (String × List Nat)

namespace FinHom

variable (h : FinHom)

/-- The component at the entity type `e`. -/
def comp (e : String) : List Nat := (h.comps.lookup e).getD []

/-- The image of an element: entities by their component, values unchanged. -/
def mapElem : Elem K → Elem K
  | .ent e i => .ent e ((h.comp e).getD i 0)
  | .val v k => .val v k

variable [∀ v, DecidableEq (K v)]

/-- The check that `h` is a homomorphism from `X` to `Y`: components of the right
length into existing entities, commuting with every reference and attribute. -/
def check (S : Schema) (X Y : FinState K) : Bool :=
  S.entities.all (fun e => (h.comp e).length == X.size e && (h.comp e).all (· < Y.size e)) &&
  S.refs.all (fun r => (List.range (X.size r.src)).all fun i =>
    decide (Y.step S (h.mapElem (.ent r.src i)) r.name =
      (X.step S (.ent r.src i) r.name).map h.mapElem)) &&
  S.attrs.all (fun a => (List.range (X.size a.src)).all fun i =>
    decide (Y.step S (h.mapElem (.ent a.src i)) a.name =
      (X.step S (.ent a.src i) a.name).map h.mapElem))

variable {h} {S : Schema} {X Y : FinState K}

theorem mapElem_has (hc : h.check S X Y = true) {x : Elem K} {o : Ob} (ho : S.IsOb o)
    (hx : X.Has x o) : Y.Has (h.mapElem x) o := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  cases o with
  | value => cases x with
    | ent => exact hx.elim
    | val => exact hx
  | entity e => cases x with
    | val => exact hx.elim
    | ent e₀ i =>
      obtain ⟨rfl, hi⟩ := hx
      obtain ⟨hlen, hlt⟩ := hc.1.1 e₀ ho
      refine ⟨rfl, ?_⟩
      change (h.comp e₀).getD i 0 < Y.size e₀
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some]
      exact hlt _ (List.getElem_mem _)

theorem step_mapElem (hc : h.check S X Y = true) {x : Elem K} {o o' : Ob} {n : String}
    (ho : S.IsOb o) (hx : X.Has x o) (hs : S.step? o n = some o') :
    Y.step S (h.mapElem x) n = (X.step S x n).map h.mapElem := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨e, rfl, hg⟩ := Schema.exists_gen_of_step? hs
  cases x with
  | val => exact hx.elim
  | ent e₀ i =>
    obtain ⟨rfl, hi⟩ := hx
    rcases hg with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · exact hc.1.2 r hr i hi
    · exact hc.2 a ha i hi

theorem eval_mapElem (hS : S.WellFormed) (hX : X.check S = true) (hc : h.check S X Y = true) :
    ∀ {x : Elem K} {o o' : Ob} {l : List String}, S.IsOb o → X.Has x o →
      S.tgt? o l = some o' → Y.eval S (h.mapElem x) l = (X.eval S x l).map h.mapElem
  | _, _, _, [], _, _, _ => rfl
  | x, o, o', n :: ns, ho, hx, hl => by
    cases hs : S.step? o n with
    | none => simp [hs] at hl
    | some o₁ =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at hl
      obtain ⟨y, hy, hy'⟩ := FinState.step_has hX hx hs
      have ih := eval_mapElem hS hX hc (Schema.isOb_of_step? hS hs) hy' hl
      simp only [FinState.eval, step_mapElem hc ho hx hs, hy, Option.map_some, Option.bind_some,
        ih]

/-- A homomorphism of finite states that passes the check is a morphism of their
states. -/
def toHom (hS : S.WellFormed) (hX : X.check S = true) (hY : Y.check S = true)
    (hc : h.check S X Y = true) : X.toState hX ⟶ Y.toState hY where
  α :=
    { app := fun c x => ⟨h.mapElem x.1, mapElem_has hc c.as.2 x.2⟩
      naturality := by
        intro c d f
        obtain ⟨a, rfl⟩ := Schema.obj_surjective c
        obtain ⟨b, rfl⟩ := Schema.obj_surjective d
        obtain ⟨p, rfl⟩ := Schema.mor_surjective f
        funext x
        apply Subtype.ext
        change h.mapElem ((X.functor hX).map (Schema.mor p) x).1 =
          ((Y.functor hY).map (Schema.mor p) ⟨h.mapElem x.1, mapElem_has hc a.2 x.2⟩).1
        have e₁ := FinState.eval_map hY p ⟨h.mapElem x.1, mapElem_has hc a.2 x.2⟩
        have e₂ := FinState.eval_map hX p x
        rw [eval_mapElem hS hX hc a.2 x.2 (Schema.tgt?_names p), e₂, Option.map_some] at e₁
        exact Option.some.inj e₁ }
  values v x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | ent => exact hx.elim
    | val w k =>
      change w = v at hx
      subst hx
      rfl

end FinHom

namespace FinState

end FinState

/-! ## Restriction -/

section Lookup

theorem lookup_map_key {α β γ : Type} [BEq β] [LawfulBEq β] (key : α → β) (g : β → γ) :
    ∀ (l : List α) {b : β}, b ∈ l.map key →
      (l.map fun x => (key x, g (key x))).lookup b = some (g b)
  | [], _, h => by simp at h
  | x :: xs, b, h => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hb : b = key x
    · subst hb
      simp
    · have : (b == key x) = false := by simpa using hb
      rw [this]
      exact lookup_map_key key g xs (by simpa [hb] using h)

theorem filterMap_range {α : Type} (f : Nat → Option α) :
    ∀ n, (∀ m < n, (f m).isSome) →
      ((List.range n).filterMap f).length = n ∧
        ∀ i < n, ((List.range n).filterMap f)[i]? = f i
  | 0, _ => by simp
  | n + 1, h => by
    obtain ⟨hlen, hget⟩ := filterMap_range f n fun m hm => h m (by omega)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h n (by omega))
    rw [List.range_succ, List.filterMap_append]
    simp only [List.filterMap_cons, hy, List.filterMap_nil]
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getElem?_append_left (by omega), hget i hi]
    · rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self, hy]
      rfl

end Lookup

namespace FinState

variable (T : Translation) (S S' : Schema) (X : FinState K)

/-- The column of the reference named `n` out of `e` in `Δ_T X`: the target of each
entity along the image path. -/
def refColumn (e n : String) : List Nat :=
  (List.range (X.size (T.ent e))).map fun i =>
    match X.eval S' (.ent (T.ent e) i) (T.gen (.entity e) n) with
    | some (.ent _ j) => j
    | _ => 0

/-- The column of the attribute named `n` out of `e` in `Δ_T X`: the value of each
entity along the image path. -/
def attrColumn (e n : String) : List (Σ v, K v) :=
  (List.range (X.size (T.ent e))).filterMap fun i =>
    match X.eval S' (.ent (T.ent e) i) (T.gen (.entity e) n) with
    | some (.val v k) => some ⟨v, k⟩
    | _ => none

/-- Restriction `Δ_T X` of a finite state of `S'` along a translation from `S`, as
data: the entities of `T e` for each entity type `e` of `S`, and the columns of
the generators along their image paths. -/
def restrict : FinState K where
  sizes := S.entities.map fun e => (e, X.size (T.ent e))
  refs := S.refs.map fun r => ((r.src, r.name), X.refColumn T S' r.src r.name)
  attrs := S.attrs.map fun a => ((a.src, a.name), X.attrColumn T S' a.src a.name)

/-- An element of `Δ_T X` as an element of `X`. -/
def rename : Elem K → Elem K
  | .ent e i => .ent (T.ent e) i
  | .val v k => .val v k

/-- An element of `X` at the image of `o`, as an element of `Δ_T X` at `o`. -/
def unrename (o : Ob) : Elem K → Elem K
  | .ent _ j => match o with
    | .entity e => .ent e j
    | .value _ => .ent "" j
  | .val v k => .val v k

variable {T S S' X}

theorem size_restrict {e : String} (he : e ∈ S.entities) :
    (X.restrict T S S').size e = X.size (T.ent e) := by
  have := lookup_map_key (fun e => e) (fun e => X.size (T.ent e)) S.entities (b := e)
    (by simpa using he)
  change ((X.restrict T S S').sizes.lookup e).getD 0 = X.size (T.ent e)
  simp only [restrict]
  rw [this]
  rfl

theorem refCol_restrict {r : Ref} (hr : r ∈ S.refs) :
    (X.restrict T S S').refCol r.src r.name = some (X.refColumn T S' r.src r.name) :=
  lookup_map_key (fun r : Ref => (r.src, r.name)) (fun k => X.refColumn T S' k.1 k.2) S.refs
    (List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem attrCol_restrict {a : Attr} (ha : a ∈ S.attrs) :
    (X.restrict T S S').attrCol a.src a.name = some (X.attrColumn T S' a.src a.name) :=
  lookup_map_key (fun a : Attr => (a.src, a.name)) (fun k => X.attrColumn T S' k.1 k.2)
    S.attrs (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem rename_has {x : Elem K} {o : Ob} (ho : S.IsOb o) (hx : (X.restrict T S S').Has x o) :
    X.Has (rename T x) (T.ob o) := by
  cases o with
  | value => cases x with
    | ent => exact hx.elim
    | val => exact hx
  | entity e => cases x with
    | val => exact hx.elim
    | ent e₀ i =>
      obtain ⟨rfl, hi⟩ := hx
      exact ⟨rfl, size_restrict ho ▸ hi⟩

theorem rename_injective {x y : Elem K} {o : Ob} (hx : (X.restrict T S S').Has x o)
    (hy : (X.restrict T S S').Has y o) (h : rename T x = rename T y) : x = y := by
  cases o with
  | value =>
    cases x with
    | ent => exact hx.elim
    | val => cases y with
      | ent => exact hy.elim
      | val => exact h
  | entity e =>
    cases x with
    | val => exact hx.elim
    | ent e₁ i => cases y with
      | val => exact hy.elim
      | ent e₂ j =>
        obtain ⟨rfl, -⟩ := hx
        obtain ⟨rfl, -⟩ := hy
        obtain rfl : i = j := by simpa [rename] using h
        rfl

theorem unrename_rename {x : Elem K} {o : Ob} (hx : (X.restrict T S S').Has x o) :
    unrename o (rename T x) = x := by
  cases o with
  | value => cases x with
    | ent => exact hx.elim
    | val => rfl
  | entity e => cases x with
    | val => exact hx.elim
    | ent e₀ i =>
      obtain ⟨rfl, -⟩ := hx
      rfl

theorem rename_unrename {z : Elem K} {o : Ob} (hz : X.Has z (T.ob o)) :
    rename T (unrename o z) = z := by
  cases o with
  | value => cases z with
    | ent => exact hz.elim
    | val => rfl
  | entity e => cases z with
    | val => exact hz.elim
    | ent e₀ j =>
      obtain ⟨rfl, -⟩ := hz
      rfl

theorem unrename_has {z : Elem K} {o : Ob} (ho : S.IsOb o) (hz : X.Has z (T.ob o)) :
    (X.restrict T S S').Has (unrename o z) o := by
  cases o with
  | value => cases z with
    | ent => exact hz.elim
    | val => exact hz
  | entity e => cases z with
    | val => exact hz.elim
    | ent e₀ j =>
      obtain ⟨-, hj⟩ := hz
      exact ⟨rfl, (size_restrict ho).symm ▸ hj⟩

end FinState

namespace FinState

variable {T : Translation} {S S' : Schema} {X : FinState K} [∀ v, DecidableEq (K v)]

/-- A step of `Δ_T X` along a generator is the image path in `X`. -/
theorem restrict_step (hS : S.WellFormed) (hX : X.check S' = true) (hT : T.Valid S S')
    {x : Elem K} {o o' : Ob} {n : String} (ho : S.IsOb o)
    (hx : (X.restrict T S S').Has x o) (hs : S.step? o n = some o') :
    ∃ y, (X.restrict T S S').step S x n = some y ∧ (X.restrict T S S').Has y o' ∧
      X.eval S' (rename T x) (T.gen o n) = some (rename T y) := by
  cases o with
  | value => simp [Schema.step?] at hs
  | entity e =>
  cases x with
  | val => exact hx.elim
  | ent e₀ i =>
  obtain ⟨rfl, hi⟩ := hx
  have hi' : i < X.size (T.ent e₀) := size_restrict ho ▸ hi
  have hs₀ := hs
  obtain ⟨z, hz, hz₁⟩ := eval_has hX
    (show X.Has (.ent (T.ent e₀) i) (T.ob (.entity e₀)) from ⟨rfl, hi'⟩)
    (Translation.tgt?_gen hT hs)
  simp only [Schema.step?] at hs
  cases hr : S.ref? e₀ n with
  | some r =>
    rw [hr] at hs
    cases hs
    obtain ⟨hrm, hrs, hrn⟩ := ref?_spec hr
    cases z with
    | val => exact hz₁.elim
    | ent e₁ j =>
      obtain ⟨he₁, hj⟩ := hz₁
      have hcol : (X.refColumn T S' e₀ n)[i]? = some j := by
        simp only [refColumn, List.getElem?_map, List.getElem?_range hi', Option.map_some]
        rw [hz]
      refine ⟨.ent r.tgt j, ?_, ⟨rfl, ?_⟩, ?_⟩
      · have := refCol_restrict (X := X) (T := T) (S' := S') hrm
        rw [hrs, hrn] at this
        simp [step, hr, this, hcol]
      · rw [size_restrict (Schema.isOb_of_step? hS hs₀)]
        exact he₁ ▸ hj
      · simp only [rename]
        rw [hz, he₁]
  | none =>
    rw [hr] at hs
    cases ha : S.attr? e₀ n with
    | none => simp [ha] at hs
    | some a =>
      rw [ha] at hs
      cases hs
      obtain ⟨ham, has, han⟩ := attr?_spec ha
      cases z with
      | ent => exact hz₁.elim
      | val v k =>
        have hall : ∀ m < X.size (T.ent e₀),
            (match X.eval S' (.ent (T.ent e₀) m) (T.gen (.entity e₀) n) with
              | some (.val v k) => some (⟨v, k⟩ : Σ v, K v)
              | _ => none).isSome := by
          intro m hm
          obtain ⟨z', hz', hz₂⟩ := eval_has hX
            (show X.Has (.ent (T.ent e₀) m) (T.ob (.entity e₀)) from ⟨rfl, hm⟩)
            (Translation.tgt?_gen hT hs₀)
          cases z' with
          | ent => exact hz₂.elim
          | val => simp [hz']
        have hcol : (X.attrColumn T S' e₀ n)[i]? = some ⟨v, k⟩ := by
          rw [attrColumn, (filterMap_range _ _ hall).2 i hi', hz]
        refine ⟨.val v k, ?_, hz₁, ?_⟩
        · have := attrCol_restrict (X := X) (T := T) (S' := S') ham
          rw [has, han] at this
          simp [step, hr, ha, this, hcol]
        · simpa [rename] using hz

/-- Following a path in `Δ_T X` is following its image in `X`. -/
theorem restrict_eval (hS : S.WellFormed) (hX : X.check S' = true) (hT : T.Valid S S') :
    ∀ {x : Elem K} {o o' : Ob} {l : List String}, S.IsOb o →
      (X.restrict T S S').Has x o → S.tgt? o l = some o' →
      ∃ y, (X.restrict T S S').eval S x l = some y ∧ (X.restrict T S S').Has y o' ∧
        X.eval S' (rename T x) (T.mapPath S o l) = some (rename T y)
  | x, _, _, [], _, hx, h => ⟨x, rfl, Option.some.inj h ▸ hx, rfl⟩
  | x, o, o', n :: ns, ho, hx, hl => by
    cases hs : S.step? o n with
    | none => simp [hs] at hl
    | some o₁ =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at hl
      obtain ⟨y, hy, hy', hey⟩ := restrict_step hS hX hT ho hx hs
      obtain ⟨z, hz, hz', hez⟩ :=
        restrict_eval hS hX hT (Schema.isOb_of_step? hS hs) hy' hl
      refine ⟨z, by simp [eval, hy, hz], hz', ?_⟩
      simp only [Translation.mapPath, hs]
      rw [eval_append, hey, Option.bind_some, hez]

/-- `Δ_T X` passes the check. -/
theorem restrict_check (hS : S.WellFormed) (hX : X.check S' = true) (hT : T.Valid S S') :
    (X.restrict T S S').check S = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨fun r hr => ?_, fun a ha => ?_⟩, fun q hq i hi => ?_⟩
  · rw [refCol_restrict hr]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    refine ⟨by simp [refColumn, size_restrict (hS.ref_src r hr)], fun j hj => ?_⟩
    simp only [refColumn, List.mem_map, List.mem_range] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    obtain ⟨z, hz, hz₁⟩ := eval_has hX
      (show X.Has (.ent (T.ent r.src) i) (T.ob (.entity r.src)) from ⟨rfl, hi⟩)
      (Translation.tgt?_gen hT (Schema.step?_of_mem_refs hS hr))
    cases z with
    | val => exact hz₁.elim
    | ent e₁ j =>
      obtain ⟨he₁, hj'⟩ := hz₁
      rw [hz, size_restrict (hS.ref_tgt r hr)]
      exact he₁ ▸ hj'
  · rw [attrCol_restrict ha]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    have hall : ∀ m < X.size (T.ent a.src),
        (match X.eval S' (.ent (T.ent a.src) m) (T.gen (.entity a.src) a.name) with
          | some (.val v k) => some (⟨v, k⟩ : Σ v, K v)
          | _ => none).isSome := by
      intro m hm
      obtain ⟨z, hz, hz₁⟩ := eval_has hX
        (show X.Has (.ent (T.ent a.src) m) (T.ob (.entity a.src)) from ⟨rfl, hm⟩)
        (Translation.tgt?_gen hT (Schema.step?_of_mem_attrs hS ha))
      cases z with
      | ent => exact hz₁.elim
      | val => simp [hz]
    refine ⟨by rw [attrColumn, (filterMap_range _ _ hall).1, size_restrict (hS.attr_src a ha)],
      fun x hx => ?_⟩
    obtain ⟨m, hm, hmx⟩ := List.mem_filterMap.mp hx
    rw [List.mem_range] at hm
    obtain ⟨z, hz, hz₁⟩ := eval_has hX
      (show X.Has (.ent (T.ent a.src) m) (T.ob (.entity a.src)) from ⟨rfl, hm⟩)
      (Translation.tgt?_gen hT (Schema.step?_of_mem_attrs hS ha))
    rw [hz] at hmx
    cases z with
    | ent => exact hz₁.elim
    | val v k =>
      cases hmx
      exact hz₁
  · have hsrc := hS.eqn_src q hq
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
    have hx : (X.restrict T S S').Has (.ent q.src i) (.entity q.src) := ⟨rfl, hi⟩
    obtain ⟨y₁, h₁, h₁', e₁⟩ :=
      restrict_eval hS hX hT (show S.IsOb (.entity q.src) from hsrc) hx hl
    obtain ⟨y₂, h₂, h₂', e₂⟩ :=
      restrict_eval hS hX hT (show S.IsOb (.entity q.src) from hsrc) hx hr
    rw [h₁, h₂]
    congr 1
    apply rename_injective h₁' h₂'
    obtain ⟨hm, b, p, p', hp, hp', hpp⟩ := hT.eqn q hq
    have hx' : X.Has (.ent (T.ent q.src) i) (.entity (T.ent q.src)) :=
      ⟨rfl, size_restrict hsrc ▸ hi⟩
    have m₁ := eval_map hX p ⟨.ent (T.ent q.src) i, hx'⟩
    have m₂ := eval_map hX p' ⟨.ent (T.ent q.src) i, hx'⟩
    rw [hp] at m₁
    rw [hp'] at m₂
    change X.eval S' (.ent (T.ent q.src) i) _ = _ at e₁ e₂
    rw [e₁] at m₁
    rw [e₂] at m₂
    rw [Option.some.inj m₁, Option.some.inj m₂, hpp]

/-- The elements of `Δ_T X` at `a` are the elements of `X` at the image of `a`. -/
def restrictEquiv (hT : T.Valid S S') (a : S.Obj) :
    (X.restrict T S S').Carrier a ≃ X.Carrier (S := S') (Translation.obj hT a) where
  toFun x := ⟨rename T x.1, rename_has a.2 x.2⟩
  invFun z := ⟨unrename a.1 z.1, unrename_has a.2 z.2⟩
  left_inv x := Subtype.ext (unrename_rename x.2)
  right_inv z := Subtype.ext (rename_unrename z.2)

/-- `Δ_T X` computed on data is isomorphic to `Δ_T` applied to the state of `X`. -/
def restrictIso (hS : S.WellFormed) (hS' : S'.WellFormed) (hX : X.check S' = true)
    (hT : T.Valid S S') :
    (X.restrict T S S').toState (restrict_check hS hX hT) ≅
      Translation.restrictState hS' hT (X.toState hX) :=
  let N : (X.restrict T S S').functor (restrict_check hS hX hT) ≅
      Translation.functor hS' hT ⋙ X.functor hX :=
    NatIso.ofComponents (fun c => (restrictEquiv hT c.as).toIso) (by
      intro c d f
      obtain ⟨a, rfl⟩ := Schema.obj_surjective c
      obtain ⟨b, rfl⟩ := Schema.obj_surjective d
      obtain ⟨p, rfl⟩ := Schema.mor_surjective f
      funext x
      apply Subtype.ext
      change rename T ((X.restrict T S S').functor (restrict_check hS hX hT)
          |>.map (Schema.mor p) x).1 =
        ((X.functor hX).map (Schema.mor (Translation.functorPath hS' hT p))
          ⟨rename T x.1, rename_has a.2 x.2⟩).1
      have e₁ := eval_map (restrict_check hS hX hT) p x
      have e₂ := eval_map hX (Translation.functorPath hS' hT p) ⟨rename T x.1, rename_has a.2 x.2⟩
      rw [Translation.names_functorPath] at e₂
      obtain ⟨y, hy, -, hey⟩ := restrict_eval hS hX hT a.2 x.2 (Schema.tgt?_names p)
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
        rfl⟩
    inv := ⟨N.inv, fun v x => by
      obtain ⟨x, hx⟩ := x
      cases x with
      | ent => exact hx.elim
      | val w k =>
        change w = v at hx
        subst hx
        rfl⟩
    hom_inv_id := Schema.State.Hom.ext N.hom_inv_id
    inv_hom_id := Schema.State.Hom.ext N.inv_hom_id }

end FinState

end DDD
