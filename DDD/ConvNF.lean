import DDD.ValueCat
import DDD.PathEq

/-!
# Normal forms of paths of conversions

`TypeList.nf v l` rewrites the path of conversions named `l` out of `v` with the
equations of `TypeList.Basic`, read left to right, into a normal form: a stack
of steps and a flag for `some`. Reading the names one at a time:

- a coercion followed by its inverse is removed;
- `datetime` followed by `date` or `time`, out of `timestamp`, becomes `date` or
  `time`;
- a coercion followed by `string` becomes `string`, repeatedly;
- a run of tables is one block, compared with another block by the function it
  computes (`tablesFn?`); a block that computes the identity is removed;
- `some` moves to the end, past the lifts that follow it, which become the
  conversions they lift.

Each rule is an instance of an equation of `Basic`, at a plain type or lifted,
and checks that both sides lead to the same type. `Schema.convEq_sound`: two
paths with the same normal form present the same morphism of `S.vcat L`.
`Schema.pathEqV` splits a path of `S.vcat L` into its part in `S`, up to the first
value type, and its conversions, and compares the first by `Schema.pathEq` and
the second by normal forms (`pathEqV_sound`). Equations outside `Basic` are not
used. The converse, that equal morphisms have equal normal forms, is not proved.
-/

namespace DDD

/-- The type that an optional type makes optional, and a plain type itself. -/
def ValueType.plain (v : ValueType) : ValueType :=
  match v with
  | .optional u => u
  | _ => v

namespace TypeList

variable (L : TypeList)

/-- A condition on plain types, at a plain type or lifted to its optional type. -/
def lifted (P : ValueType → Bool) (u : ValueType) : Bool :=
  match u with
  | .optional u' => u'.isPlain && P u'
  | _ => P u

/-! ## The rules -/

/-- `[x, y]` out of `u` is a coercion followed by its inverse. -/
def cancelsPlain (x y : String) (u : ValueType) : Bool :=
  (match u with
    | .named m => (L.base? m).any fun b => x == b.text && y == m
    | _ => false) ||
  (L.base? x).any fun b => b == u && y == b.text

/-- `x` out of `u` is a coercion. -/
def coercionPlain (x : String) (u : ValueType) : Bool :=
  (match u with
    | .named m => (L.base? m).any fun b => x == b.text
    | _ => false) ||
  (L.base? x).any (· == u)

/-- `ns` out of `u` is a path of tables that computes the identity. -/
def identityPlain (ns : List String) (u : ValueType) : Bool :=
  (L.tablesFn? u ns).isSome && L.tablesFn? u ns == L.tablesFn? u []

/-- `ns` and `ns'` out of `u` are paths of tables that compute the same function. -/
def sameFnPlain (ns ns' : List String) (u : ValueType) : Bool :=
  (L.tablesFn? u ns).isSome && L.tablesFn? u ns == L.tablesFn? u ns'

/-- `n` out of `u` is a table. -/
def isTable (u : ValueType) (n : String) : Bool :=
  n != "some" && n != "string" && (builtinConv? u.plain n).isNone &&
    (L.coerce? u.plain n).isNone && (L.table? u.plain n).isSome

/-- A step of a normal form: a conversion, or a run of tables (`table`), out of
`src`. -/
structure Tok where
  src : ValueType
  names : List String
  table : Bool
deriving DecidableEq, Repr

/-- The names of a stack of steps, the top first, from the bottom to the top. -/
def real : List Tok → List String
  | [] => []
  | t :: s => real s ++ t.names

/-- A run of tables `ns` out of `u`, or nothing when it computes the identity. -/
def block (u : ValueType) (ns : List String) (s : List Tok) : List Tok :=
  if lifted (L.identityPlain ns) u && L.convTgt? u ns == some u then s
  else ⟨u, ns, true⟩ :: s

/-- The conversion `n` out of `u`, on a stack whose top ends at `u`. -/
def push (u : ValueType) (n : String) : List Tok → List Tok
  | [] => if L.isTable u n then L.block u [n] [] else [⟨u, [n], false⟩]
  | t :: s =>
    if t.table && L.isTable u n then L.block t.src (t.names ++ [n]) s
    else match t.names with
      | [x] =>
        if lifted (L.cancelsPlain x n) t.src && L.convTgt? t.src [x, n] == some t.src then s
        else if n == "string" && lifted (L.coercionPlain x) t.src &&
            L.convTgt? t.src [x, n] == L.convTgt? t.src [n] then push t.src n s
        else if x == "datetime" && (n == "date" || n == "time") &&
            lifted (· == .timestamp) t.src &&
            L.convTgt? t.src [x, n] == L.convTgt? t.src [n] then ⟨t.src, [n], false⟩ :: s
        else if L.isTable u n then L.block u [n] (t :: s)
        else ⟨u, [n], false⟩ :: t :: s
      | _ => if L.isTable u n then L.block u [n] (t :: s) else ⟨u, [n], false⟩ :: t :: s

/-- A normal form in progress: the stack, its type `cur`, and whether a `some` was
moved to the end. -/
structure NF where
  cur : ValueType
  moved : Bool
  stk : List Tok
deriving DecidableEq, Repr

/-- The type of the path read so far. -/
def NF.actual (st : NF) : ValueType := if st.moved then .optional st.cur else st.cur

/-- The path a normal form presents. -/
def NF.real (st : NF) : List String := TypeList.real st.stk ++ if st.moved then ["some"] else []

/-- One name more. -/
def nfStep (st : NF) (n : String) : NF :=
  if n = "some" then { st with moved := true }
  else match L.conv? st.cur n with
    | some w => ⟨w, st.moved, L.push st.cur n st.stk⟩
    | none => st

/-- The normal form of the path named `l` out of `v`. -/
def nf (v : ValueType) (l : List String) : NF := l.foldl L.nfStep ⟨v, false, []⟩

/-- Two steps of normal forms are the same: equal, or runs of tables that compute
the same function. -/
def sameTok (t t' : Tok) : Bool :=
  t.src == t'.src && t.table == t'.table &&
    (t.names == t'.names ||
      (t.table && lifted (L.sameFnPlain t.names t'.names) t.src &&
        L.convTgt? t.src t.names == L.convTgt? t.src t'.names))

/-- Two stacks are the same, step by step. -/
def sameStk : List Tok → List Tok → Bool
  | [], [] => true
  | t :: s, t' :: s' => L.sameTok t t' && sameStk s s'
  | _, _ => false

/-- Path equality of conversions out of `v`: both paths exist and lead to the same
type, and their normal forms are the same. -/
def convEq (v : ValueType) (l l' : List String) : Bool :=
  (L.convTgt? v l).isSome && L.convTgt? v l == L.convTgt? v l' &&
    (L.nf v l).moved == (L.nf v l').moved && L.sameStk (L.nf v l).stk (L.nf v l').stk

/-! ## Lemmas on conversions -/

variable {L}

theorem basic_of_lifted {P : ValueType → Bool} {l r : List String}
    (hP : ∀ u, P u = true → L.Basic u l r) {u : ValueType} (h : lifted P u = true) :
    L.Basic u l r := by
  unfold lifted at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact .lift h.1 (hP _ h.2)
  · exact hP _ h

theorem basic_cancels {x y : String} {u : ValueType} (h : L.cancelsPlain x y u = true) :
    L.Basic u [x, y] [] := by
  simp only [cancelsPlain, Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · obtain ⟨b, hb, hx⟩ := (Option.any_eq_true _ _).mp h
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact .coerceBack hb
    · exact absurd h (by simp)
  · obtain ⟨b, hb, hx⟩ := (Option.any_eq_true _ _).mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact .coerceThere hb

theorem basic_coercion {x : String} {u : ValueType} (h : L.coercionPlain x u = true) :
    L.Basic u [x, "string"] ["string"] := by
  simp only [coercionPlain, Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · obtain ⟨b, hb, hx⟩ := (Option.any_eq_true _ _).mp h
      obtain rfl : x = b.text := by simpa using hx
      exact .stringBack hb
    · exact absurd h (by simp)
  · obtain ⟨b, hb, hx⟩ := (Option.any_eq_true _ _).mp h
    obtain rfl : b = u := by simpa using hx
    exact .stringThere hb

theorem basic_identity {ns : List String} {u : ValueType} (h : L.identityPlain ns u = true) :
    L.Basic u ns [] := by
  simp only [identityPlain, Bool.and_eq_true, beq_iff_eq] at h
  exact .tables h.1 h.2

theorem basic_sameFn {ns ns' : List String} {u : ValueType} (h : L.sameFnPlain ns ns' u = true) :
    L.Basic u ns ns' := by
  simp only [sameFnPlain, Bool.and_eq_true, beq_iff_eq] at h
  exact .tables h.1 h.2

theorem basic_date {n : String} {u : ValueType} (hn : (n == "date" || n == "time") = true)
    (h : (u == .timestamp) = true) : L.Basic u ["datetime", n] [n] := by
  obtain rfl : u = .timestamp := by simpa using h
  rcases Bool.or_eq_true_iff.mp hn with hn | hn
  · obtain rfl : n = "date" := by simpa using hn
    exact .date
  · obtain rfl : n = "time" := by simpa using hn
    exact .time

@[simp] theorem convTgt?_nil (v : ValueType) : L.convTgt? v [] = some v := rfl

theorem convTgt?_cons (v : ValueType) (n : String) (ns : List String) :
    L.convTgt? v (n :: ns) = (L.conv? v n).bind fun w => L.convTgt? w ns := rfl

theorem convTgt?_append (v : ValueType) (l m : List String) :
    L.convTgt? v (l ++ m) = (L.convTgt? v l).bind fun w => L.convTgt? w m := by
  induction l generalizing v with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.cons_append, convTgt?_cons, ih]
    cases L.conv? v n <;> rfl

theorem convTgt?_singleton (v : ValueType) (n : String) : L.convTgt? v [n] = L.conv? v n := by
  rw [convTgt?_cons]
  cases L.conv? v n <;> rfl

theorem convTgt?_snoc {v u : ValueType} {l : List String} (h : L.convTgt? v l = some u)
    (n : String) : L.convTgt? v (l ++ [n]) = L.conv? u n := by
  rw [convTgt?_append, h, Option.bind_some, convTgt?_singleton]

theorem conv?_plain {u : ValueType} (hu : u.isPlain = true) (n : String) :
    L.conv? u n = L.plainConv? u n := by
  cases u <;> first | rfl | exact absurd hu (by simp [ValueType.isPlain])

theorem conv?_some {x y : ValueType} (h : L.conv? x "some" = some y) :
    x.isPlain = true ∧ y = .optional x := by
  cases x with
  | optional u =>
    simp only [conv?] at h
    split at h
    · split at h
      · rename_i w hw
        simp only [plainConv?, if_true] at hw
        obtain rfl := Option.some.inj hw
        simp [ValueType.isPlain] at h
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | _ =>
    simp only [conv?, plainConv?, if_true, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩

theorem conv?_optional {u y : ValueType} {n : String} (h : L.conv? (.optional u) n = some y) :
    u.isPlain = true ∧ ∃ w, L.plainConv? u n = some w ∧ w.isPlain = true ∧ y = .optional w := by
  simp only [conv?] at h
  split at h
  · rename_i hu
    split at h
    · rename_i w hw
      split at h
      · rename_i hw'
        exact ⟨hu, w, hw, hw', (Option.some.inj h).symm⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end TypeList

/-! ## Soundness -/

namespace Schema

open TypeList

variable {S : Schema} {L : TypeList}

theorem vtgt?_value_conv (v : ValueType) :
    ∀ l : List String, S.vtgt? L (.value v) l = (L.convTgt? v l).map .value
  | [] => rfl
  | n :: ns => by
    simp only [vtgt?_cons, vstep?, convTgt?_cons]
    cases L.conv? v n with
    | none => rfl
    | some w => exact vtgt?_value_conv w ns

/-- The value object of `v`. -/
abbrev vval (S : Schema) (L : TypeList) (v : ValueType) : S.VObj L := ⟨.value v, trivial⟩

theorem convTgt?_of_vPathEq {v : ValueType} {l l' : List String}
    (h : S.VPathEq L (vval S L v) l l') : L.convTgt? v l = L.convTgt? v l' := by
  obtain ⟨b, p, q, hp, hq, -⟩ := h
  have h₁ := vtgt?_vnames p
  have h₂ := vtgt?_vnames q
  rw [hp, vtgt?_value_conv] at h₁
  rw [hq, vtgt?_value_conv] at h₂
  exact Option.map_injective (fun _ _ h => Ob.value.inj h) (h₁.trans h₂.symm)

variable (hS : S.WellFormed)
include hS

theorem vPathEq_refl {v u : ValueType} {l : List String} (h : L.convTgt? v l = some u) :
    S.VPathEq L (vval S L v) l l :=
  VPathEq.refl hS (o := .value u) (by rw [vtgt?_value_conv, h]; rfl)

/-- An equation of `Basic` between two paths that lead to the same type holds after
any path. -/
theorem vPathEq_basic {v u : ValueType} {p l r : List String} {o : ValueType}
    (hp : L.convTgt? v p = some u) (h : L.Basic u l r) (hl : L.convTgt? u l = some o)
    (hr : L.convTgt? u r = some o) : S.VPathEq L (vval S L v) (p ++ l) (p ++ r) :=
  VPathEq.append_left hS (c := vval S L u) (by rw [vtgt?_value_conv, hp]; rfl)
    (VPathEq.of_basic hS h (o := .value o) (by rw [vtgt?_value_conv, hl]; rfl)
      (by rw [vtgt?_value_conv, hr]; rfl))

theorem vPathEq_append_right {v : ValueType} {l l' m : List String} {o : ValueType}
    (h : S.VPathEq L (vval S L v) l l') (hm : L.convTgt? v (l ++ m) = some o) :
    S.VPathEq L (vval S L v) (l ++ m) (l' ++ m) :=
  VPathEq.append_right hS h (o := .value o) (by rw [vtgt?_value_conv, hm]; rfl)

omit hS in
/-- The steps of a stack lead from `v` to `u`, each from the end of the steps below. -/
def Typed (L : TypeList) (v : ValueType) : List Tok → ValueType → Prop
  | [], u => u = v
  | t :: s, u => Typed L v s t.src ∧ L.convTgt? t.src t.names = some u

omit hS in
theorem convTgt?_real {v : ValueType} : ∀ {s : List Tok} {u : ValueType},
    Typed L v s u → L.convTgt? v (real s) = some u
  | [], _, h => by rw [show _ = v from h]; rfl
  | t :: s, _, ⟨h₁, h₂⟩ => by
    rw [real, convTgt?_append, convTgt?_real h₁, Option.bind_some, h₂]

theorem block_sound {v u w : ValueType} {s : List Tok} {ns : List String}
    (hs : Typed L v s u) (hns : L.convTgt? u ns = some w) :
    Typed L v (L.block u ns s) w ∧
      S.VPathEq L (vval S L v) (real s ++ ns) (real (L.block u ns s)) := by
  unfold block
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain rfl : w = u := Option.some.inj (hns.symm.trans h.2)
    refine ⟨hs, ?_⟩
    have := vPathEq_basic hS (convTgt?_real hs) (basic_of_lifted (fun _ => basic_identity) h.1)
      hns rfl
    simpa using this
  · exact ⟨⟨hs, hns⟩, vPathEq_refl hS (by rw [convTgt?_append, convTgt?_real hs]; exact hns)⟩

theorem push_sound {v : ValueType} (n : String) :
    ∀ {s : List Tok} {u w : ValueType}, Typed L v s u → L.conv? u n = some w →
      Typed L v (L.push u n s) w ∧ S.VPathEq L (vval S L v) (real s ++ [n]) (real (L.push u n s))
  | [], u, w, hs, hn => by
    have hn' : L.convTgt? u [n] = some w := by rw [convTgt?_singleton, hn]
    unfold push
    split
    · exact block_sound hS hs hn'
    · exact ⟨⟨hs, hn'⟩, vPathEq_refl hS (by rw [convTgt?_append, convTgt?_real hs]; exact hn')⟩
  | t :: s, u, w, hs, hn => by
    have hn' : L.convTgt? u [n] = some w := by rw [convTgt?_singleton, hn]
    have hdefault : Typed L v (if L.isTable u n then L.block u [n] (t :: s)
          else ⟨u, [n], false⟩ :: t :: s) w ∧
        S.VPathEq L (vval S L v) (real (t :: s) ++ [n])
          (real (if L.isTable u n then L.block u [n] (t :: s) else ⟨u, [n], false⟩ :: t :: s)) := by
      split
      · exact block_sound hS hs hn'
      · exact ⟨⟨hs, hn'⟩, vPathEq_refl hS (by rw [convTgt?_append, convTgt?_real hs]; exact hn')⟩
    obtain ⟨hs₁, hs₂⟩ := hs
    unfold push
    split
    · have hns : L.convTgt? t.src (t.names ++ [n]) = some w := by
        rw [convTgt?_snoc hs₂, hn]
      have := block_sound hS hs₁ hns
      simpa [real, List.append_assoc] using this
    · split
      · rename_i x hx
        have hx' : L.convTgt? t.src [x, n] = some w := by
          rw [show [x, n] = [x] ++ [n] from rfl, convTgt?_snoc (hx ▸ hs₂), hn]
        have hreal : real (t :: s) ++ [n] = real s ++ [x, n] := by simp [real, hx]
        split
        · rename_i h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain rfl : w = t.src := Option.some.inj (hx'.symm.trans h.2)
          refine ⟨hs₁, ?_⟩
          rw [hreal]
          have := vPathEq_basic hS (convTgt?_real hs₁)
            (basic_of_lifted (fun _ => basic_cancels) h.1) hx' rfl
          simpa using this
        · split
          · rename_i h
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨⟨hstr, hco⟩, htgt⟩ := h
            have hs' : L.convTgt? t.src [n] = some w := htgt ▸ hx'
            obtain ⟨ih₁, ih₂⟩ := push_sound n hs₁ (by rwa [convTgt?_singleton] at hs')
            refine ⟨ih₁, ?_⟩
            rw [hreal]
            refine VPathEq.trans ?_ ih₂
            subst hstr
            exact vPathEq_basic hS (convTgt?_real hs₁)
              (basic_of_lifted (fun _ => basic_coercion) hco) hx' hs'
          · split
            · rename_i h
              simp only [Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨⟨⟨hdt, hn₂⟩, hts⟩, htgt⟩ := h
              have hs' : L.convTgt? t.src [n] = some w := htgt ▸ hx'
              refine ⟨⟨hs₁, hs'⟩, ?_⟩
              rw [hreal]
              subst hdt
              have := vPathEq_basic hS (convTgt?_real hs₁)
                (basic_of_lifted (fun _ => basic_date hn₂) hts) hx' hs'
              simpa [real] using this
            · exact hdefault
      · exact hdefault

variable (L) in
/-- What the normal form of a path satisfies: its stack is typed, and the path it
presents is equal to the path. -/
structure NFInv (v : ValueType) (l : List String) (st : NF) : Prop where
  typed : Typed L v st.stk st.cur
  plain : st.moved = true → st.cur.isPlain = true
  tgt : L.convTgt? v l = some st.actual
  eq : S.VPathEq L (vval S L v) l st.real

theorem nfStep_sound {v : ValueType} {l : List String} {st : NF} (h : NFInv (S := S) L v l st)
    (n : String) {y : ValueType} (hy : L.convTgt? v (l ++ [n]) = some y) :
    NFInv (S := S) L v (l ++ [n]) (L.nfStep st n) := by
  rw [convTgt?_snoc h.tgt] at hy
  unfold nfStep
  split
  · rename_i hn
    subst hn
    obtain ⟨hp, rfl⟩ := conv?_some hy
    have hm : st.moved = false := by
      cases hmv : st.moved
      · rfl
      · simp [NF.actual, hmv, ValueType.isPlain] at hp
    have hact : st.actual = st.cur := by simp [NF.actual, hm]
    refine ⟨h.typed, fun _ => hact ▸ hp, ?_, ?_⟩
    · rw [convTgt?_snoc h.tgt, hy, hact]
      simp [NF.actual]
    · have := vPathEq_append_right hS h.eq (by rw [convTgt?_snoc h.tgt, hy])
      simpa [NF.real, hm] using this
  · rename_i hn
    cases hmv : st.moved
    · have hact : st.actual = st.cur := by simp [NF.actual, hmv]
      rw [hact] at hy
      rw [hy]
      obtain ⟨h₁, h₂⟩ := push_sound hS n h.typed hy
      refine ⟨h₁, by simp, ?_, ?_⟩
      · rw [convTgt?_snoc h.tgt, hact, hy]
        simp [NF.actual]
      · have h₃ := vPathEq_append_right hS h.eq (by rw [convTgt?_snoc h.tgt, hact, hy])
        simp only [NF.real, hmv] at h₃ ⊢
        simp only [Bool.false_eq_true, if_false, List.append_nil] at h₃ ⊢
        exact h₃.trans h₂
    · have hact : st.actual = .optional st.cur := by simp [NF.actual, hmv]
      rw [hact] at hy
      obtain ⟨hu, w, hw, hwp, rfl⟩ := conv?_optional hy
      have hc : L.conv? st.cur n = some w := by rw [conv?_plain hu, hw]
      rw [hc]
      obtain ⟨h₁, h₂⟩ := push_sound hS n h.typed hc
      have hreal := convTgt?_real h.typed
      refine ⟨h₁, fun _ => hwp, ?_, ?_⟩
      · rw [convTgt?_snoc h.tgt, hact, hy]
        simp [NF.actual]
      · -- l ++ [n] = R ++ [some, n] = R ++ [n, some] = push ++ [some]
        have hR : L.convTgt? v (real st.stk ++ ["some"]) = some (.optional st.cur) := by
          rw [convTgt?_snoc hreal]
          simp [conv?_plain hu, plainConv?]
        have e₁ := vPathEq_append_right hS h.eq (m := [n]) (by rw [convTgt?_snoc h.tgt, hact, hy])
        simp only [NF.real, hmv, if_true] at e₁ ⊢
        have hsome : L.Basic st.cur ["some", n] [n, "some"] :=
          .some hu hn hw hwp
        have e₂ := vPathEq_basic hS (L := L) hreal hsome
          (o := .optional w) (by simp [convTgt?_cons, conv?_plain hu, plainConv?, hy]) (by
            simp [convTgt?_cons, hc, conv?_plain hwp, plainConv?])
        have e₃ := vPathEq_append_right hS h₂ (m := ["some"]) (o := .optional w) (by
          rw [convTgt?_snoc (by rw [convTgt?_append, hreal]; simpa [convTgt?_singleton] using hc)]
          simp [conv?_plain hwp, plainConv?])
        simp only [List.append_assoc, List.singleton_append] at e₁ e₂ e₃
        exact e₁.trans (e₂.trans e₃)

theorem nf_sound_aux {v : ValueType} : ∀ (l acc : List String) (st : NF),
    NFInv (S := S) L v acc st → ∀ {y : ValueType}, L.convTgt? v (acc ++ l) = some y →
      NFInv (S := S) L v (acc ++ l) (l.foldl L.nfStep st)
  | [], acc, st, h, _, _ => by simpa using h
  | n :: ns, acc, st, h, y, hy => by
    have hy' : L.convTgt? v ((acc ++ [n]) ++ ns) = some y := by simpa using hy
    have hn : (L.convTgt? v (acc ++ [n])).isSome := by
      rw [convTgt?_append] at hy'
      cases hc : L.convTgt? v (acc ++ [n]) <;> simp_all
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hn
    have := nf_sound_aux ns (acc ++ [n]) (L.nfStep st n) (nfStep_sound hS h n hx) hy'
    simpa using this

theorem nf_sound {v : ValueType} (l : List String) {y : ValueType}
    (hy : L.convTgt? v l = some y) : NFInv (S := S) L v l (L.nf v l) := by
  have := nf_sound_aux hS l [] ⟨v, false, []⟩ ⟨rfl, by simp, rfl, vPathEq_refl hS rfl⟩
    (by simpa using hy)
  simpa [nf] using this

theorem sameStk_sound {v : ValueType} :
    ∀ {s s' : List Tok} {u u' : ValueType}, Typed L v s u → Typed L v s' u' →
      L.sameStk s s' = true → u = u' ∧ S.VPathEq L (vval S L v) (real s) (real s')
  | [], [], u, u', hs, hs', _ => by
    obtain rfl : u = v := hs
    obtain rfl : u' = u := hs'
    exact ⟨rfl, vPathEq_refl hS rfl⟩
  | t :: s, t' :: s', u, u', ⟨hs₁, hs₂⟩, ⟨hs₁', hs₂'⟩, h => by
    simp only [sameStk, Bool.and_eq_true] at h
    obtain ⟨ht, h⟩ := h
    obtain ⟨hsrc, ih⟩ := sameStk_sound hs₁ hs₁' h
    simp only [sameTok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨-, -⟩, hn⟩ := ht
    have hreal := convTgt?_real hs₁
    have hreal' := convTgt?_real hs₁'
    have e₁ := vPathEq_append_right hS ih (m := t.names) (o := u) (by
      rw [convTgt?_append, hreal, Option.bind_some, hs₂])
    rcases hn with hn | ⟨⟨-, hfn⟩, htgt⟩
    · have hu : u = u' := by rw [hsrc, hn] at hs₂; exact Option.some.inj (hs₂.symm.trans hs₂')
      refine ⟨hu, ?_⟩
      simp only [real]
      rw [← hn]
      exact e₁
    · have hu : u = u' := by
        rw [hs₂, hsrc, hs₂'] at htgt
        exact Option.some.inj htgt
      subst hu
      refine ⟨rfl, e₁.trans ?_⟩
      have := vPathEq_basic hS (L := L) (hsrc ▸ hreal')
        (basic_of_lifted (fun _ => basic_sameFn) hfn) hs₂ (hsrc ▸ hs₂')
      simpa [real] using this
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => by simp [sameStk] at h

/-- Conversions with the same normal form present the same morphism. -/
theorem convEq_sound {v : ValueType} {l l' : List String} (h : L.convEq v l l' = true) :
    S.VPathEq L (vval S L v) l l' := by
  simp only [convEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hl, htgt⟩, hm⟩, hstk⟩ := h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hl
  have h₁ := nf_sound hS l hx
  have h₂ := nf_sound hS l' (htgt ▸ hx)
  obtain ⟨hu, e⟩ := sameStk_sound hS h₁.typed h₂.typed hstk
  have e' : S.VPathEq L (vval S L v) (L.nf v l).real (L.nf v l').real := by
    unfold NF.real
    rw [hm]
    have hr := convTgt?_real h₁.typed
    cases hmv : (L.nf v l').moved
    · simpa using e
    · have hp := h₁.plain (hm.trans hmv)
      have e₂ := vPathEq_append_right hS e (m := ["some"]) (o := .optional (L.nf v l).cur) (by
        rw [convTgt?_snoc hr]
        simp [conv?_plain hp, plainConv?])
      simpa using e₂
  exact h₁.eq.trans (e'.trans h₂.eq.symm)

/-! ## Paths of `S.vcat L` -/

omit hS

variable (S L) in
/-- The number of generators of `S` at the start of a path, up to the first value
type. -/
def entityLen : Ob → List String → Nat
  | .entity e, n :: ns =>
    match S.step? (.entity e) n with
    | some o => entityLen o ns + 1
    | none => 0
  | _, _ => 0

variable (S L) in
/-- Path equality in `S.vcat L`: path equality in `S`, or path equality in `S` of the
parts up to the first value type `v` and equal normal forms of the conversions out
of `v` that follow. -/
def pathEqV (o : Ob) (l l' : List String) : Bool :=
  S.pathEq o l l' ||
    match S.tgt? o (l.take (S.entityLen o l)) with
    | some (.value v) =>
      S.pathEq o (l.take (S.entityLen o l)) (l'.take (S.entityLen o l')) &&
        L.convEq v (l.drop (S.entityLen o l)) (l'.drop (S.entityLen o l'))
    | _ => false

theorem pathEqV_sound (hS : S.WellFormed) (a : S.VObj L) {l l' : List String}
    (h : S.pathEqV L a.1 l l' = true) : S.VPathEq L a l l' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact VPathEq.of_pathEq (a := ⟨a.1, a.2⟩) (pathEq_sound hS ⟨a.1, a.2⟩ h)
  · split at h
    · rename_i v hv
      simp only [Bool.and_eq_true] at h
      obtain ⟨hp, hc⟩ := h
      have hcs : (L.convTgt? v (l.drop (S.entityLen a.1 l))).isSome := by
        simp only [convEq, Bool.and_eq_true] at hc
        exact hc.1.1.1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hcs
      obtain ⟨b, f, g, hf, hg, -⟩ := pathEq_sound hS ⟨a.1, a.2⟩ hp
      have hb : b.1 = .value v := Option.some.inj ((tgt?_names f).symm.trans (hf ▸ hv))
      have hv' : S.tgt? a.1 (l'.take (S.entityLen a.1 l')) = some (.value v) :=
        hg ▸ hb ▸ tgt?_names g
      have e₁ : S.VPathEq L a (l.take (S.entityLen a.1 l)) (l'.take (S.entityLen a.1 l')) :=
        VPathEq.of_pathEq (a := ⟨a.1, a.2⟩) (pathEq_sound hS ⟨a.1, a.2⟩ hp)
      have e₂ := VPathEq.append_right hS e₁ (m := l.drop (S.entityLen a.1 l)) (o := .value x) (by
        rw [vtgt?_append, vtgt?_of_tgt? hv, Option.bind_some, vtgt?_value_conv, hx]
        rfl)
      have e₃ := VPathEq.append_left hS (c := vval S L v) (vtgt?_of_tgt? hv') (convEq_sound hS hc)
      rw [List.take_append_drop] at e₂
      rw [List.take_append_drop] at e₃
      exact e₂.trans e₃
    · exact absurd h (by simp)

end Schema

end DDD
