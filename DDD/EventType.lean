import DDD.LitData

/-!
# Event types and occurrences

An event type is structure: a name, references to entity types of a published
language, and attributes (`EventType`). Over a published language `P` it is the
schema `ev.over P`: `P` with one more entity type, named after the event type, its
references into `P` and its attributes. The entity type is an aggregate of its own
and, when the event type has a field, a value object, so an occurrence is identified
by all its fields; all occurrences of an event type without fields are alike.
`EventType.check` decides that the name is new, that the references go to entity
types of `P`, that the schema is well formed, which makes the references reach
roots only, and that `P` is included in it.

An occurrence is dynamics: a value for each field (`Occurrence`), an entity of `P`
for each reference and a value for each attribute. Over a finite state `X` of `P`
it is the finite state `occ.state ev X`: `X` with one entity of the event type.
States do not store occurrences: `X` is a state of `P`, and the occurrence is the
one entity added to it.

- `Occurrence.check`: the state with the occurrence is a state of the event
  schema. Then every reference names an entity of `X` (`resolves`), so an
  occurrence with a dangling reference is refused (`check_eq_false_of_dangling`),
  and so is one without a field (`check_eq_false_of_missing`).
  `Occurrence.toState` is its state, with one entity of the event type
  (`size_state_name`).
- Views: a context sees a published language through its translation, as the
  restriction of its state. `Occurrence.checkAt` checks an occurrence against the
  view of a state of a context, owner or consumer, along a translation that may
  convert; its references then name entities of the context, of the images of
  their targets (`resolvesAt`). Two contexts whose states agree on the published
  language accept the same occurrences (`checkAt_of_agree`).
-/

namespace DDD

namespace EventType

variable (ev : EventType) (P : Schema)

/-- The event schema over the published language `P`: `P` with the entity type of
the event, its references and attributes. The entity type is an aggregate of its
own, and a value object when the event type has a field: a value object needs one. -/
def over : Schema :=
  { P with
    entities := P.entities ++ [ev.name]
    refs := P.refs ++ ev.refs.map fun r => ⟨r.1, ev.name, r.2⟩
    attrs := P.attrs ++ ev.attrs.map fun a => ⟨a.1, ev.name, a.2⟩
    aggregates := P.aggregates ++ [⟨ev.name, []⟩]
    valueObjects :=
      P.valueObjects ++ if ev.refs.isEmpty && ev.attrs.isEmpty then [] else [ev.name] }

/-- The check of an event type over `P`: its name is not an entity type of `P`, its
references go to entity types of `P`, the event schema is well formed, and `P` is
included in it. -/
def check : Bool :=
  !P.entities.contains ev.name && ev.refs.all (fun r => P.entities.contains r.2) &&
    (ev.over P).checkWellFormed &&
    ({} : Translation).checkValid P (ev.over P) (ev.over P).pathEq

variable {ev P}

theorem wellFormed (h : ev.check P = true) : (ev.over P).WellFormed := by
  simp only [check, Bool.and_eq_true] at h
  exact (Schema.checkWellFormed_iff _).mp h.1.2

theorem name_notMem (h : ev.check P = true) : ev.name ∉ P.entities := by
  simp only [check, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact h.1.1.1

theorem ref_mem (h : ev.check P = true) {r : String × String} (hr : r ∈ ev.refs) :
    r.2 ∈ P.entities := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem,
    decide_eq_true_eq] at h
  exact h.1.1.2 r hr

/-- The published language is included in the event schema. -/
theorem inclusion (h : ev.check P = true) : ({} : Translation).Valid P (ev.over P) := by
  have hw := wellFormed h
  simp only [check, Bool.and_eq_true] at h
  exact Translation.checkValid_sound (fun a _ _ hp => Schema.pathEq_sound hw a hp) h.2

theorem mem_refs_over {r : String × String} (hr : r ∈ ev.refs) :
    (⟨r.1, ev.name, r.2⟩ : Ref) ∈ (ev.over P).refs :=
  List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

end EventType

/-- An occurrence of an event type: for each reference the number of an entity, and
for each attribute a value. -/
structure Occurrence (K : ValueType → Type) where
  refs : List (String × Nat) := []
  attrs : List (String × Σ v, K v) := []

namespace Occurrence

variable {K : ValueType → Type} (occ : Occurrence K) (ev : EventType) (X : FinState K)

/-- The state `X` of the published language with the occurrence: one entity of the
event type, with its references and values. -/
def state : FinState K where
  sizes := (ev.name, 1) :: X.sizes
  refs := ev.refs.map (fun r =>
    ((ev.name, r.1), ((occ.refs.lookup r.1).map fun i => [i]).getD [])) ++ X.refs
  attrs := ev.attrs.map (fun a =>
    ((ev.name, a.1), ((occ.attrs.lookup a.1).map fun x => [x]).getD [])) ++ X.attrs

/-- The state has one entity of the event type. -/
theorem size_state_name : (occ.state ev X).size ev.name = 1 := by
  simp [FinState.size, state]

/-- The other entity types have the entities of `X`. -/
theorem size_state_of_ne {e : String} (h : e ≠ ev.name) : (occ.state ev X).size e = X.size e := by
  have : (e == ev.name) = false := by simpa using h
  simp [FinState.size, state, List.lookup_cons, this]

/-- The column of a reference of the event type holds the entity the occurrence
names, or nothing. -/
theorem refCol_state {r : String × String} (hr : r ∈ ev.refs) :
    (occ.state ev X).refCol ev.name r.1 =
      some (((occ.refs.lookup r.1).map fun i => [i]).getD []) := by
  have h := lookup_map_key (fun r : String × String => (ev.name, r.1))
    (fun k : String × String => ((occ.refs.lookup k.2).map fun i => [i]).getD []) ev.refs
    (b := (ev.name, r.1)) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  simp only [FinState.refCol, state, List.lookup_append]
  rw [h]
  rfl

variable [∀ v, DecidableEq (K v)]

/-- The check of an occurrence over `X`: it names fields of the event type, each
once, and `X` with the occurrence is a state of the event schema. -/
def check (P : Schema) : Bool :=
  (occ.refs.all fun f => (ev.refs.map (·.1)).contains f.1) &&
    (occ.attrs.all fun f => (ev.attrs.map (·.1)).contains f.1) &&
    decide (occ.refs.map (·.1)).Nodup && decide (occ.attrs.map (·.1)).Nodup &&
    (occ.state ev X).check (ev.over P)

variable {occ ev X} {P : Schema}

theorem check_state (h : occ.check ev X P = true) : (occ.state ev X).check (ev.over P) = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.2

/-- Every reference of a checked occurrence names an entity of `X`. -/
theorem resolves (hev : ev.check P = true) (h : occ.check ev X P = true) {r : String × String}
    (hr : r ∈ ev.refs) : ∃ i, occ.refs.lookup r.1 = some i ∧ i < X.size r.2 := by
  obtain ⟨c, hc, hlen, hlt⟩ := FinState.check_ref (check_state h)
    (EventType.mem_refs_over (P := P) hr)
  rw [refCol_state occ ev X hr] at hc
  rw [size_state_name] at hlen
  have hne : r.2 ≠ ev.name := fun e => EventType.name_notMem hev (e ▸ EventType.ref_mem hev hr)
  cases hl : occ.refs.lookup r.1 with
  | none =>
    rw [hl] at hc
    obtain rfl : [] = c := by simpa using hc
    simp at hlen
  | some i =>
    rw [hl] at hc
    obtain rfl : [i] = c := by simpa using hc
    refine ⟨i, rfl, ?_⟩
    have := hlt i (List.mem_singleton_self i)
    rwa [size_state_of_ne occ ev X hne] at this

/-- An occurrence with a dangling reference is refused. -/
theorem check_eq_false_of_dangling (hev : ev.check P = true) {r : String × String}
    (hr : r ∈ ev.refs) {i : Nat} (hi : occ.refs.lookup r.1 = some i) (hd : X.size r.2 ≤ i) :
    occ.check ev X P = false := by
  by_contra h
  obtain ⟨j, hj, hlt⟩ := resolves hev (by simpa using h) hr
  rw [hi] at hj
  obtain rfl := Option.some.inj hj
  omega

/-- An occurrence without a reference of its event type is refused. -/
theorem check_eq_false_of_missing (hev : ev.check P = true) {r : String × String}
    (hr : r ∈ ev.refs) (hn : occ.refs.lookup r.1 = none) : occ.check ev X P = false := by
  by_contra h
  obtain ⟨j, hj, -⟩ := resolves hev (by simpa using h) hr
  rw [hn] at hj
  cases hj

variable (occ ev X) in
/-- A checked occurrence over `X`, as a state of the event schema with one entity of
the event type. -/
def toState (h : occ.check ev X P = true) : (ev.over P).State K :=
  (occ.state ev X).toState (check_state h)

/-! ## Occurrences in the exchange format -/

open Lean in
/-- An occurrence in the exchange format: `references` (`name`, `entity`) and
`attributes` (`name`, `value`). -/
def toJson (occ : Occurrence LitK) : Json := Json.mkObj [
  ("references", Json.arr (occ.refs.map fun r =>
    Json.mkObj [("name", .str r.1), ("entity", Lean.toJson r.2)]).toArray),
  ("attributes", Json.arr (occ.attrs.map fun a =>
    Json.mkObj [("name", .str a.1), ("value", Lean.toJson a.2.2)]).toArray)]

open Lean in
/-- An occurrence of `ev`, read from JSON; each value is given the value type that
`ev` declares for its attribute. -/
def fromJson (ev : EventType) (j : Json) : Except String (Occurrence LitK) := do
  let refs ← (← getList j "references").mapM fun r => do
    pure (← r.getObjValAs? String "name", ← r.getObjValAs? Nat "entity")
  let attrs ← (← getList j "attributes").mapM fun a => do
    let n ← a.getObjValAs? String "name"
    let some v := ev.attrs.lookup n | throw s!"no attribute {n} in the event type {ev.name}"
    let l : Lit ← fromJson? (← a.getObjVal? "value")
    pure (n, (⟨v, l⟩ : Σ v, LitK v))
  pure { refs, attrs }

instance : DecidableEq (Occurrence LitK) := fun a b =>
  decidable_of_iff (a.refs = b.refs ∧ a.attrs = b.attrs) (by
    obtain ⟨_, _⟩ := a
    obtain ⟨_, _⟩ := b
    simp)

/-- The occurrence with each literal in normal form for its value type, where it has
one. -/
def normalize (L : TypeList) (occ : Occurrence LitK) : Occurrence LitK :=
  { occ with attrs := occ.attrs.map fun a =>
      (a.1, ⟨a.2.1, (L.normalize a.2.1 a.2.2).toOption.getD a.2.2⟩) }

/-- Every value of the occurrence is a literal of its value type, in normal form. -/
def litsFit (L : TypeList) (occ : Occurrence LitK) : Bool :=
  occ.attrs.all fun a => match L.normalize a.2.1 a.2.2 with
    | .ok l => l == a.2.2
    | .error _ => false

/-- An occurrence as text: its references by entity number, then its values. -/
def text (occ : Occurrence LitK) : String :=
  ", ".intercalate ((occ.refs.map fun r => s!"{r.1} = #{r.2}") ++
    occ.attrs.map fun a => s!"{a.1} = {Lit.render a.2.2}")

variable (ev : EventType) (P : Schema) (X : FinState LitK) (occ : Occurrence LitK) in
/-- `occ` is an occurrence of `ev` over the state `X` of `P`: the event schema is
well formed, `X` with the occurrence is a state of it with one entity of the event
type, and every reference names an entity of `X`. -/
def IsOccurrence : Prop :=
  (ev.over P).WellFormed ∧ (occ.state ev X).check (ev.over P) = true ∧
    (occ.state ev X).size ev.name = 1 ∧
    ∀ r ∈ ev.refs, ∃ i, occ.refs.lookup r.1 = some i ∧ i < X.size r.2

theorem isOccurrence {ev : EventType} {P : Schema} {X : FinState LitK} {occ : Occurrence LitK}
    (hev : ev.check P = true) (h : occ.check ev X P = true) : IsOccurrence ev P X occ :=
  ⟨EventType.wellFormed hev, check_state h, size_state_name occ ev X,
    fun _ hr => resolves hev h hr⟩

end Occurrence

/-! ## Views -/

namespace FinState

variable {L : TypeList} {T : Translation} {S S' : Schema} {X : FinState LitK}

theorem size_vrestrictLit {e : String} (he : e ∈ S.entities) :
    (X.vrestrictLit L T S S').size e = X.size (T.ent e) := by
  have := lookup_map_key (fun e => e) (fun e => X.size (T.ent e)) S.entities (b := e)
    (by simpa using he)
  change ((X.vrestrictLit L T S S').sizes.lookup e).getD 0 = X.size (T.ent e)
  simp only [vrestrictLit]
  rw [this]
  rfl

end FinState

namespace Occurrence

variable (L : TypeList) (T : Translation) (P S : Schema) (ev : EventType) (X : FinState LitK)
  (occ : Occurrence LitK)

/-- The check of an occurrence in a context: against the view of the state `X` of
the schema `S`, its restriction to the published language `P` along `T`, which may
convert. -/
def checkAt : Bool := occ.check ev (X.vrestrictLit L T P S) P

variable {L T P S ev X occ}

/-- The references of an occurrence checked in a context name entities of the
context: of the image of the target of each reference. -/
theorem resolvesAt (hev : ev.check P = true) (h : occ.checkAt L T P S ev X = true)
    {r : String × String} (hr : r ∈ ev.refs) :
    ∃ i, occ.refs.lookup r.1 = some i ∧ i < X.size (T.ent r.2) := by
  obtain ⟨i, hi, hlt⟩ := resolves hev h hr
  exact ⟨i, hi, by rwa [FinState.size_vrestrictLit (EventType.ref_mem hev hr)] at hlt⟩

/-- Two contexts whose states agree on the published language accept the same
occurrences. -/
theorem checkAt_of_agree {T' : Translation} {S' : Schema} {X' : FinState LitK}
    (h : X.vrestrictLit L T P S = X'.vrestrictLit L T' P S') :
    occ.checkAt L T P S ev X = occ.checkAt L T' P S' ev X' := by
  unfold checkAt
  rw [h]

end Occurrence

end DDD
