import DDD.PathEq
import Mathlib.CategoryTheory.Whiskering

/-!
# Translations

A translation `T` from a schema `S` to a schema `S'` maps entity types to entity
types, value types to themselves, and each generator to a path: a reference to a
path between the images of its endpoints, an attribute to a path ending at the
same value type. Each equation of `S` must go to an equation that holds in `S'`.

The deep form, `Translation`, lists the images of entity types and generators.
An entity type or generator it does not list keeps its name, so an inclusion
between schemas that use the same names is the empty translation (a conformist).
A general translation models an anti-corruption layer.

- `Translation.Valid T S S'`: the conditions above. `checkValid` decides it,
  given a procedure for path equality in `S'` (`checkValid_iff`).
- `Translation.functor`: the functor `S.cat ⥤ S'.cat` of a valid translation. On
  a path it is the path of the images of the generators (`names_functorPath`); it
  sends value types to themselves.
- `Translation.restrict`: restriction `Δ_T` along the functor, from functors
  `S'.cat ⥤ Type` to functors `S.cat ⥤ Type`.
-/

namespace DDD

open CategoryTheory

/-- The image of the generator `name` out of the entity type `src`: a path, as a
list of names. -/
structure GenImage where
  src : String
  name : String
  path : List String
deriving DecidableEq, Repr

/-- A translation between schemas, as finite data: the images of entity types and
of generators. Unlisted entity types and generators keep their names. -/
structure Translation where
  entities : List (String × String) := []
  gens : List GenImage := []
deriving DecidableEq, Repr

namespace Translation

variable (T : Translation)

/-- The image of the entity type `e`. -/
def ent (e : String) : String :=
  ((T.entities.find? (·.1 == e)).map (·.2)).getD e

/-- The image of an object: entity types by `ent`, value types unchanged. -/
def ob : Ob → Ob
  | .entity e => .entity (T.ent e)
  | .value v => .value v

/-- The image of the generator named `n` out of `o`. -/
def gen : Ob → String → List String
  | .entity e, n => ((T.gens.find? fun g => g.src == e && g.name == n).map (·.path)).getD [n]
  | .value _, n => [n]

/-- The image of the path `l` out of `o` in `S`: the images of its generators, in
order. -/
def mapPath (S : Schema) : Ob → List String → List String
  | _, [] => []
  | o, n :: ns =>
    T.gen o n ++ match S.step? o n with
      | some o' => mapPath S o' ns
      | none => []

/-- `T` is a translation from `S` to `S'`. -/
structure Valid (S S' : Schema) : Prop where
  /-- Entity types go to entity types. -/
  entity : ∀ e ∈ S.entities, T.ent e ∈ S'.entities
  /-- A reference `r : e ⟶ e'` goes to a path from the image of `e` to the image
  of `e'`. -/
  ref : ∀ r ∈ S.refs,
    S'.tgt? (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name) = some (T.ob (.entity r.tgt))
  /-- An attribute `a : e ⟶ v` goes to a path from the image of `e` to `v`. -/
  attr : ∀ a ∈ S.attrs,
    S'.tgt? (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name) = some (.value a.tgt)
  /-- Each equation goes to an equation that holds in `S'`. -/
  eqn : ∀ q ∈ S.eqns, ∃ h : T.ent q.src ∈ S'.entities,
    S'.PathEq ⟨.entity (T.ent q.src), h⟩ (T.mapPath S (.entity q.src) q.lhs)
      (T.mapPath S (.entity q.src) q.rhs)

/-- The check for `Valid`, with `peq` deciding path equality in `S'`. -/
def checkValid (S S' : Schema) (peq : Ob → List String → List String → Bool) : Bool :=
  S.entities.all (fun e => decide (T.ent e ∈ S'.entities)) &&
  S.refs.all (fun r => decide (S'.tgt? (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name) =
    some (T.ob (.entity r.tgt)))) &&
  S.attrs.all (fun a => decide (S'.tgt? (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name) =
    some (.value a.tgt))) &&
  S.eqns.all (fun q => decide (T.ent q.src ∈ S'.entities) &&
    peq (.entity (T.ent q.src)) (T.mapPath S (.entity q.src) q.lhs)
      (T.mapPath S (.entity q.src) q.rhs))

variable {T}

/-- `checkValid` decides `Valid` when `peq` decides path equality in `S'`. -/
theorem checkValid_iff {S S' : Schema} {peq : Ob → List String → List String → Bool}
    (hpeq : ∀ (a : S'.Obj) (l l' : List String), peq a.1 l l' = true ↔ S'.PathEq a l l') :
    T.checkValid S S' peq = true ↔ T.Valid S S' := by
  simp only [checkValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨he, hr⟩, ha⟩, hq⟩
    exact ⟨he, hr, ha, fun q hq' => ⟨(hq q hq').1,
      (hpeq ⟨.entity (T.ent q.src), (hq q hq').1⟩ _ _).mp (hq q hq').2⟩⟩
  · intro h
    refine ⟨⟨⟨h.entity, h.ref⟩, h.attr⟩, fun q hq => ?_⟩
    obtain ⟨hm, hpe⟩ := h.eqn q hq
    exact ⟨hm, (hpeq ⟨.entity (T.ent q.src), hm⟩ _ _).mpr hpe⟩

/-- `checkValid` is sound when `peq` is. -/
theorem checkValid_sound {S S' : Schema} {peq : Ob → List String → List String → Bool}
    (hpeq : ∀ (a : S'.Obj) (l l' : List String), peq a.1 l l' = true → S'.PathEq a l l')
    (h : T.checkValid S S' peq = true) : T.Valid S S' := by
  simp only [checkValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨he, hr⟩, ha⟩, hq⟩ := h
  exact ⟨he, hr, ha, fun q hq' =>
    ⟨(hq q hq').1, hpeq ⟨.entity (T.ent q.src), (hq q hq').1⟩ _ _ (hq q hq').2⟩⟩

/-! ## Images of paths -/

variable {S S' : Schema}

theorem mapPath_singleton (o : Ob) (n : String) : T.mapPath S o [n] = T.gen o n := by
  simp only [mapPath]
  split <;> simp

theorem mapPath_append {o x : Ob} {l : List String} (h : S.tgt? o l = some x)
    (m : List String) : T.mapPath S o (l ++ m) = T.mapPath S o l ++ T.mapPath S x m := by
  induction l generalizing o with
  | nil => cases h; simp [mapPath]
  | cons n ns ih =>
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      simp [mapPath, hs, ih h]

/-- A generator of `S` goes to a path of `S'` between the images of its
endpoints. -/
theorem tgt?_gen (hT : T.Valid S S') {o o' : Ob} {n : String} (h : S.step? o n = some o') :
    S'.tgt? (T.ob o) (T.gen o n) = some (T.ob o') := by
  cases o with
  | value => simp [Schema.step?] at h
  | entity e =>
    simp only [Schema.step?] at h
    split at h
    · rename_i r hr
      cases h
      unfold Schema.ref? at hr
      have hp := List.find?_some hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hT.ref r (List.mem_of_find?_eq_some hr)
    · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      unfold Schema.attr? at ha
      have hp := List.find?_some ha
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hT.attr a (List.mem_of_find?_eq_some ha)

/-! ## The induced functor -/

theorem isOb_ob (hT : T.Valid S S') : ∀ {o : Ob}, S.IsOb o → S'.IsOb (T.ob o)
  | .entity e, h => hT.entity e h
  | .value _, _ => trivial

/-- The image of an object of `S`. -/
def obj (hT : T.Valid S S') (a : S.Obj) : S'.Obj := ⟨T.ob a.1, isOb_ob hT a.2⟩

/-- Each generator goes to the path of its image. -/
def prefunctor (hS' : S'.WellFormed) (hT : T.Valid S S') : S.Obj ⥤q Paths S'.Obj where
  obj := obj hT
  map {a b} f := S'.pathOf hS' (obj hT a) (obj hT b) (T.gen a.1 f.1) (tgt?_gen hT f.2)

/-- The image of a path: the paths of the images of its generators, composed. -/
def functorPath (hS' : S'.WellFormed) (hT : T.Valid S S') {a b : S.Obj}
    (p : Quiver.Path a b) : Quiver.Path (obj hT a) (obj hT b) :=
  (Paths.lift (prefunctor hS' hT)).map p

theorem names_functorPath (hS' : S'.WellFormed) (hT : T.Valid S S') {a b : S.Obj}
    (p : Quiver.Path a b) :
    Schema.names (functorPath hS' hT p) = T.mapPath S a.1 (Schema.names p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [functorPath, Paths.lift_cons, Schema.names_paths_comp, ← functorPath, ih,
      Schema.names_cons, mapPath_append (Schema.tgt?_names p), mapPath_singleton]
    exact congrArg _ (Schema.names_pathOf _ _ _ _ _)

/-- The functor between schema categories that a valid translation induces. -/
def functor (hS' : S'.WellFormed) (hT : T.Valid S S') : S.cat ⥤ S'.cat :=
  CategoryTheory.Quotient.lift S.rel
    (Paths.lift (prefunctor hS' hT) ⋙ CategoryTheory.Quotient.functor S'.rel) (by
      rintro a b f₁ f₂ ⟨q, hq, ha, h₁, h₂⟩
      change Schema.mor (functorPath hS' hT f₁) = Schema.mor (functorPath hS' hT f₂)
      apply Schema.PathEq.mor_eq
      rw [names_functorPath, names_functorPath, h₁, h₂, ha]
      obtain ⟨hm, hpe⟩ := hT.eqn q hq
      have hobj : obj hT a = ⟨.entity (T.ent q.src), hm⟩ := Subtype.ext (by simp [obj, ha, ob])
      rw [hobj]
      exact hpe)

@[simp] theorem functor_obj (hS' : S'.WellFormed) (hT : T.Valid S S') (a : S.Obj) :
    (functor hS' hT).obj (S.obj a) = S'.obj (obj hT a) := rfl

theorem functor_map_mor (hS' : S'.WellFormed) (hT : T.Valid S S') {a b : S.Obj}
    (p : Quiver.Path a b) :
    (functor hS' hT).map (Schema.mor p) = Schema.mor (functorPath hS' hT p) := rfl

/-- Value types go to themselves. -/
theorem obj_value (hT : T.Valid S S') (v : ValueType) :
    obj hT ⟨.value v, trivial⟩ = ⟨.value v, trivial⟩ := rfl

/-! ## Restriction -/

/-- Restriction `Δ_T` along a translation: precomposition with its functor. -/
def restrict (hS' : S'.WellFormed) (hT : T.Valid S S') : (S'.cat ⥤ Type) ⥤ (S.cat ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj (functor hS' hT)

theorem restrict_obj (hS' : S'.WellFormed) (hT : T.Valid S S') (X : S'.cat ⥤ Type) :
    (restrict hS' hT).obj X = functor hS' hT ⋙ X := rfl

/-! ## The empty translation

The empty translation keeps every name. When it is valid from `S` to `S'`, `S` is
a sub-presentation of `S'`, and its functor is the identity on names. -/

@[simp] theorem ent_empty (e : String) : ({} : Translation).ent e = e := rfl

@[simp] theorem ob_empty (o : Ob) : ({} : Translation).ob o = o := by cases o <;> rfl

@[simp] theorem gen_empty (o : Ob) (n : String) : ({} : Translation).gen o n = [n] := by
  cases o <;> rfl

theorem mapPath_empty : ∀ {o x : Ob} {l : List String}, S.tgt? o l = some x →
    ({} : Translation).mapPath S o l = l
  | _, _, [], _ => rfl
  | o, x, n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      simp [mapPath, hs, mapPath_empty h]

theorem names_functorPath_empty (hS' : S'.WellFormed) (hT : ({} : Translation).Valid S S')
    {a b : S.Obj} (p : Quiver.Path a b) : Schema.names (functorPath hS' hT p) = Schema.names p := by
  rw [names_functorPath, mapPath_empty (Schema.tgt?_names p)]

theorem obj_empty (hT : ({} : Translation).Valid S S') (a : S.Obj) :
    obj hT a = ⟨a.1, ob_empty a.1 ▸ isOb_ob hT a.2⟩ :=
  Subtype.ext (ob_empty _)

end Translation

end DDD
