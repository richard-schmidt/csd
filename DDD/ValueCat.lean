import DDD.Translation
import DDD.Literals

/-!
# Conversions

The value types form a category whose arrows are conversions, presented by the
generators below and a fixed list of equations (`TypeList.Basic`). A conversion
is named, like a generator of a schema, and its name determines it at its
source (`TypeList.conv?`):

- at a plain (not optional) type `v`:
  - `some : v → optional v`;
  - `string : v → string`, the normal form of a value as text, for `v` other than
    `string`;
  - the built-ins `datetime`, `date` and `time` out of `timestamp` (in UTC),
    `date` and `time` out of `datetime`, and `decimal` out of `int`;
  - coercions between a named type and its base, both ways: out of `named m`
    over `b`, the conversion named by `b` (such as `decimal`); out of `b`, the
    conversion named `m`;
  - the tables of the list out of `v`, by their names;
  - out of a record, its fields, the projections;
- at `optional v`: the lift of each conversion `c` out of `v` to a plain type,
  under the name of `c`; absent values stay absent.

No other conversion exists: users do not write functions.

The equations (`Basic`), for each instance and, lifted, at `optional v`:

- a coercion followed by its inverse is the identity;
- two paths of tables out of a finite type with the same target and the same
  images of every value are equal (`tablesFn?`), the empty path included: a
  path of tables is the table it computes;
- `some` commutes with the lifts: `some, c = c, some`;
- `datetime, date = date` and `datetime, time = time` out of `timestamp`;
- a coercion followed by `string` is `string`.

`TypeList.convLit` applies a conversion to a literal in normal form, as the
readers of the exchange format and the Julia side do.
-/

namespace DDD

/-- A plain value type: not optional. -/
def ValueType.isPlain : ValueType → Bool
  | .optional _ => false
  | _ => true

namespace TypeList

variable (L : TypeList)

/-- The base of the named type `n`, when it is declared over a built-in. -/
def base? (n : String) : Option ValueType :=
  match L.lookup n with
  | some (.over b) => some b
  | _ => none

/-- The fields of the record `n`. -/
def fields? (n : String) : Option (List (String × ValueType)) :=
  match L.lookup n with
  | some (.record fs) => some fs
  | _ => none

/-- The table named `n` out of `v`. -/
def table? (v : ValueType) (n : String) : Option Table :=
  L.tables.find? fun t => t.name == n && t.source == v

/-- The built-in conversions other than `some` and `string`. -/
def builtinConv? : ValueType → String → Option ValueType
  | .timestamp, "datetime" => some .datetime
  | .timestamp, "date" => some .date
  | .timestamp, "time" => some .time
  | .datetime, "date" => some .date
  | .datetime, "time" => some .time
  | .int, "decimal" => some .decimal
  | _, _ => none

/-- The coercion named `n` out of `v`: to the base of a named type, or from a base
to a named type over it. -/
def coerce? (v : ValueType) (n : String) : Option ValueType :=
  match v with
  | .named m => match L.base? m with
    | some b => if n = b.text then some b else none
    | none => none
  | _ =>
    if v.isBuiltin then
      match L.base? n with
      | some b => if b = v then some (.named n) else none
      | none => none
    else none

/-- The field named `n` of the record `v`, as its type. -/
def field? (v : ValueType) (n : String) : Option ValueType :=
  match v with
  | .named r => (L.fields? r).bind (·.lookup n)
  | _ => none

/-- The target of the conversion named `n` out of the plain type `v`. -/
def plainConv? (v : ValueType) (n : String) : Option ValueType :=
  if n = "some" then some (.optional v)
  else if n = "string" then (if v = .string then none else some .string)
  else builtinConv? v n <|> L.coerce? v n <|> (L.table? v n).map (·.target) <|> L.field? v n

/-- The target of the conversion named `n` out of `v`: at an optional type, the
lift of a conversion of its base to a plain type. -/
def conv? : ValueType → String → Option ValueType
  | .optional v, n =>
    if v.isPlain then
      match L.plainConv? v n with
      | some w => if w.isPlain then some (.optional w) else none
      | none => none
    else none
  | v, n => L.plainConv? v n

/-- The target of a path of conversions. -/
def convTgt? : ValueType → List String → Option ValueType
  | v, [] => some v
  | v, n :: ns => (L.conv? v n).bind fun w => convTgt? w ns

/-! ## Paths of tables -/

/-- The target of a path of tables. -/
def tablesTgt? : ValueType → List String → Option ValueType
  | v, [] => some v
  | v, n :: ns => (L.table? v n).bind fun t => tablesTgt? t.target ns

/-- The image of the value `x` along a path of tables. -/
def tablesApply? : ValueType → List String → String → Option String
  | _, [], x => some x
  | v, n :: ns, x => (L.table? v n).bind fun t => (t.rows.lookup x).bind (tablesApply? t.target ns)

/-- What a path of tables out of a finite type computes: its target and the image
of each value of its source. -/
def tablesFn? (v : ValueType) (ns : List String) : Option (ValueType × List (Option String)) :=
  (L.values? v).bind fun xs => (L.tablesTgt? v ns).map fun w => (w, xs.map (L.tablesApply? v ns))

/-! ## The equations -/

/-- The equations between paths of conversions out of a value type, each as the
names of its two sides. -/
inductive Basic : ValueType → List String → List String → Prop
  /-- Out of a named type, its base and back is the identity. -/
  | coerceBack {m : String} {b : ValueType} : L.base? m = some b → Basic (.named m) [b.text, m] []
  /-- Out of a base, a named type over it and back is the identity. -/
  | coerceThere {m : String} {b : ValueType} : L.base? m = some b → Basic b [m, b.text] []
  /-- Paths of tables that compute the same function are equal. -/
  | tables {v : ValueType} {ns ns' : List String} :
      (L.tablesFn? v ns).isSome = true → L.tablesFn? v ns = L.tablesFn? v ns' → Basic v ns ns'
  /-- `some` commutes with the lifts. -/
  | some {v w : ValueType} {n : String} : v.isPlain = true → n ≠ "some" →
      L.plainConv? v n = some w → w.isPlain = true → Basic v ["some", n] [n, "some"]
  /-- The date of a timestamp is the date of its date and time. -/
  | date : Basic .timestamp ["datetime", "date"] ["date"]
  /-- The time of a timestamp is the time of its date and time. -/
  | time : Basic .timestamp ["datetime", "time"] ["time"]
  /-- The text of a named type is the text of its base. -/
  | stringBack {m : String} {b : ValueType} : L.base? m = some b →
      Basic (.named m) [b.text, "string"] ["string"]
  /-- The text of a base is the text of a named type over it. -/
  | stringThere {m : String} {b : ValueType} : L.base? m = some b → Basic b [m, "string"] ["string"]
  /-- Each equation holds between the lifts. -/
  | lift {v : ValueType} {l r : List String} : v.isPlain = true → Basic v l r →
      Basic (.optional v) l r

/-! ## Conversions of literals -/

/-- A literal as the text of the conversion `string`: its normal form. -/
def _root_.DDD.Lit.str : Lit → String
  | .text s => s
  | .int i => toString i
  | .bool b => toString b
  | .null => "null"
  | .record fs => Lit.render (.record fs)

/-- A value of a finite type as the text of the rows of tables. -/
def finKey : Lit → Option String
  | .text s => some s
  | .bool b => some (toString b)
  | _ => none

/-- The literal of the value `x` of the finite type `w`. -/
def finLit (w : ValueType) (x : String) : Lit :=
  if w = .bool then .bool (x == "true") else .text x

/-- The conversion named `n` out of the plain type `v`, applied to a literal in
normal form. -/
def plainConvLit (v : ValueType) (n : String) (l : Lit) : Except String Lit :=
  if n = "some" then pure l
  else if n = "string" then pure (.text l.str)
  else match v, n, l with
    | .timestamp, "datetime", .text s => pure (.text (s.dropRight 1))
    | .timestamp, "date", .text s => pure (.text (s.take 10))
    | .timestamp, "time", .text s => pure (.text ((s.drop 11).dropRight 1))
    | .datetime, "date", .text s => pure (.text (s.take 10))
    | .datetime, "time", .text s => pure (.text (s.drop 11))
    | .int, "decimal", .int i => pure (.text (toString i))
    | _, _, _ =>
      if (L.coerce? v n).isSome then pure l
      else match L.table? v n, l with
        | some t, l => match (finKey l).bind fun x => t.rows.lookup x with
          | some y => pure (finLit t.target y)
          | none => throw s!"the table {n} has no row for {l.render}"
        | none, .record fs => match fs.lookup n with
          | some x => pure x
          | none => throw s!"the record {v.text} has no field {n}"
        | none, _ => throw s!"there is no conversion {n} out of {v.text} for {l.render}"

/-- The conversion named `n` out of `v`, applied to a literal in normal form; a
lift keeps an absent value absent. -/
def convLit : ValueType → String → Lit → Except String Lit
  | .optional _, _, .null => pure .null
  | .optional v, n, l => L.plainConvLit v n l
  | v, n, l => L.plainConvLit v n l

/-- A path of conversions applied to a literal in normal form. -/
def applyLit : ValueType → List String → Lit → Except String Lit
  | _, [], l => pure l
  | v, n :: ns, l => match L.conv? v n with
    | some w => do applyLit w ns (← L.convLit v n l)
    | none => throw s!"there is no conversion {n} out of {v.text}"

end TypeList

/-! ## Schemas with conversions -/

/-- The schema without entity types. With conversions, it presents the category of
value types (`TypeList.cat`). -/
def emptySchema : Schema := { entities := [] }

namespace Schema

open CategoryTheory

variable (S : Schema) (L : TypeList)

/-- The generators of `S` out of entity types, and the conversions of `L` out of value
types. -/
def vstep? : Ob → String → Option Ob
  | .entity e, n => S.step? (.entity e) n
  | .value v, n => (L.conv? v n).map .value

/-- The target of a path of generators and conversions. -/
def vtgt? : Ob → List String → Option Ob
  | o, [] => some o
  | o, n :: ns => (S.vstep? L o n).bind fun o' => vtgt? o' ns

@[simp] theorem vtgt?_nil (o : Ob) : S.vtgt? L o [] = some o := rfl

@[simp] theorem vtgt?_cons (o : Ob) (n : String) (ns : List String) :
    S.vtgt? L o (n :: ns) = (S.vstep? L o n).bind fun o' => S.vtgt? L o' ns := rfl

theorem vtgt?_append (o : Ob) (ns ms : List String) :
    S.vtgt? L o (ns ++ ms) = (S.vtgt? L o ns).bind fun o' => S.vtgt? L o' ms := by
  induction ns generalizing o with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.cons_append, vtgt?_cons, ih]
    cases S.vstep? L o n <;> rfl

/-- The objects of `S`, with the generators and the conversions as arrows. -/
@[nolint unusedArguments]
def VObj (S : Schema) (_L : TypeList) : Type := { o : Ob // S.IsOb o }

instance : Quiver (S.VObj L) where
  Hom a b := { n : String // S.vstep? L a.1 n = some b.1 }

variable {S L}

/-- The names along a path of generators and conversions. -/
def vnames {a : S.VObj L} : ∀ {b : S.VObj L}, Quiver.Path a b → List String
  | _, .nil => []
  | _, .cons p e => vnames p ++ [e.1]

@[simp] theorem vnames_nil {a : S.VObj L} : vnames (Quiver.Path.nil : Quiver.Path a a) = [] := rfl

@[simp] theorem vnames_cons {a b c : S.VObj L} (p : Quiver.Path a b) (e : b ⟶ c) :
    vnames (p.cons e) = vnames p ++ [e.1] := rfl

@[simp] theorem vnames_comp {a b c : S.VObj L} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    vnames (p.comp q) = vnames p ++ vnames q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih]

@[simp] theorem vnames_toPath {a b : S.VObj L} (e : a ⟶ b) : vnames e.toPath = [e.1] := rfl

@[simp] theorem vnames_paths_comp {a b c : Paths (S.VObj L)} (p : a ⟶ b) (q : b ⟶ c) :
    vnames (S := S) (L := L) (p ≫ q) = vnames (S := S) (L := L) p ++ vnames (S := S) (L := L) q :=
  vnames_comp p q

theorem vtgt?_vnames {a b : S.VObj L} (p : Quiver.Path a b) :
    S.vtgt? L a.1 (vnames p) = some b.1 := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [vtgt?_append, ih, e.2]

/-- A path is determined by its source and its names. -/
theorem vnames_injective {a : S.VObj L} :
    ∀ {b : S.VObj L} (p q : Quiver.Path a b), vnames p = vnames q → p = q
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons _ _, h => by simp at h
  | _, .cons _ _, .nil, h => by simp at h
  | _, .cons (b := x) p e, .cons (b := y) q e', h => by
    obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
    have hxy : x = y := Subtype.ext <| Option.some.inj <|
      (vtgt?_vnames p).symm.trans (h₁ ▸ vtgt?_vnames q)
    subst hxy
    obtain rfl := vnames_injective p q h₁
    obtain rfl : e = e' := Subtype.ext (List.singleton_inj.mp h₂)
    rfl

variable (S L)

/-- Two paths are related when their names are the two sides of an equation of `S`,
or of an equation between conversions. -/
def vrel : HomRel (Paths (S.VObj L)) := fun a _ f g =>
  (∃ q ∈ S.eqns, a.1 = .entity q.src ∧ vnames f = q.lhs ∧ vnames g = q.rhs) ∨
    (∃ v, a.1 = .value v ∧ L.Basic v (vnames f) (vnames g))

/-- The category `S` presents with the conversions of `L`. -/
def vcat : Cat := Cat.of (CategoryTheory.Quotient (S.vrel L))

/-- The object of `S.vcat L` for an object of `S`. -/
def vobj (a : S.VObj L) : S.vcat L := (CategoryTheory.Quotient.functor (S.vrel L)).obj a

variable {S L}

/-- The morphism of `S.vcat L` a path presents. -/
def vmor {a b : S.VObj L} (p : Quiver.Path a b) : S.vobj L a ⟶ S.vobj L b :=
  (CategoryTheory.Quotient.functor (S.vrel L)).map (X := a) (Y := b) p

@[simp] theorem vmor_nil {a : S.VObj L} :
    vmor (Quiver.Path.nil : Quiver.Path a a) = 𝟙 (S.vobj L a) :=
  (CategoryTheory.Quotient.functor (S.vrel L)).map_id (X := a)

theorem vmor_comp {a b c : S.VObj L} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    vmor (p.comp q) = vmor p ≫ vmor q :=
  (CategoryTheory.Quotient.functor (S.vrel L)).map_comp (X := a) (Y := b) (Z := c) p q

theorem vmor_cons {a b c : S.VObj L} (p : Quiver.Path a b) (e : b ⟶ c) :
    vmor (p.cons e) = vmor p ≫ vmor e.toPath :=
  vmor_comp p e.toPath

/-- Every morphism of `S.vcat L` is presented by a path. -/
theorem vmor_surjective {a b : S.VObj L} (f : S.vobj L a ⟶ S.vobj L b) :
    ∃ p : Quiver.Path a b, vmor p = f :=
  (CategoryTheory.Quotient.functor (S.vrel L)).map_surjective f

variable (S L)

/-- The paths named `l` and `l'` out of `a` exist, are parallel, and present the
same morphism of `S.vcat L`. -/
def VPathEq (a : S.VObj L) (l l' : List String) : Prop :=
  ∃ (b : S.VObj L) (p q : Quiver.Path a b), vnames p = l ∧ vnames q = l' ∧ vmor p = vmor q

variable {S L}

/-- A generator or a conversion ends at an object. -/
theorem isOb_of_vstep? (hS : S.WellFormed) {o o' : Ob} {n : String}
    (h : S.vstep? L o n = some o') : S.IsOb o' := by
  cases o with
  | entity e => exact isOb_of_step? hS (show S.step? (.entity e) n = some o' from h)
  | value v =>
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
    trivial

/-- Every list of names with a target is the list of names of a path. -/
theorem vexists_path (hS : S.WellFormed) :
    ∀ (a : S.VObj L) (l : List String) {o : Ob}, S.vtgt? L a.1 l = some o →
      ∃ (b : S.VObj L) (p : Quiver.Path a b), b.1 = o ∧ vnames p = l
  | a, [], _, h => ⟨a, .nil, Option.some.inj h, rfl⟩
  | a, n :: ns, _, h => by
    obtain ⟨o', h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, p, rfl, rfl⟩ := vexists_path hS ⟨o', isOb_of_vstep? hS h₁⟩ ns h₂
    exact ⟨b, (Quiver.Hom.toPath (show a ⟶ ⟨o', _⟩ from ⟨n, h₁⟩)).comp p, rfl, by simp⟩

/-- In a well-formed schema, the path named `l` from `a` to `b`, given that `l` leads
from `a` to `b`. -/
def vpathOf (hS : S.WellFormed) :
    ∀ (a b : S.VObj L) (l : List String), S.vtgt? L a.1 l = some b.1 → Quiver.Path a b
  | a, b, [], h => (Subtype.ext (Option.some.inj h) : a = b) ▸ Quiver.Path.nil
  | a, b, n :: ns, h =>
    match hs : S.vstep? L a.1 n with
    | none => absurd h (by simp [hs])
    | some o =>
      (Quiver.Hom.toPath (show a ⟶ ⟨o, isOb_of_vstep? hS hs⟩ from ⟨n, hs⟩)).comp
        (vpathOf hS ⟨o, isOb_of_vstep? hS hs⟩ b ns (by simpa [hs] using h))

@[simp] theorem vnames_vpathOf (hS : S.WellFormed) :
    ∀ (a b : S.VObj L) (l : List String) (h : S.vtgt? L a.1 l = some b.1),
      vnames (vpathOf hS a b l h) = l
  | a, b, [], h => by
    obtain rfl : a = b := Subtype.ext (Option.some.inj h)
    rfl
  | a, b, n :: ns, h => by
    unfold vpathOf
    split
    · rename_i hs
      simp [hs] at h
    · simp [vnames_vpathOf]

/-- Paths whose names satisfy `VPathEq` present the same morphism. -/
theorem VPathEq.vmor_eq {a b : S.VObj L} {p q : Quiver.Path a b}
    (h : S.VPathEq L a (vnames p) (vnames q)) : vmor p = vmor q := by
  obtain ⟨b', p', q', hp, hq, hm⟩ := h
  obtain rfl : b' = b :=
    Subtype.ext (Option.some.inj ((vtgt?_vnames p').symm.trans (hp ▸ vtgt?_vnames p)))
  rwa [vnames_injective p' p hp, vnames_injective q' q hq] at hm

theorem VPathEq.refl (hS : S.WellFormed) {a : S.VObj L} {l : List String} {o : Ob}
    (h : S.vtgt? L a.1 l = some o) : S.VPathEq L a l l := by
  obtain ⟨b, p, -, rfl⟩ := vexists_path hS a l h
  exact ⟨b, p, p, rfl, rfl, rfl⟩

theorem VPathEq.symm {a : S.VObj L} {l l' : List String} (h : S.VPathEq L a l l') :
    S.VPathEq L a l' l := by
  obtain ⟨b, p, q, hp, hq, hm⟩ := h
  exact ⟨b, q, p, hq, hp, hm.symm⟩

theorem VPathEq.trans {a : S.VObj L} {l l' l'' : List String} (h : S.VPathEq L a l l')
    (h' : S.VPathEq L a l' l'') : S.VPathEq L a l l'' := by
  obtain ⟨b, p, q, hp, hq, hm⟩ := h
  obtain ⟨b', p', q', hp', hq', hm'⟩ := h'
  obtain rfl : b = b' := Subtype.ext (Option.some.inj
    ((vtgt?_vnames q).symm.trans (hq ▸ hp' ▸ vtgt?_vnames p')))
  obtain rfl := vnames_injective q p' (hq.trans hp'.symm)
  exact ⟨b, p, q', hp, hq', hm.trans hm'⟩

/-- Equal paths stay equal after a common continuation. -/
theorem VPathEq.append_right (hS : S.WellFormed) {a : S.VObj L} {l l' m : List String}
    {o : Ob} (h : S.VPathEq L a l l') (hm : S.vtgt? L a.1 (l ++ m) = some o) :
    S.VPathEq L a (l ++ m) (l' ++ m) := by
  obtain ⟨b, p, q, hp, hq, he⟩ := h
  rw [vtgt?_append, ← hp, vtgt?_vnames, Option.bind_some] at hm
  obtain ⟨c, r, -, hr⟩ := vexists_path hS b m hm
  exact ⟨c, p.comp r, q.comp r, by simp [hp, hr], by simp [hq, hr], by
    rw [vmor_comp, vmor_comp, he]⟩

/-- Equal paths stay equal after a common beginning. -/
theorem VPathEq.append_left (hS : S.WellFormed) {a c : S.VObj L} {l m m' : List String}
    (hl : S.vtgt? L a.1 l = some c.1) (h : S.VPathEq L c m m') :
    S.VPathEq L a (l ++ m) (l ++ m') := by
  obtain ⟨b, p, q, hp, hq, he⟩ := h
  obtain ⟨c', r, hc, hr⟩ := vexists_path hS a l hl
  obtain rfl : c' = c := Subtype.ext hc
  exact ⟨b, r.comp p, r.comp q, by simp [hp, hr], by simp [hq, hr], by
    rw [vmor_comp, vmor_comp, he]⟩

/-- Each equation between conversions holds in `S.vcat L`. -/
theorem VPathEq.of_basic (hS : S.WellFormed) {v : ValueType} {l r : List String} {o : Ob}
    (h : L.Basic v l r) (hl : S.vtgt? L (.value v) l = some o)
    (hr : S.vtgt? L (.value v) r = some o) : S.VPathEq L ⟨.value v, trivial⟩ l r := by
  obtain ⟨b, p, hb, hp⟩ := vexists_path hS (L := L) ⟨.value v, trivial⟩ l hl
  obtain ⟨b', q, hb', hq⟩ := vexists_path hS (L := L) ⟨.value v, trivial⟩ r hr
  obtain rfl : b = b' := Subtype.ext (hb.trans hb'.symm)
  exact ⟨b, p, q, hp, hq, CategoryTheory.Quotient.sound _ (Or.inr ⟨v, rfl, by rwa [hp, hq]⟩)⟩

/-- Two functors out of `S.vcat L` are equal when they agree on objects and on
generators and conversions. -/
theorem vext_functor {X : Type*} [Category X] {F G : S.vcat L ⥤ X}
    (h_obj : ∀ a, F.obj (S.vobj L a) = G.obj (S.vobj L a))
    (h_map : ∀ (a b : S.VObj L) (e : a ⟶ b), F.map (vmor e.toPath) =
      eqToHom (h_obj a) ≫ G.map (vmor e.toPath) ≫ eqToHom (h_obj b).symm) : F = G := by
  apply CategoryTheory.Quotient.lift_unique'
  exact Paths.ext_functor (funext h_obj) h_map

/-! ## The inclusion of `S.cat` -/

/-- A generator of `S` is a generator with conversions. -/
theorem vstep?_of_step? {o o' : Ob} {n : String} (h : S.step? o n = some o') :
    S.vstep? L o n = some o' := by
  cases o with
  | entity e => exact h
  | value v => simp [step?] at h

/-- A path of `S` is a path with conversions. -/
theorem vtgt?_of_tgt? : ∀ {o o' : Ob} {l : List String}, S.tgt? o l = some o' →
    S.vtgt? L o l = some o'
  | _, _, [], h => h
  | o, o', n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some x =>
      simp only [tgt?_cons, hs, Option.bind_some] at h
      simp only [vtgt?_cons, vstep?_of_step? (L := L) hs, Option.bind_some]
      exact vtgt?_of_tgt? h

variable (S L)

/-- Each generator of `S` to itself. -/
def vincPre : S.Obj ⥤q Paths (S.VObj L) where
  obj a := a
  map {a b} e := Quiver.Hom.toPath (show @Quiver.Hom (S.VObj L) _ a b from
    ⟨e.1, vstep?_of_step? e.2⟩)

variable {S L}

theorem vnames_vincPath {a b : S.Obj} (p : Quiver.Path a b) :
    vnames ((Paths.lift (S.vincPre L)).map p) = names p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Paths.lift_cons, vnames_paths_comp, ih]
    rfl

variable (S L)

/-- The inclusion of the category of `S` into the category of `S` with conversions:
the identity on objects and on generators. -/
def vinc : S.cat ⥤ S.vcat L :=
  CategoryTheory.Quotient.lift S.rel
    (Paths.lift (S.vincPre L) ⋙ CategoryTheory.Quotient.functor (S.vrel L)) (by
      rintro a b f g ⟨q, hq, ha, hf, hg⟩
      exact CategoryTheory.Quotient.sound _
        (Or.inl ⟨q, hq, ha, by rw [vnames_vincPath, hf], by rw [vnames_vincPath, hg]⟩))

variable {S L}

@[simp] theorem vinc_obj (a : S.Obj) : (S.vinc L).obj (S.obj a) = S.vobj L a := rfl

theorem vinc_map_mor {a b : S.Obj} (p : Quiver.Path a b) :
    (S.vinc L).map (mor p) = vmor ((Paths.lift (S.vincPre L)).map p) := rfl

/-- What is equal in `S.cat` is equal with conversions. -/
theorem VPathEq.of_pathEq {a : S.Obj} {l l' : List String} (h : S.PathEq a l l') :
    S.VPathEq L a l l' := by
  obtain ⟨b, p, q, hp, hq, hm⟩ := h
  refine ⟨b, (Paths.lift (S.vincPre L)).map p, (Paths.lift (S.vincPre L)).map q,
    by rw [vnames_vincPath, hp], by rw [vnames_vincPath, hq], ?_⟩
  rw [← vinc_map_mor, ← vinc_map_mor, hm]

end Schema

/-! ## The category of value types -/

namespace TypeList

open CategoryTheory

/-- The category of value types: the objects are the value types, the arrows the
conversions of `L`, subject to the equations `Basic`. -/
def cat (L : TypeList) : Cat := emptySchema.vcat L

end TypeList

namespace Schema

open CategoryTheory

variable {S : Schema} {L : TypeList}

theorem isOb_of_empty {o : Ob} (h : emptySchema.IsOb o) : S.IsOb o := by
  cases o with
  | entity e => exact absurd h (by simp [IsOb, emptySchema])
  | value v => trivial

theorem vstep?_of_empty {o o' : Ob} {n : String} (h : emptySchema.vstep? L o n = some o') :
    S.vstep? L o n = some o' := by
  cases o with
  | entity e => simp [vstep?, step?, ref?, attr?, emptySchema] at h
  | value v => exact h

variable (S L)

/-- Each conversion to itself. -/
def vvalsPre : emptySchema.VObj L ⥤q Paths (S.VObj L) where
  obj a := ⟨a.1, isOb_of_empty a.2⟩
  map {a b} e := Quiver.Hom.toPath (show @Quiver.Hom (S.VObj L) _ ⟨a.1, isOb_of_empty a.2⟩
    ⟨b.1, isOb_of_empty b.2⟩ from ⟨e.1, vstep?_of_empty e.2⟩)

variable {S L}

theorem vnames_vvalsPath {a b : emptySchema.VObj L} (p : Quiver.Path a b) :
    vnames ((Paths.lift (S.vvalsPre L)).map p) = vnames p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Paths.lift_cons, vnames_paths_comp, ih]
    rfl

variable (S L)

/-- The category of value types in the category of `S` with conversions: the
value types and the conversions, to themselves. -/
def vvals : L.cat ⥤ S.vcat L :=
  CategoryTheory.Quotient.lift (emptySchema.vrel L)
    (Paths.lift (S.vvalsPre L) ⋙ CategoryTheory.Quotient.functor (S.vrel L)) (by
      rintro a b f g (⟨q, hq, -⟩ | ⟨v, ha, h⟩)
      · simp [emptySchema] at hq
      · exact CategoryTheory.Quotient.sound _
          (Or.inr ⟨v, ha, by rwa [vnames_vvalsPath, vnames_vvalsPath]⟩))

end Schema

/-! ## Translations -/

namespace Translation

open CategoryTheory Schema

variable {S S' : Schema} {L : TypeList} (T : Translation)

/-- The image of the path `l` out of `o`, generators and conversions. -/
def vmapPath (S : Schema) (L : TypeList) : Ob → List String → List String
  | _, [] => []
  | o, n :: ns =>
    T.gen o n ++ match S.vstep? L o n with
      | some o' => vmapPath S L o' ns
      | none => []

theorem vmapPath_append {o x : Ob} {l : List String} (h : S.vtgt? L o l = some x)
    (m : List String) : T.vmapPath S L o (l ++ m) = T.vmapPath S L o l ++ T.vmapPath S L x m := by
  induction l generalizing o with
  | nil => simp only [vtgt?_nil, Option.some.injEq] at h; subst h; simp [vmapPath]
  | cons n ns ih =>
    cases hs : S.vstep? L o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [vtgt?_cons, hs, Option.bind_some] at h
      simp [vmapPath, hs, ih h]

/-- On a path of `S`, the image with conversions is the image. -/
theorem vmapPath_of_tgt? : ∀ {o x : Ob} {l : List String}, S.tgt? o l = some x →
    T.vmapPath S L o l = T.mapPath S o l
  | _, _, [], _ => rfl
  | o, x, n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [tgt?_cons, hs, Option.bind_some] at h
      simp [vmapPath, mapPath, hs, vstep?_of_step? (L := L) hs, vmapPath_of_tgt? h]

/-- Out of a value type, the image of a path of conversions is the path. -/
theorem vmapPath_value : ∀ {v : ValueType} {x : Ob} {l : List String},
    S.vtgt? L (.value v) l = some x → T.vmapPath S L (.value v) l = l
  | _, _, [], _ => rfl
  | v, x, n :: ns, h => by
    cases hc : L.conv? v n with
    | none => simp [vstep?, hc] at h
    | some w =>
      simp only [vtgt?_cons, vstep?, hc, Option.map_some, Option.bind_some] at h
      simp [vmapPath, gen, vstep?, hc, vmapPath_value h]

/-- A generator or a conversion goes to a path between the images of its ends. -/
theorem vtgt?_gen (hT : T.Valid S S') {o o' : Ob} {n : String} (h : S.vstep? L o n = some o') :
    S'.vtgt? L (T.ob o) (T.gen o n) = some (T.ob o') := by
  cases o with
  | entity e => exact vtgt?_of_tgt? (tgt?_gen hT (show S.step? (.entity e) n = some o' from h))
  | value v =>
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [ob, gen, vstep?, hw]

/-- The image of an object, with conversions. -/
def vobj (hT : T.Valid S S') (a : S.VObj L) : S'.VObj L := ⟨T.ob a.1, isOb_ob hT a.2⟩


theorem vmapPath_singleton (o : Ob) (n : String) : T.vmapPath S L o [n] = T.gen o n := by
  simp only [vmapPath]
  cases S.vstep? L o n <;> simp

/-- Each generator and conversion goes to the path of its image. -/
def vprefunctor (hS' : S'.WellFormed) (hT : T.Valid S S') : S.VObj L ⥤q Paths (S'.VObj L) where
  obj := T.vobj hT
  map {a b} f := S'.vpathOf hS' (T.vobj hT a) (T.vobj hT b) (T.gen a.1 f.1) (T.vtgt?_gen hT f.2)

/-- The image of a path of generators and conversions. -/
def vfunctorPath (hS' : S'.WellFormed) (hT : T.Valid S S') {a b : S.VObj L}
    (p : Quiver.Path a b) : Quiver.Path (T.vobj hT a) (T.vobj hT b) :=
  (Paths.lift (T.vprefunctor hS' hT)).map p

theorem vnames_vfunctorPath (hS' : S'.WellFormed) (hT : T.Valid S S') {a b : S.VObj L}
    (p : Quiver.Path a b) : vnames (T.vfunctorPath hS' hT p) = T.vmapPath S L a.1 (vnames p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [vfunctorPath, Paths.lift_cons, vnames_paths_comp, ← vfunctorPath, ih, vnames_cons,
      vmapPath_append T (vtgt?_vnames p), vmapPath_singleton]
    exact congrArg _ (vnames_vpathOf _ _ _ _ _)

/-- The functor between the categories with conversions that a valid translation
induces: the images of the generators, and each conversion to itself. -/
def vfunctor (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S.vcat L ⥤ S'.vcat L :=
  CategoryTheory.Quotient.lift (S.vrel L)
    (Paths.lift (T.vprefunctor hS' hT) ⋙ CategoryTheory.Quotient.functor (S'.vrel L)) (by
      rintro a b f₁ f₂ (⟨q, hq, ha, h₁, h₂⟩ | ⟨v, ha, h⟩)
      · change vmor (T.vfunctorPath hS' hT f₁) = vmor (T.vfunctorPath hS' hT f₂)
        apply VPathEq.vmor_eq
        obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
        rw [vnames_vfunctorPath, vnames_vfunctorPath, h₁, h₂, ha, T.vmapPath_of_tgt? hl,
          T.vmapPath_of_tgt? hr]
        obtain ⟨hm, hpe⟩ := hT.eqn q hq
        have hobj : T.vobj hT a = ⟨.entity (T.ent q.src), hm⟩ := Subtype.ext (by
          simp [vobj, ha, ob])
        rw [hobj]
        exact VPathEq.of_pathEq hpe
      · change vmor (T.vfunctorPath hS' hT f₁) = vmor (T.vfunctorPath hS' hT f₂)
        apply CategoryTheory.Quotient.sound
        have hv : (T.vobj hT a).1 = .value v := by simp [vobj, ha, ob]
        have t₁ := vtgt?_vnames f₁
        have t₂ := vtgt?_vnames f₂
        rw [ha] at t₁ t₂
        exact Or.inr ⟨v, hv, by
          rw [vnames_vfunctorPath, vnames_vfunctorPath, ha, T.vmapPath_value t₁,
            T.vmapPath_value t₂]
          exact h⟩)

theorem vfunctor_map_vmor (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    {a b : S.VObj L} (p : Quiver.Path a b) :
    (T.vfunctor hS hS' hT).map (vmor p) = vmor (T.vfunctorPath hS' hT p) := rfl

/-- With conversions, the functor of a translation extends its functor. -/
theorem vinc_comp_vfunctor (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S.vinc L ⋙ T.vfunctor hS hS' hT = T.functor hS' hT ⋙ S'.vinc L := by
  refine Schema.ext_functor (fun a => rfl) fun a b e => ?_
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [vinc_map_mor, vfunctor_map_vmor, functor_map_mor, vinc_map_mor]
  congr 1
  apply vnames_injective
  rw [vnames_vfunctorPath, vnames_vincPath, vnames_vincPath, names_functorPath]
  simp only [names_toPath, vmapPath_singleton, mapPath_singleton]
  rfl

/-- Translations are the identity on the category of value types. -/
theorem vvals_comp_vfunctor (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S') :
    S.vvals L ⋙ T.vfunctor hS hS' hT = S'.vvals L := by
  have hob : ∀ a : emptySchema.VObj L, T.ob a.1 = a.1 := by
    rintro ⟨⟨e⟩ | ⟨v⟩, h⟩
    · exact absurd h (by simp [IsOb, emptySchema])
    · rfl
  refine Schema.vext_functor (fun a => congrArg (S'.vobj L) (Subtype.ext (hob a)))
    fun a b e => ?_
  obtain ⟨⟨ea⟩ | ⟨v⟩, ha⟩ := a
  · exact absurd ha (by simp [IsOb, emptySchema])
  obtain ⟨⟨eb⟩ | ⟨w⟩, hb⟩ := b
  · exact absurd hb (by simp [IsOb, emptySchema])
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map]
  change vmor (T.vfunctorPath hS' hT ((Paths.lift (S.vvalsPre L)).map e.toPath)) =
    vmor ((Paths.lift (S'.vvalsPre L)).map e.toPath)
  congr 1
  apply vnames_injective
  rw [vnames_vfunctorPath, vnames_vvalsPath, vnames_vvalsPath, vnames_toPath,
    vmapPath_singleton]
  rfl

end Translation

end DDD
