import DDD.Values
import Mathlib.Data.List.Dedup

/-!
# Literals and the list of value types

The exchange format writes the values of finite states as literals (`Lit`): JSON
integers, strings, booleans and `null`. A model declares its project-defined
value types in one list (`TypeList`), shared by all its contexts: an enumeration
with its values, or a named type over a built-in.

- `TypeList.Sound`: each name declared once and different from the names of the
  built-ins, each enumeration with at least one value and no value twice, each
  base a built-in. `checkSound` decides it (`checkSound_iff`), and
  `TypeList.problems` lists its failures, none exactly when it holds
  (`problems_eq_nil_iff`).
- `TypeList.admits`: the value types an attribute can have: the built-ins, the
  declared names, and `optional v` for an admitted `v` that is not itself
  optional. `undeclared?` and `ValueType.nested` say why a type is not
  admitted (`admits_iff`).
- Normal forms (`TypeList.normalize`): each value type has one written form per
  value. `normalize` parses a literal and returns that form, or a sentence that
  says why the literal is not a value of the type:
  - `decimal`: digits with an optional sign and decimal point, without a
    leading `+`, leading zeros, or trailing zeros after the point (`1.50` is
    `1.5`); a JSON integer is accepted;
  - `date`: `YYYY-MM-DD`, a day of the proleptic Gregorian calendar;
  - `time`: `HH:MM:SS`, seconds always written, a fraction of a second without
    trailing zeros (`09:30` is `09:30:00`);
  - `datetime`: a date and a time separated by `T`, without time zone (a space
    or `t` is read as `T`);
  - `timestamp`: a date and a time with a time zone, `Z` or an offset, written
    in UTC with `Z` (`2026-11-04T09:30:00+01:00` is `2026-11-04T08:30:00Z`);
  - `duration`: `P` with days, hours, minutes and seconds, weeks read as seven
    days, hours below 24 and minutes and seconds below 60 (`PT90M` is
    `PT1H30M`, the zero duration `PT0S`); months and years are refused, since
    they have no fixed length;
  - `uuid`: lower case, with hyphens;
  - `int`, `string`, `bool`: JSON integers, strings and booleans as they are;
  - a declared enumeration: one of its values, as written; a named type over a
    built-in: the normal form of the built-in;
  - `optional v`: `null`, or a literal of `v`.

Two literals of a type in normal form are equal exactly when they denote the
same value. The normalizers belong to the reader of the exchange format, as the
JSON parser does: `Examples/Literals.lean` tests them on examples.
-/

namespace DDD

/-- The elements of `l` that occur more than once, each listed once. -/
def dups (l : List String) : List String := (l.filter fun x => 1 < l.count x).dedup

theorem dups_eq_nil_iff (l : List String) : dups l = [] ↔ l.Nodup := by
  rw [dups, List.dedup_eq_nil, List.filter_eq_nil_iff, List.nodup_iff_count_le_one]
  constructor
  · intro h a
    by_cases ha : a ∈ l
    · simpa using h a ha
    · simp [List.count_eq_zero_of_not_mem ha]
  · intro h a _
    simpa using h a

/-! ## Value types as text -/

def ValueType.text : ValueType → String
  | .int => "int"
  | .decimal => "decimal"
  | .string => "string"
  | .date => "date"
  | .uuid => "uuid"
  | .bool => "bool"
  | .datetime => "datetime"
  | .timestamp => "timestamp"
  | .time => "time"
  | .duration => "duration"
  | .named n => n
  | .optional v => "optional " ++ v.text

/-- The built-in value types: neither named nor optional. -/
def ValueType.isBuiltin : ValueType → Bool
  | .named _ | .optional _ => false
  | _ => true

/-- `optional` applied to an optional type. -/
def ValueType.nested : ValueType → Bool
  | .optional (.optional _) => true
  | _ => false

/-- The names of the built-in value types, and `optional`. No declared type takes
one of them, so a name in text always means one type. -/
def builtinNames : List String :=
  ["int", "decimal", "string", "date", "uuid", "bool", "datetime", "timestamp", "time",
    "duration", "optional"]

/-! ## Literals -/

/-- A literal value: the values of finite states in the exchange format. Decimals,
dates, times, UUIDs and the values of named types are written as text; `null` is
the absent value of an optional type. -/
inductive Lit where
  | int (i : Int)
  | text (s : String)
  | bool (b : Bool)
  | null
deriving DecidableEq, Repr

/-- A literal as text, for messages. -/
def Lit.render : Lit → String
  | .int i => toString i
  | .text s => s
  | .bool b => toString b
  | .null => "null"

/-! ## The list of value types -/

/-- The declaration of a project-defined value type: an enumeration with its
values, or a named type over a built-in. -/
inductive TypeDecl where
  | enum (values : List String)
  | over (base : ValueType)
deriving DecidableEq, Repr

/-- A declaration is sound: an enumeration has a value and no value twice, a base
is a built-in. -/
def TypeDecl.Sound : TypeDecl → Prop
  | .enum vs => vs ≠ [] ∧ vs.Nodup
  | .over b => b.isBuiltin = true

instance : (d : TypeDecl) → Decidable d.Sound
  | .enum vs => inferInstanceAs (Decidable (vs ≠ [] ∧ vs.Nodup))
  | .over b => inferInstanceAs (Decidable (b.isBuiltin = true))

/-- The project-defined value types of a model, by name. -/
structure TypeList where
  decls : List (String × TypeDecl) := []
deriving DecidableEq, Repr

namespace TypeList

variable (L : TypeList)

/-- The declaration of the type named `n`. -/
def lookup (n : String) : Option TypeDecl := L.decls.lookup n

/-- The list is sound: names declared once and different from the built-ins, and
every declaration sound. -/
structure Sound : Prop where
  nodup : (L.decls.map (·.1)).Nodup
  notBuiltin : ∀ d ∈ L.decls, d.1 ∉ builtinNames
  decl : ∀ d ∈ L.decls, d.2.Sound

/-- The check for `Sound`. -/
def checkSound : Bool :=
  decide (L.decls.map (·.1)).Nodup &&
    L.decls.all fun d => decide (d.1 ∉ builtinNames) && decide d.2.Sound

theorem checkSound_iff : L.checkSound = true ↔ L.Sound := by
  simp only [checkSound, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun d hd => (h₂ d hd).1, fun d hd => (h₂ d hd).2⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, fun d hd => ⟨h₂ d hd, h₃ d hd⟩⟩

/-- A failure of a condition of `Sound`. -/
inductive Problem where
  /-- The name `n` is declared more than once. -/
  | duplicateType (n : String)
  /-- The name `n` is the name of a built-in. -/
  | builtinName (n : String)
  /-- The enumeration `n` has no value. -/
  | emptyEnum (n : String)
  /-- The enumeration `n` lists `v` more than once. -/
  | duplicateValue (n v : String)
  /-- The named type `n` is declared over `b`, which is not a built-in. -/
  | baseNotBuiltin (n : String) (b : ValueType)
deriving DecidableEq, Repr

/-- The failures of one declaration. -/
def declProblems (d : String × TypeDecl) : List Problem :=
  (if d.1 ∈ builtinNames then [.builtinName d.1] else []) ++
    match d.2 with
    | .enum vs => (if vs = [] then [.emptyEnum d.1] else []) ++ (dups vs).map (.duplicateValue d.1)
    | .over b => if b.isBuiltin then [] else [.baseNotBuiltin d.1 b]

/-- The failures of the conditions of `Sound`, in their order. -/
def problems : List Problem :=
  (dups (L.decls.map (·.1))).map .duplicateType ++ L.decls.flatMap declProblems

theorem declProblems_eq_nil_iff (d : String × TypeDecl) :
    declProblems d = [] ↔ d.1 ∉ builtinNames ∧ d.2.Sound := by
  obtain ⟨n, d⟩ := d
  cases d with
  | enum vs => simp [declProblems, TypeDecl.Sound, dups_eq_nil_iff]
  | over b => simp [declProblems, TypeDecl.Sound]

theorem problems_eq_nil_iff : L.problems = [] ↔ L.Sound := by
  simp only [problems, List.append_eq_nil_iff, List.map_eq_nil_iff, dups_eq_nil_iff,
    List.flatMap_eq_nil_iff, declProblems_eq_nil_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun d hd => (h₂ d hd).1, fun d hd => (h₂ d hd).2⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, fun d hd => ⟨h₂ d hd, h₃ d hd⟩⟩

namespace Problem

def describe : Problem → String
  | .duplicateType n => s!"the value type {n} is declared more than once"
  | .builtinName n => s!"{n} is the name of a built-in value type"
  | .emptyEnum n => s!"the enumeration {n} has no value"
  | .duplicateValue n v => s!"the enumeration {n} lists {v} more than once"
  | .baseNotBuiltin n b =>
    s!"the value type {n} is declared over {b.text}; a named type is declared over a built-in"

def kind : Problem → String
  | .duplicateType .. => "duplicateValueType"
  | .builtinName .. => "builtinTypeName"
  | .emptyEnum .. => "emptyEnumeration"
  | .duplicateValue .. => "duplicateEnumerationValue"
  | .baseNotBuiltin .. => "baseNotBuiltin"

end Problem

/-! ## Admitted value types -/

/-- The value types an attribute can have: the built-ins, the declared names, and
`optional v` for an admitted `v` that is not optional. -/
def admits : ValueType → Bool
  | .named n => (L.lookup n).isSome
  | .optional (.optional _) => false
  | .optional v => admits v
  | _ => true

/-- The undeclared name in a value type, if there is one. -/
def undeclared? : ValueType → Option String
  | .named n => if (L.lookup n).isSome then none else some n
  | .optional v => undeclared? v
  | _ => none

theorem admits_iff (v : ValueType) :
    L.admits v = true ↔ L.undeclared? v = none ∧ v.nested = false := by
  cases v with
  | optional w =>
    cases w with
    | optional u => simp [admits, ValueType.nested]
    | named n =>
      simp only [admits, undeclared?, ValueType.nested, and_true]
      cases L.lookup n <;> simp
    | _ => simp [admits, undeclared?, ValueType.nested]
  | named n =>
    simp only [admits, undeclared?, ValueType.nested, and_true]
    cases L.lookup n <;> simp
  | _ => simp [admits, undeclared?, ValueType.nested]

end TypeList

/-! ## Normal forms -/

namespace Norm

def natOf (cs : List Char) : Nat := cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

def isDigits (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

def dropZerosRight (cs : List Char) : List Char := (cs.reverse.dropWhile (· == '0')).reverse

/-- `n` in decimal, padded with zeros to `w` digits. -/
def pad (w n : Nat) : String :=
  let s := toString n
  (String.ofList (List.replicate (w - s.length) '0')) ++ s

def fracText (f : List Char) : String := if f.isEmpty then "" else "." ++ String.ofList f

/-- The normal form of a decimal. -/
def decimal (s : String) : Except String String := do
  let (neg, rest) := match s.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let (ip, tail) := rest.span (· != '.')
  let fp := tail.drop 1
  unless ip.all Char.isDigit && fp.all Char.isDigit && (!ip.isEmpty || !fp.isEmpty) do
    throw s!"{s} is not a decimal: write digits with an optional sign and decimal point, \
      such as -12.5"
  let ip' := match ip.dropWhile (· == '0') with
    | [] => ['0']
    | r => r
  let fp' := dropZerosRight fp
  let zero := ip' == ['0'] && fp'.isEmpty
  pure ((if neg && !zero then "-" else "") ++ String.ofList ip' ++ fracText fp')

def isLeap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeap y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- Year, month and day of `YYYY-MM-DD`. -/
def parseDate : List Char → Option (Nat × Nat × Nat)
  | [y₁, y₂, y₃, y₄, '-', m₁, m₂, '-', d₁, d₂] =>
    if isDigits [y₁, y₂, y₃, y₄, m₁, m₂, d₁, d₂] then
      let y := natOf [y₁, y₂, y₃, y₄]
      let m := natOf [m₁, m₂]
      let d := natOf [d₁, d₂]
      if 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m then some (y, m, d) else none
    else none
  | _ => none

def dateText (y m d : Nat) : String := pad 4 y ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d

/-- Hours, minutes and seconds within range, and the digits of the fraction of a
second without trailing zeros. -/
def hms (h m s f : List Char) : Option (Nat × Nat × Nat × List Char) :=
  if isDigits (h ++ m ++ s) && natOf h < 24 && natOf m < 60 && natOf s < 60 then
    some (natOf h, natOf m, natOf s, dropZerosRight f)
  else none

/-- `HH:MM`, `HH:MM:SS`, or `HH:MM:SS` with a fraction after `.` or `,`. -/
def parseTime : List Char → Option (Nat × Nat × Nat × List Char)
  | [h₁, h₂, ':', m₁, m₂] => hms [h₁, h₂] [m₁, m₂] ['0', '0'] []
  | h₁ :: h₂ :: ':' :: m₁ :: m₂ :: ':' :: s₁ :: s₂ :: rest =>
    match rest with
    | [] => hms [h₁, h₂] [m₁, m₂] [s₁, s₂] []
    | c :: f =>
      if (c == '.' || c == ',') && isDigits f then hms [h₁, h₂] [m₁, m₂] [s₁, s₂] f
      else none
  | _ => none

def timeText (h m s : Nat) (f : List Char) : String :=
  pad 2 h ++ ":" ++ pad 2 m ++ ":" ++ pad 2 s ++ fracText f

/-- The normal form of a date. -/
def date (s : String) : Except String String :=
  match parseDate s.toList with
  | some (y, m, d) => pure (dateText y m d)
  | none => throw s!"{s} is not a date: write YYYY-MM-DD, a day of the calendar"

/-- The normal form of a time of day. -/
def time (s : String) : Except String String :=
  match parseTime s.toList with
  | some (h, m, sec, f) => pure (timeText h m sec f)
  | none => throw s!"{s} is not a time: write HH:MM:SS, hours below 24"

/-- The date and the rest of a date and time, separated by `T`, `t` or a space. -/
def splitDateTime (cs : List Char) : Option (List Char × List Char) :=
  match cs.drop 10 with
  | c :: rest => if c == 'T' || c == 't' || c == ' ' then some (cs.take 10, rest) else none
  | [] => none

def hasZone (cs : List Char) : Bool := cs.any fun c => c == 'Z' || c == 'z' || c == '+' || c == '-'

/-- The normal form of a date and time without time zone. -/
def datetime (s : String) : Except String String := do
  let err := s!"{s} is not a datetime: write YYYY-MM-DDTHH:MM:SS, without time zone"
  let some (dcs, tcs) := splitDateTime s.toList | throw err
  if hasZone tcs then
    throw s!"{s} is not a datetime: a datetime has no time zone, a timestamp has one"
  let some (y, m, d) := parseDate dcs | throw err
  let some (h, mi, sec, f) := parseTime tcs | throw err
  pure (dateText y m d ++ "T" ++ timeText h mi sec f)

/-- An offset from UTC, `HH:MM`, `HHMM` or `HH`, in minutes. -/
def offset : List Char → Option Nat
  | [a, b, ':', c, d] | [a, b, c, d] =>
    if isDigits [a, b, c, d] && natOf [a, b] < 24 && natOf [c, d] < 60 then
      some (natOf [a, b] * 60 + natOf [c, d])
    else none
  | [a, b] => if isDigits [a, b] && natOf [a, b] < 24 then some (natOf [a, b] * 60) else none
  | _ => none

/-- The time and the offset from UTC in minutes of a time with a time zone. -/
def splitZone (cs : List Char) : Option (List Char × Int) :=
  match cs.reverse with
  | 'Z' :: r | 'z' :: r => some (r.reverse, 0)
  | _ =>
    match cs.span fun c => c != '+' && c != '-' with
    | (t, sgn :: o) => (offset o).map fun n => (t, if sgn == '-' then -(n : Int) else n)
    | (_, []) => none

/-- The number of days from 1970-01-01 to a day of the proleptic Gregorian
calendar. -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The day `z` days after 1970-01-01, as year, month and day. -/
def civilFromDays (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- The normal form of a timestamp: in UTC, with `Z`. -/
def timestamp (s : String) : Except String String := do
  let err := s!"{s} is not a timestamp: write YYYY-MM-DDTHH:MM:SS with a time zone, \
    such as Z for UTC or +01:00"
  let some (dcs, rest) := splitDateTime s.toList | throw err
  let some (tcs, off) := splitZone rest
    | if hasZone rest then throw err
      else throw s!"{s} is not a timestamp: a timestamp has a time zone, such as Z for UTC"
  let some (y, m, d) := parseDate dcs | throw err
  let some (h, mi, sec, f) := parseTime tcs | throw err
  let total : Int := ((h * 60 + mi : Nat) : Int) - off
  let mins := total % 1440
  let (y', m', d') := civilFromDays (daysFromCivil y m d + total / 1440)
  unless 0 ≤ y' ∧ y' ≤ 9999 do
    throw s!"{s} is not a timestamp: its year in UTC is not between 0000 and 9999"
  pure (dateText y'.toNat m'.toNat d'.toNat ++ "T" ++
    timeText (mins / 60).toNat (mins % 60).toNat sec f ++ "Z")

/-- The components of a duration: the characters of each number and its unit. -/
def components (cs : List Char) : Option (List (List Char × Char)) :=
  let step : Option (List (List Char × Char) × List Char) → Char →
      Option (List (List Char × Char) × List Char)
    | none, _ => none
    | some (acc, num), c =>
      if c.isDigit || c == '.' || c == ',' then some (acc, num ++ [c])
      else if num.isEmpty then none
      else some (acc ++ [(num, c)], [])
  match cs.foldl step (some ([], [])) with
  | some (acc, []) => some acc
  | _ => none

/-- `units` lists some of `allowed`, in their order, each at most once. -/
def inOrder : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | u :: us, a :: as => if u == a then inOrder us as else inOrder (u :: us) as

/-- A number of a duration: its whole part and the digits of its fraction. -/
def durationNumber (num : List Char) : Option (Nat × List Char) :=
  match num.span Char.isDigit with
  | (ip, []) => if isDigits ip then some (natOf ip, []) else none
  | (ip, c :: f) =>
    if (c == '.' || c == ',') && isDigits ip && isDigits f then some (natOf ip, f) else none

def unitSeconds : Char → Nat
  | 'W' => 604800
  | 'D' => 86400
  | 'H' => 3600
  | 'M' => 60
  | _ => 1

/-- The normal form of a duration. -/
def duration (s : String) : Except String String := do
  let err := s!"{s} is not a duration: write P with days, hours, minutes and seconds, \
    such as P1DT2H30M or PT90S"
  let 'P' :: body := s.toList.map Char.toUpper | throw err
  let (dpart, ttail) := body.span (· != 'T')
  let tpart := ttail.drop 1
  if !ttail.isEmpty && tpart.isEmpty then throw err
  let some dc := components dpart | throw err
  let some tc := components tpart | throw err
  if dc.isEmpty && tc.isEmpty then throw err
  if dc.any fun c => c.2 == 'Y' || c.2 == 'M' then
    throw s!"{s} is not a duration: months and years have no fixed length; write days, \
      or declare a named type"
  unless inOrder (dc.map (·.2)) ['W', 'D'] && inOrder (tc.map (·.2)) ['H', 'M', 'S'] do throw err
  let mut total := 0
  let mut frac : List Char := []
  for (num, u) in dc ++ tc do
    let some (n, f) := durationNumber num | throw err
    if !f.isEmpty && u != 'S' then
      throw s!"{s} is not a duration: only the seconds take a fraction"
    total := total + n * unitSeconds u
    frac := f
  let f := dropZerosRight frac
  let days := total / 86400
  let r := total % 86400
  let h := r / 3600
  let mi := r % 3600 / 60
  let sec := r % 60
  let tp := (if h > 0 then s!"{h}H" else "") ++ (if mi > 0 then s!"{mi}M" else "") ++
    (if sec > 0 || !f.isEmpty then s!"{sec}{fracText f}S" else "")
  let out := "P" ++ (if days > 0 then s!"{days}D" else "") ++ (if tp.isEmpty then "" else "T" ++ tp)
  pure (if out == "P" then "PT0S" else out)

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The normal form of a UUID: lower case, hyphens after 8, 12, 16 and 20 digits. -/
def uuid (s : String) : Except String String := do
  let cs := s.toList.map Char.toLower
  let hyphens := [8, 13, 18, 23]
  let hyphenated := cs.length == 36 && (List.range 36).all fun i =>
    if i ∈ hyphens then cs[i]? == some '-' else (cs[i]?.map isHex) == some true
  let plain := cs.length == 32 && cs.all isHex
  unless hyphenated || plain do
    throw s!"{s} is not a UUID: write 32 hexadecimal digits in groups of 8, 4, 4, 4 and 12"
  let hs := cs.filter (· != '-')
  let group (i n : Nat) : String := String.ofList ((hs.drop i).take n)
  pure ("-".intercalate [group 0 8, group 8 4, group 12 4, group 16 4, group 20 12])

end Norm

/-- The normal form of a literal of a built-in value type. -/
def normalizeBuiltin : ValueType → Lit → Except String Lit
  | .int, .int i => pure (.int i)
  | .bool, .bool b => pure (.bool b)
  | .string, .text s => pure (.text s)
  | .decimal, .int i => pure (.text (toString i))
  | .decimal, .text s => .text <$> Norm.decimal s
  | .date, .text s => .text <$> Norm.date s
  | .uuid, .text s => .text <$> Norm.uuid s
  | .datetime, .text s => .text <$> Norm.datetime s
  | .timestamp, .text s => .text <$> Norm.timestamp s
  | .time, .text s => .text <$> Norm.time s
  | .duration, .text s => .text <$> Norm.duration s
  | v, .null => throw s!"the value is missing, and {v.text} is not optional"
  | v, l => throw s!"{l.render} is not a value of {v.text}"

/-- The normal form of a literal of a value type, given the list of value types. -/
def TypeList.normalize (L : TypeList) : ValueType → Lit → Except String Lit
  | .named n, l => match L.lookup n with
    | none => throw s!"the value type {n} is not declared"
    | some (.enum vs) => match l with
      | .text s =>
        if s ∈ vs then pure (.text s)
        else throw s!"{s} is not a value of {n}, whose values are {", ".intercalate vs}"
      | .null => throw s!"the value is missing, and {n} is not optional"
      | l => throw s!"{l.render} is not a value of {n}"
    | some (.over b) =>
      if b.isBuiltin then normalizeBuiltin b l
      else throw s!"the value type {n} is declared over {b.text}, which is not a built-in"
  | .optional (.optional _), _ => throw "a value type is optional at most once"
  | .optional _, .null => pure .null
  | .optional v, l => L.normalize v l
  | v, l => normalizeBuiltin v l

end DDD
