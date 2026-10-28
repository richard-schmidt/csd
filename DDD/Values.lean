import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Value types

The value types shared by all bounded contexts, and their interpretation
`K : ValueType → Type`. An attribute of a schema ends in a value type, and a state
sends each value type `v` to `K v`. Translations leave value types unchanged.

Per-model checks compare values, so every `K v` has decidable equality, and that
equality is equality of the values denoted: each value has exactly one
representation.

- `Decimal` replaces `Float`. A decimal is a finite decimal number in lowest
  terms, so two decimals are equal exactly when they denote the same rational
  number (`Decimal.toRat_injective`). `Float` does not qualify: its equality is
  IEEE equality, which is not reflexive on NaN.
- `Date` is the number of days since 1970-01-01 in the proleptic Gregorian
  calendar. Every integer is a date.
- `Uuid` is 128 bits, written in the canonical 8-4-4-4-12 hexadecimal form.
-/

namespace DDD

/-! ## Decimals -/

/-- The finite decimal number `mantissa / 10 ^ exponent`, in lowest terms: the
exponent is zero or the mantissa is not a multiple of ten. -/
structure Decimal where
  mantissa : Int
  exponent : Nat
  lowest : exponent = 0 ∨ ¬ (10 : Int) ∣ mantissa
deriving DecidableEq

namespace Decimal

/-- The decimal `m / 10 ^ e`: trailing zeros of `m` are removed while the exponent
is positive. -/
def normalize (m : Int) : Nat → Decimal
  | 0 => ⟨m, 0, .inl rfl⟩
  | e + 1 => if h : (10 : Int) ∣ m then normalize (m / 10) e else ⟨m, e + 1, .inr h⟩

/-- The rational number a decimal denotes. -/
def toRat (d : Decimal) : ℚ := d.mantissa / 10 ^ d.exponent

/-- Normalizing does not change the number. -/
theorem toRat_normalize (m : Int) (e : Nat) : (normalize m e).toRat = m / 10 ^ e := by
  induction e generalizing m with
  | zero => simp [normalize, toRat]
  | succ e ih =>
    unfold normalize
    split
    · rename_i h
      obtain ⟨k, rfl⟩ := h
      rw [ih, Int.mul_ediv_cancel_left _ (by norm_num)]
      push_cast
      field_simp
      ring
    · rfl

/-- Two decimals are equal exactly when they denote the same number. -/
theorem toRat_injective : Function.Injective toRat := by
  suffices key : ∀ d₁ d₂ : Decimal, d₁.exponent ≤ d₂.exponent →
      d₁.toRat = d₂.toRat → d₁ = d₂ by
    intro d₁ d₂ h
    rcases le_total d₁.exponent d₂.exponent with h' | h'
    · exact key d₁ d₂ h' h
    · exact (key d₂ d₁ h' h.symm).symm
  rintro ⟨m₁, e₁, h₁⟩ ⟨m₂, e₂, h₂⟩ (hle : e₁ ≤ e₂) heq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hm : m₁ * 10 ^ k = m₂ := by
    have h10 : (10 : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ (by norm_num)
    have hk : (10 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [toRat, pow_add] at heq
    rw [div_eq_div_iff h10 (mul_ne_zero h10 hk)] at heq
    have : ((m₁ * 10 ^ k : ℤ) : ℚ) = m₂ := by
      push_cast
      apply mul_right_cancel₀ h10
      linear_combination heq
    exact_mod_cast this
  cases k with
  | zero => simp only [pow_zero, mul_one] at hm; subst hm; rfl
  | succ k =>
    exfalso
    rcases h₂ with h₂ | h₂
    · omega
    · exact h₂ ⟨m₁ * 10 ^ k, by rw [← hm, pow_succ]; ring⟩

instance (n : Nat) : OfNat Decimal n := ⟨⟨n, 0, .inl rfl⟩⟩

/-- Decimal literals: `12.50` is the decimal `125 / 10`. -/
instance : OfScientific Decimal where
  ofScientific m s e := if s then normalize m e else ⟨m * 10 ^ e, 0, .inl rfl⟩

instance : Neg Decimal where
  neg d := ⟨-d.mantissa, d.exponent, d.lowest.imp id (fun h h' => h (dvd_neg.mp h'))⟩

/-- Decimal notation: `-12.5`, `0.05`, `3`. -/
protected def toString (d : Decimal) : String :=
  let digits := Nat.toDigits 10 d.mantissa.natAbs
  let padded := List.replicate (d.exponent + 1 - digits.length) '0' ++ digits
  let k := padded.length - d.exponent
  let sign := if d.mantissa < 0 then "-" else ""
  if d.exponent = 0 then sign ++ String.ofList digits
  else sign ++ String.ofList (padded.take k) ++ "." ++ String.ofList (padded.drop k)

instance : ToString Decimal := ⟨Decimal.toString⟩
instance : Repr Decimal := ⟨fun d _ => Decimal.toString d⟩

end Decimal

/-! ## Dates -/

/-- A calendar date, as the number of days since 1970-01-01 in the proleptic
Gregorian calendar. -/
structure Date where
  days : Int
deriving DecidableEq

namespace Date

/-- The date with year `y`, month `m` (1 to 12) and day `d` (1 to the length of the
month). Out-of-range arguments give some date; `ofCivil?` rejects them. The
computation is `days_from_civil` of H. Hinnant, "chrono-Compatible Low-Level Date
Algorithms". -/
def ofCivil (y : Int) (m d : Nat) : Date :=
  let y : Int := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y % 400
  let mp : Int := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  ⟨era * 146097 + doe - 719468⟩

/-- Year, month (1 to 12) and day (1 to 31) of a date: `civil_from_days`, the
inverse of `ofCivil` on valid dates. -/
def toCivil (date : Date) : Int × Nat × Nat :=
  let z := date.days + 719468
  let era := z / 146097
  let doe := (z % 146097).toNat
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (era * 400 + yoe + (if m ≤ 2 then 1 else 0), m, d)

/-- The date with year `y`, month `m` and day `d`, if these name a date. -/
def ofCivil? (y : Int) (m d : Nat) : Option Date :=
  let date := ofCivil y m d
  if date.toCivil = (y, m, d) then some date else none

/-- `n` in decimal, padded with zeros to `width` digits. -/
private def pad (width n : Nat) : String :=
  let digits := Nat.toDigits 10 n
  String.ofList (List.replicate (width - digits.length) '0' ++ digits)

/-- ISO 8601 notation, `2026-10-28`. Years outside 0 to 9999 carry a sign. -/
protected def toString (date : Date) : String :=
  let (y, m, d) := date.toCivil
  let year :=
    if 0 ≤ y ∧ y ≤ 9999 then pad 4 y.toNat
    else (if y < 0 then "-" else "+") ++ pad 4 y.natAbs
  year ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d

instance : ToString Date := ⟨Date.toString⟩
instance : Repr Date := ⟨fun d _ => Date.toString d⟩

example : ofCivil 1970 1 1 = ⟨0⟩ := by decide
example : ofCivil 2000 3 1 = ⟨11017⟩ := by decide
example : (ofCivil 2024 2 29).toCivil = (2024, 2, 29) := by decide
example : ofCivil? 2026 2 29 = none := by decide

end Date

/-! ## UUIDs -/

/-- A UUID: 128 bits. -/
structure Uuid where
  bits : BitVec 128
deriving DecidableEq

namespace Uuid

/-- The canonical form: 32 lower-case hexadecimal digits in groups 8-4-4-4-12. -/
protected def toString (u : Uuid) : String :=
  let hex := Nat.toDigits 16 u.bits.toNat
  let hex := List.replicate (32 - hex.length) '0' ++ hex
  let group (i n : Nat) := String.ofList ((hex.drop i).take n)
  String.intercalate "-" [group 0 8, group 8 4, group 12 4, group 16 4, group 20 12]

instance : ToString Uuid := ⟨Uuid.toString⟩
instance : Repr Uuid := ⟨fun u _ => Uuid.toString u⟩

end Uuid

/-! ## Value types and their interpretation -/

/-- The value types shared by all contexts. -/
inductive ValueType where
  | int | decimal | string | date | uuid
deriving DecidableEq, Repr, Fintype

/-- The interpretation of the value types, the same in every context. -/
abbrev K : ValueType → Type
  | .int => Int
  | .decimal => Decimal
  | .string => String
  | .date => Date
  | .uuid => Uuid

instance : (v : ValueType) → DecidableEq (K v)
  | .int => inferInstanceAs (DecidableEq Int)
  | .decimal => inferInstanceAs (DecidableEq Decimal)
  | .string => inferInstanceAs (DecidableEq String)
  | .date => inferInstanceAs (DecidableEq Date)
  | .uuid => inferInstanceAs (DecidableEq Uuid)

instance : (v : ValueType) → Repr (K v)
  | .int => inferInstanceAs (Repr Int)
  | .decimal => inferInstanceAs (Repr Decimal)
  | .string => inferInstanceAs (Repr String)
  | .date => inferInstanceAs (Repr Date)
  | .uuid => inferInstanceAs (Repr Uuid)

instance : (v : ValueType) → ToString (K v)
  | .int => inferInstanceAs (ToString Int)
  | .decimal => inferInstanceAs (ToString Decimal)
  | .string => inferInstanceAs (ToString String)
  | .date => inferInstanceAs (ToString Date)
  | .uuid => inferInstanceAs (ToString Uuid)

example : (12.50 : K .decimal) = 12.5 := by decide
example : (-0.050 : K .decimal) ≠ 0.05 := by decide
example : (Date.ofCivil 2026 10 28 : K .date) ≠ Date.ofCivil 2026 10 29 := by decide

end DDD
