import DDD.Values

/-!
# Example: an interpretation of the value types

`K` interprets the value types for the examples. Its equality is decidable and is
equality of values, since each value has one representation:

- `Decimal`, in place of `Float`: a finite decimal number in lowest terms;
- `Date`: the number of days since 1970-01-01 in the proleptic Gregorian
  calendar;
- `Uuid`: 128 bits.
-/

namespace DDD.Examples.Values

/-- The finite decimal number `mantissa / 10 ^ exponent`, in lowest terms: the
exponent is zero or the mantissa is not a multiple of ten. -/
structure Decimal where
  mantissa : Int
  exponent : Nat
  lowest : exponent = 0 ∨ ¬ (10 : Int) ∣ mantissa
deriving DecidableEq

/-- A calendar date, as the number of days since 1970-01-01 in the proleptic
Gregorian calendar. -/
structure Date where
  days : Int
deriving DecidableEq

/-- A UUID: 128 bits. -/
structure Uuid where
  bits : BitVec 128
deriving DecidableEq

/-- The interpretation of the value types in the examples. -/
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

end DDD.Examples.Values
