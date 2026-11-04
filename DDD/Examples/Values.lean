import DDD.Values

/-!
# Example: an interpretation of the value types

`K` interprets the value types for the examples. Its equality is decidable and is
equality of values, since each value has one representation:

- `Decimal`, in place of `Float`: a finite decimal number in lowest terms;
- `Date`: the number of days since 1970-01-01 in the proleptic Gregorian
  calendar;
- `Uuid`: 128 bits;
- `bool`: `Bool`;
- `time`: the seconds since midnight, a `Decimal`;
- `datetime`: a `Date` and a time of day;
- `timestamp`: the seconds since 1970-01-01T00:00:00Z, a `Decimal`;
- `duration`: a number of seconds, a `Decimal`;
- a named type: the names of its elements, as strings. The examples do not
  restrict them to a declared list;
- `optional v`: `Option` of the interpretation of `v`.
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

/-- A time of day, as the seconds since midnight. -/
structure TimeOfDay where
  seconds : Decimal
deriving DecidableEq

/-- A date and a time of day, without time zone. -/
structure DateTime where
  date : Date
  time : TimeOfDay
deriving DecidableEq

/-- An instant, as the seconds since 1970-01-01T00:00:00Z. -/
structure Instant where
  seconds : Decimal
deriving DecidableEq

/-- An exact length of time, in seconds. -/
structure Duration where
  seconds : Decimal
deriving DecidableEq

/-- The interpretation of the value types in the examples. -/
abbrev K : ValueType → Type
  | .int => Int
  | .decimal => Decimal
  | .string => String
  | .date => Date
  | .uuid => Uuid
  | .bool => Bool
  | .datetime => DateTime
  | .timestamp => Instant
  | .time => TimeOfDay
  | .duration => Duration
  | .named _ => String
  | .optional v => Option (K v)

instance instDecidableEqK : (v : ValueType) → DecidableEq (K v)
  | .int => inferInstanceAs (DecidableEq Int)
  | .decimal => inferInstanceAs (DecidableEq Decimal)
  | .string => inferInstanceAs (DecidableEq String)
  | .date => inferInstanceAs (DecidableEq Date)
  | .uuid => inferInstanceAs (DecidableEq Uuid)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .datetime => inferInstanceAs (DecidableEq DateTime)
  | .timestamp => inferInstanceAs (DecidableEq Instant)
  | .time => inferInstanceAs (DecidableEq TimeOfDay)
  | .duration => inferInstanceAs (DecidableEq Duration)
  | .named _ => inferInstanceAs (DecidableEq String)
  | .optional v =>
    have := instDecidableEqK v
    inferInstanceAs (DecidableEq (Option (K v)))

end DDD.Examples.Values
