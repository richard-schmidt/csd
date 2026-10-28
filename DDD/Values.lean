import Mathlib.Tactic.DeriveFintype

/-!
# Value types

The value types shared by all bounded contexts. Schemas refer to them only: an
attribute ends in a value type, and translations leave value types unchanged.

Their interpretation `K : ValueType → Type` is not fixed here. It is a parameter
of the state layer, the same for all contexts of an integration, and the general
theorems hold for every `K`. Per-model checks compare values, so they require
`DecidableEq (K v)` for every `v`, and that equality must be equality of values:
`Float` does not qualify, since IEEE equality is not reflexive on NaN.
`DDD.Examples.Values` gives the interpretation the examples use.
-/

namespace DDD

/-- The value types shared by all contexts. -/
inductive ValueType where
  | int | decimal | string | date | uuid
deriving DecidableEq, Repr, Fintype

end DDD
