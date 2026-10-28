/-!
# Value types

The value types shared by all bounded contexts: `int`, `decimal`, `string`,
`date`, `uuid`, `bool`, and project-defined types `named n`, such as an
enumeration `named "OrderStatus"`. Schemas refer to them only: an attribute ends
in a value type, and translations leave value types unchanged. There are no
operations on values.

Their interpretation `K : ValueType → Type` is not fixed here. It is a parameter
of the state layer, the same for all contexts of an integration, and the general
theorems hold for every `K`. Per-model checks compare values, so they require
`DecidableEq (K v)` for every `v`, and that equality must be equality of values:
`Float` does not qualify, since IEEE equality is not reflexive on NaN.
`DDD.Examples.Values` gives the interpretation the examples use.
-/

namespace DDD

/-- The value types shared by all contexts. `named n` is a project-defined value
type, such as an enumeration; the interpretation `K` gives it its values. -/
inductive ValueType where
  | int | decimal | string | date | uuid | bool
  | named (name : String)
deriving DecidableEq, Repr

end DDD
