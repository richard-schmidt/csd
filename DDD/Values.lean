/-!
# Value types

The value types shared by all bounded contexts: the built-ins `int`, `decimal`,
`string`, `date`, `uuid`, `bool`, `datetime` (a date and a time of day, without
time zone), `timestamp` (an instant), `time` (a time of day) and `duration` (an
exact length of time, without months or years); project-defined types
`named n`, such as an enumeration `named "OrderStatus"`; and `optional v`, whose
values are absent or a value of `v`. Schemas refer to them only: an attribute
ends in a value type, and translations leave value types unchanged. There are
no operations on values.

Their interpretation `K : ValueType → Type` is not fixed here. It is a parameter
of the state layer, the same for all contexts of an integration, and the general
theorems hold for every `K`. Per-model checks compare values, so they require
`DecidableEq (K v)` for every `v`, and that equality must be equality of values:
`Float` does not qualify, since IEEE equality is not reflexive on NaN.
`DDD.Examples.Values` gives the interpretation the examples use. The list of
project-defined types of a model, and the literals of each type in the exchange
format, are in `DDD.Literals`.
-/

namespace DDD

/-- The value types shared by all contexts. `named n` is a project-defined value
type, such as an enumeration; the interpretation `K` gives it its values.
`optional v` has the values of `v` and one more, the absent value. -/
inductive ValueType where
  | int | decimal | string | date | uuid | bool
  | datetime | timestamp | time | duration
  | named (name : String)
  | optional (v : ValueType)
deriving DecidableEq, Repr

end DDD
