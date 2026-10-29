import DDD.Json
import DDD.Examples.Integration
import DDD.Examples.Gluing

/-!
# Example: the context map in the exchange format

`workspace` is the document that the Julia side reads: the context map of
`Integration.lean` as a `MapDoc`, the expected results of the strict
non-interference check for the Customers kernel (both legs full and faithful,
`Gluing.orders_fullyFaithful` and `Gluing.shipping_fullyFaithful`), and the
failing kernel of `Gluing.lean` as a scenario (the leg from Orders fails the
check, `Gluing.delivery_check`). `cli/CsdExport.lean` writes it to
`julia/data/workspace.json`.

The round trips through JSON text are tested with `#guard`: schemas,
translations, the map, and a finite state of the Customers kernel.
-/

set_option linter.hashCommand false

namespace DDD.Examples.Exchange

open Lean Integration

/-- The name of each context. -/
def contextName : Context → String
  | .Catalog => "Catalog"
  | .CatalogPL => "CatalogPL"
  | .Orders => "Orders"
  | .OrdersPL => "OrdersPL"
  | .Customers => "Customers"
  | .Payments => "Payments"
  | .Shipping => "Shipping"

/-- The contexts, upstream first. -/
def contexts : List Context :=
  [.CatalogPL, .OrdersPL, .Customers, .Catalog, .Orders, .Payments, .Shipping]

/-- The arrows, with their names. -/
def arrows : List (String × String × String × Translation) :=
  [("catalogPL_catalog", "CatalogPL", "Catalog", translation Arrow.catalogPL_catalog),
   ("catalogPL_orders", "CatalogPL", "Orders", translation Arrow.catalogPL_orders),
   ("ordersPL_orders", "OrdersPL", "Orders", translation Arrow.ordersPL_orders),
   ("ordersPL_payments", "OrdersPL", "Payments", translation Arrow.ordersPL_payments),
   ("customers_orders", "Customers", "Orders", translation Arrow.customers_orders),
   ("customers_shipping", "Customers", "Shipping", translation Arrow.customers_shipping)]

/-- The context map as data. -/
def map : MapDoc where
  contexts := contexts.map fun c => (contextName c, schema c, kernel c)
  arrows := arrows

/-- The document for the Julia side. -/
def workspace : Json := Json.mkObj [
  ("format", .str formatVersion), ("kind", .str "workspace"),
  ("map", map.toJson),
  ("expectations", Json.arr #[Json.mkObj [("kernel", .str "Customers"),
    ("fullyFaithful", toJson [true, true])]]),
  ("scenarios", Json.arr #[Json.mkObj [("name", .str "deliveryAddress"),
    ("kernel", Gluing.kernel₂.toJson), ("left", Gluing.orders₂.toJson),
    ("right", Gluing.shipping₂.toJson), ("fullyFaithful", toJson [false, true])]])]

/-! ## Round trips -/

/-- Encoding, printing, parsing and decoding gives back the value. -/
def roundTrip {α : Type} [DecidableEq α] (enc : α → Json) (dec : Json → Except String α)
    (x : α) : Bool :=
  match Json.parse (enc x).compress >>= dec with
  | .ok y => decide (y = x)
  | .error _ => false

#guard contexts.all fun c => roundTrip Schema.toJson Schema.fromJson (schema c)
#guard arrows.all fun a => roundTrip Translation.toJson Translation.fromJson a.2.2.2
#guard roundTrip MapDoc.toJson MapDoc.fromJson map
#guard roundTrip Schema.toJson Schema.fromJson Gluing.shipping₂

/-- A finite state of the Customers kernel: two customers at one address. -/
def customersState : FinState LitK where
  sizes := [("Customer", 2), ("Address", 1)]
  refs := [(("Customer", "address"), [0, 0])]
  attrs := [(("Customer", "name"), [⟨.string, .text "Ada"⟩, ⟨.string, .text "Grace"⟩]),
    (("Address", "street"), [⟨.string, .text "Bahnhofstrasse 1"⟩]),
    (("Address", "city"), [⟨.string, .text "Bern"⟩])]

#guard customersState.check customers
#guard customersState.checkValueObjects customers
#guard roundTrip FinState.toJson (FinState.fromJson customers) customersState

end DDD.Examples.Exchange
