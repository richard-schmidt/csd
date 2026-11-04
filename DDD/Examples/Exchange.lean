import DDD.Json
import DDD.Report
import DDD.Examples.Integration
import DDD.Examples.Gluing

/-!
# Example: the context map in the exchange format

`workspace` is the document that the Julia side reads: the context map of
`Integration.lean` as a `MapDoc`, the expected results of the strict
non-interference check for the Customers kernel (both legs full and faithful,
`Gluing.orders_fullyFaithful` and `Gluing.shipping_fullyFaithful`), and the
failing kernel of `Gluing.lean` as a scenario (the leg from Orders fails the
check, `Gluing.delivery_check`), and a scenario whose two sides share a name
outside the kernel (`created_clash`), which the Julia side qualifies with the
context names before gluing. `cli/CsdExport.lean` writes it to
`julia/data/workspace.json`.

The map declares its value types (`valueTypes`). The workspace also carries a
sample, the schema `deliveries` with a value type of each kind and a finite
state whose literals are written in other forms than their normal forms; the
Julia side passes it through to its certificate, whose reader puts the
literals in normal form.

The round trips through JSON text are tested with `#guard`: schemas,
translations, the map, and finite states of the Customers kernel and of the
sample.
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

/-- The value types of the example map and of the sample. -/
def valueTypes : TypeList where
  decls := [("OrderStatus", .enum ["placed", "paid", "shipped", "cancelled"]),
    ("PaymentMethod", .enum ["card", "invoice", "transfer"]),
    ("DeliveryStatus", .enum ["scheduled", "dispatched", "delivered"]),
    ("Money", .over .decimal)]

/-- The context map as data. -/
def map : MapDoc where
  valueTypes := valueTypes
  contexts := contexts.map fun c => (contextName c, schema c, kernel c)
  arrows := arrows

/-- Orders, with the date each customer was created. -/
def ordersCreated : Schema :=
  { Orders.schema with attrs := Orders.schema.attrs ++ [⟨"createdAt", "Customer", .date⟩] }

/-- Shipping, with the date each customer was created. -/
def shippingCreated : Schema :=
  { Shipping.schema with attrs := Shipping.schema.attrs ++ [⟨"createdAt", "Customer", .date⟩] }

/-- The two share `Customer.createdAt` outside the kernel, so they cannot be glued
as they are. -/
theorem created_clash : Schema.gluingClashes customers ordersCreated shippingCreated =
    ["Customer.createdAt"] := by
  decide

/-- Deliveries, with a value type of each kind. -/
def deliveries : Schema where
  entities := ["Delivery"]
  attrs := [⟨"id", "Delivery", .uuid⟩, ⟨"status", "Delivery", .named "DeliveryStatus"⟩,
    ⟨"scheduledFor", "Delivery", .datetime⟩,
    ⟨"dispatchedAt", "Delivery", .optional .timestamp⟩,
    ⟨"window", "Delivery", .duration⟩, ⟨"opensAt", "Delivery", .time⟩,
    ⟨"fee", "Delivery", .named "Money"⟩, ⟨"note", "Delivery", .optional .string⟩]

/-- A column of literals of one value type. -/
def col (v : ValueType) (ls : List Lit) : List (Σ _ : ValueType, Lit) := ls.map fun l => ⟨v, l⟩

/-- Two deliveries, with literals written in other forms than their normal forms. -/
def deliveriesState : FinState LitK where
  sizes := [("Delivery", 2)]
  refs := []
  attrs := [
    (("Delivery", "id"), col .uuid
      [.text "7C9E6679-7425-40DE-944B-E07FC1F90AE7", .text "9b2f0c431d2e4f5a8b6c3d4e5f6a7b8c"]),
    (("Delivery", "status"), col (.named "DeliveryStatus") [.text "dispatched", .text "scheduled"]),
    (("Delivery", "scheduledFor"), col .datetime
      [.text "2026-11-04 09:30", .text "2026-11-05T14:00:00"]),
    (("Delivery", "dispatchedAt"), col (.optional .timestamp)
      [.text "2026-11-04T09:10:00+01:00", .null]),
    (("Delivery", "window"), col .duration [.text "PT90M", .text "PT2H"]),
    (("Delivery", "opensAt"), col .time [.text "08:00", .text "08:00:00"]),
    (("Delivery", "fee"), col (.named "Money") [.text "12.50", .int 9]),
    (("Delivery", "note"), col (.optional .string) [.null, .text "Leave at the door"])]

/-- The document for the Julia side. -/
def workspace : Json := Json.mkObj [
  ("format", .str formatVersion), ("kind", .str "workspace"),
  ("map", map.toJson),
  ("expectations", Json.arr #[Json.mkObj [("kernel", .str "Customers"),
    ("fullyFaithful", toJson [true, true])]]),
  ("scenarios", Json.arr #[Json.mkObj [("name", .str "deliveryAddress"),
    ("kernel", Gluing.kernel₂.toJson), ("left", Gluing.orders₂.toJson),
    ("right", Gluing.shipping₂.toJson), ("fullyFaithful", toJson [false, true])],
    Json.mkObj [("name", .str "createdAt"), ("kernel", customers.toJson),
    ("left", ordersCreated.toJson), ("right", shippingCreated.toJson),
    ("qualify", toJson ["Orders", "Shipping"])]]),
  ("samples", Json.arr #[Json.mkObj [("name", .str "Deliveries"),
    ("schema", deliveries.toJson), ("state", deliveriesState.toJson)]])]

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

/-! ## The sample -/

#guard roundTrip Schema.toJson Schema.fromJson deliveries
#guard roundTrip FinState.toJson (FinState.fromJson deliveries) deliveriesState
#guard roundTrip TypeList.toJson TypeList.fromJson valueTypes

/-- The sample as the Julia side passes it on: its schema, its state, and the
claims about them, with the list of value types of the map. -/
def sampleCertificate : Certificate where
  valueTypes := valueTypes
  schemas := [("Deliveries", deliveries)]
  states := [("XD", "Deliveries", deliveriesState.normalize valueTypes)]
  claims := [.valueTypes, .wellFormed "Deliveries", .declared "Deliveries", .state "XD"]

#guard sampleCertificate.check

/-- The sample's schema as a context of a map document, with the list of value
types. -/
def sampleMap : MapDoc where
  valueTypes := valueTypes
  contexts := [("Deliveries", deliveries, false)]
  arrows := []

#guard sampleMap.report.getObjValD "failed" == (0 : Nat)
#guard ({ sampleMap with valueTypes := {} } : MapDoc).report.getObjValD "failed" == (1 : Nat)

-- The state as written fails the check of literals: its literals are not in
-- normal form.
#guard !deliveriesState.litsFit valueTypes
#guard (deliveriesState.litProblems valueTypes).length == 8

#guard ((deliveriesState.normalize valueTypes).attrCol "Delivery" "dispatchedAt").map
    (·.map (·.2)) == some [.text "2026-11-04T08:10:00Z", .null]
#guard ((deliveriesState.normalize valueTypes).attrCol "Delivery" "window").map
    (·.map (·.2)) == some [.text "PT1H30M", .text "PT2H"]

end DDD.Examples.Exchange
