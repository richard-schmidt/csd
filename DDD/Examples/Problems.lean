import DDD.MapCheck
import DDD.Examples.Integration

/-!
# Problems and reports on the examples

- A schema that breaks every condition of `WellFormed` has one problem of each
  kind.
- The variants of Orders and Catalog that break the aggregate rule have one
  boundary problem per reference into a member from outside.
- The schemas of the example map have no problem (`Schema.problems_eq_nil_iff_wellFormed`).
- The failing translation into Payments has one problem, its equation; a
  translation with wrong images has one problem per wrong image.
- The report of a context map document with a broken list of value types, a
  broken context, a context with undeclared value types, a failing arrow, an
  arrow that does not keep a key, an arrow to a missing context, an arrow out of
  a kernel that renames, a published language that reaches a member of an
  aggregate, two contexts on a cycle, two declared route equations that do
  not hold, and two event types that are none (`brokenMap`). `cli/CsdExport.lean` writes it to
  `cli/test/broken-map.json`, which CI checks with `csd-check --json`.
- Documents with a published language that merges entity types (`mergedMap`) and
  with names declared twice (`twiceMap`).
-/

set_option linter.hashCommand false

namespace DDD.Examples.Problems

open DDD Lean

/-- A schema that breaks every condition of `WellFormed`. -/
def broken : Schema where
  entities := ["A", "B", "A", "E", "G"]
  refs := [⟨"b", "A", "B"⟩, ⟨"b", "A", "C"⟩, ⟨"x", "Z", "B"⟩, ⟨"f", "G", "G"⟩]
  attrs := [⟨"name", "B", .string⟩, ⟨"v", "Y", .int⟩]
  eqns := [⟨"A", ["b", "name"], ["b"]⟩, ⟨"Q", [], []⟩]
  aggregates := [⟨"A", [⟨"B", "a"⟩]⟩, ⟨"B", []⟩, ⟨"W", []⟩, ⟨"E", [⟨"G", "f"⟩]⟩]
  valueObjects := ["E", "V"]
  keys := [⟨"Q", ["x"]⟩, ⟨"B", []⟩, ⟨"B", ["name", "nope"]⟩]
  subtypes := [⟨"S", "s"⟩, ⟨"B", "up"⟩]

example : broken.problems = [
    .duplicateEntity "A",
    .duplicateGenerator "A" "b",
    .refTarget ⟨"b", "A", "C"⟩,
    .refSource ⟨"x", "Z", "B"⟩,
    .attrSource ⟨"v", "Y", .int⟩,
    .eqnNotParallel ⟨"A", ["b", "name"], ["b"]⟩ (some (.value .string)) (some (.entity "B")),
    .eqnSource ⟨"Q", [], []⟩,
    .aggregateEntity "W" "W",
    .aggregateOverlap "B",
    .missingOwner "A" ⟨"B", "a"⟩,
    .ownerCycle "E" ⟨"G", "f"⟩,
    .boundary ⟨"x", "Z", "B"⟩ "A",
    .valueObjectFields "E",
    .valueObjectEntity "V",
    .keyEntity ⟨"Q", ["x"]⟩,
    .keyEmpty "B",
    .keyField ⟨"B", ["name", "nope"]⟩ "nope",
    .subtypeEntity "S",
    .subtypeRef ⟨"B", "up"⟩] := by decide

/-- Orders with a customer's address inside the customer aggregate: the billing and
shipping addresses of an order reach into it. -/
example : Orders.withCustomerAddress.problems = [
    .boundary ⟨"billTo", "Order", "Address"⟩ "Customer",
    .boundary ⟨"shipTo", "Order", "Address"⟩ "Customer"] := by decide

example : Catalog.withFeatured.problems = [.boundary ⟨"featured", "Category", "Image"⟩ "Product"] :=
  by decide

example : Orders.schema.problems = [] :=
  (Schema.problems_eq_nil_iff_wellFormed _).mpr Orders.wellFormed

example : Payments.schema.problems = [] :=
  (Schema.problems_eq_nil_iff_wellFormed _).mpr Payments.wellFormed

/-- The billing address sent to the invoice's shipping address: the equation
`billTo = customer.address` goes to `shipTo = payer.address`. -/
example : Integration.ordersPaymentsBillToShipTo.problems Orders.published Payments.schema
    Payments.schema.pathEq =
    [.eqn ⟨"Order", ["billTo"], ["customer", "address"]⟩ ["shipTo"] ["payer", "address"]] := by
  decide

/-- Wrong images: an order's customer goes to its shipping address, its billing
address to a name that is not a generator, its id to its payer, and its date keeps
a name that Payments does not have. -/
def wrongImages : Translation where
  entities := [("Customer", "Payer"), ("Order", "Invoice")]
  gens := [⟨"Order", "customer", ["shipTo"]⟩, ⟨"Order", "billTo", ["nowhere"]⟩,
    ⟨"Order", "id", ["payer"]⟩]

example : wrongImages.problems Orders.published Payments.schema Payments.schema.pathEq = [
    .ref ⟨"customer", "Order", "Customer"⟩ ["shipTo"] (.entity "Payer") (some (.entity "Address")),
    .ref ⟨"billTo", "Order", "Address"⟩ ["nowhere"] (.entity "Address") none,
    .attr ⟨"id", "Order", .uuid⟩ ["payer"] (some (.entity "Payer")),
    .attr ⟨"placedOn", "Order", .date⟩ ["placedOn"] none,
    .eqn ⟨"Order", ["billTo"], ["customer", "address"]⟩ ["nowhere"] ["shipTo", "address"]] := by
  decide

/-- Orders sent to an entity type that Payments does not have. -/
example : (({ entities := [("Customer", "Payer"), ("Order", "Bill")] } : Translation).problems
    Orders.published Payments.schema Payments.schema.pathEq).map (·.kind) =
    ["entityImage", "referenceImage", "referenceImage", "referenceImage", "attributeImage",
      "attributeImage", "equationSourceImage"] := by decide

/-! ## The report of a context map document -/

/-- A schema with an undeclared value type and a value type optional twice. -/
def untyped : Schema where
  entities := ["Tag"]
  attrs := [⟨"code", "Tag", .optional (.named "Code")⟩,
    ⟨"weight", "Tag", .optional (.optional .int)⟩]

example : untyped.problems = [] := by decide

/-- OrdersPL → Payments with the street of an address sent to its city. It is valid,
but it does not keep the key of the value object `Address`: Payments identifies an
address by its street and its city, and only the city is an image. -/
def streetToCity : Translation :=
  { Integration.ordersPayments with
    gens := ⟨"Address", "street", ["city"]⟩ :: Integration.ordersPayments.gens }

example : streetToCity.keysNotKept Orders.published Payments.schema =
    [⟨"Address", ["street", "city"]⟩] := by decide

/-- The lines of invoices, as a schema of its own. -/
def lines : Schema where
  entities := ["InvoiceLine"]
  attrs := [⟨"quantity", "InvoiceLine", .int⟩]

/-- A schema with one entity type. -/
def thing : Schema where
  entities := ["Thing"]

/-- A list of value types with an empty enumeration and a built-in name; contexts,
one of them broken, one with undeclared value types and one marked as a kernel;
and arrows: the valid translation into Payments, the failing one, one that does
not keep a key, one to a context the document does not have, one out of the
kernel that renames customers to payers, one marked as publishing that sends its
entity type to a member of the invoice aggregate, and two that form a cycle. Two
route equations are declared: one between two routes with different translations,
one whose right side names no arrow. Two event types: one named after an entity
type of its context, and one that refers to a refund, a member of the payment
aggregate. -/
def brokenMap : MapDoc where
  valueTypes := { decls := [("PaymentMethod", .enum ["card", "invoice", "transfer"]),
    ("Size", .enum []), ("string", .over .string)] }
  contexts := [("OrdersPL", Orders.published, false), ("Payments", Payments.schema, false),
    ("Broken", broken, false), ("Untyped", untyped, false),
    ("Customers", Integration.customers, true), ("Lines", lines, false),
    ("Ping", thing, false), ("Pong", thing, false)]
  arrows := [("billing", "OrdersPL", "Payments", Integration.ordersPayments),
    ("billingToShipping", "OrdersPL", "Payments", Integration.ordersPaymentsBillToShipTo),
    ("streetToCity", "OrdersPL", "Payments", streetToCity),
    ("dangling", "OrdersPL", "Nowhere", {}),
    ("payers", "Customers", "Payments", { entities := [("Customer", "Payer")] }),
    ("publishLines", "Lines", "Payments", {}),
    ("ping", "Ping", "Pong", {}), ("pong", "Pong", "Ping", {})]
  published := ["publishLines"]
  events := [("OrdersPL", { name := "Order", refs := [("order", "Order")] }),
    ("Payments", { name := "Refunded", refs := [("refund", "Refund")] })]
  routeEqns := [(["billing"], ["streetToCity"]), (["billing"], ["nowhere"])]

/-- The kinds of the problems of the entries of a report, with their names and
results. -/
def summary (entries : Json) : List (String × Bool × List String) :=
  match entries.getArr? with
  | .ok a => a.toList.map fun e =>
    ((e.getObjValAs? String "name").toOption.getD "",
      (e.getObjValAs? Bool "ok").toOption.getD false,
      match (e.getObjVal? "problems").toOption.bind (·.getArr?.toOption) with
      | some ps => ps.toList.map fun p => (p.getObjValAs? String "kind").toOption.getD ""
      | none => [])
  | .error _ => []

#guard summary (brokenMap.report.getObjValD "contexts") ==
  [("OrdersPL", false, ["eventName"]), ("Payments", false, ["aggregateBoundary"]),
   ("Broken", false, ["duplicateEntity", "duplicateGenerator", "referenceTarget",
     "referenceSource", "attributeSource", "equationNotParallel", "equationSource",
     "aggregateEntity", "aggregateOverlap", "missingOwner", "ownerCycle", "aggregateBoundary",
     "valueObjectFields", "valueObjectEntity", "keyEntity", "keyEmpty", "keyField",
     "subtypeEntity", "subtypeReference"]),
   ("Untyped", false, ["undeclaredValueType", "nestedOptional"]),
   ("Customers", true, []), ("Lines", true, []), ("Ping", true, []), ("Pong", true, [])]

#guard summary (Json.arr #[(brokenMap.report.getObjValD "valueTypes").setObjVal! "name" ""]) ==
  [("", false, ["emptyEnumeration", "builtinTypeName"])]

#guard summary (brokenMap.report.getObjValD "arrows") ==
  [("billing", true, []), ("billingToShipping", false, ["equationImage"]),
   ("streetToCity", false, ["keyNotKept"]), ("dangling", false, ["unknownSchema"]),
   ("payers", false, ["kernelTranslation"]), ("publishLines", false, ["publishedMember"]),
   ("ping", true, []), ("pong", true, [])]

-- The map as a whole: the cycle, and the two declared equations.
#guard summary (Json.arr #[(brokenMap.report.getObjValD "map").setObjVal! "name" ""]) ==
  [("", false, ["cycle", "routeEquation", "routeEquation"])]

#guard brokenMap.report.getObjValD "failed" == (11 : Nat)

-- The conditions on the map: the names are distinct, and the other four fail.
#guard brokenMap.conditions.map (·.2.1) == [true, false, false, false, false]
#guard !brokenMap.check

/-- The published language of Catalog marked as published by Orders: its two entity
types go to one. -/
def mergedMap : MapDoc where
  contexts := [("CatalogPL", Catalog.published, false), ("Orders", Orders.schema, false)]
  arrows := [("catalogPL_orders", "CatalogPL", "Orders", Integration.catalogOrders)]
  published := ["catalogPL_orders"]

#guard summary (mergedMap.report.getObjValD "arrows") ==
  [("catalogPL_orders", false, ["entitiesMerged", "entitiesMerged"])]

/-- An event type of a context the document does not have: a problem of the map. -/
def lostMap : MapDoc where
  contexts := [("Ping", thing, false)]
  arrows := []
  events := [("Nowhere", { name := "Lost" })]

#guard summary (Json.arr #[(lostMap.report.getObjValD "map").setObjVal! "name" ""]) ==
  [("", false, ["unknownSchema"])]
#guard !lostMap.check

/-- A context and an arrow declared twice. -/
def twiceMap : MapDoc where
  contexts := [("Ping", thing, false), ("Pong", thing, false), ("Ping", thing, false)]
  arrows := [("ping", "Ping", "Pong", {}), ("ping", "Ping", "Pong", {})]

#guard summary (Json.arr #[(twiceMap.report.getObjValD "map").setObjVal! "name" ""]) ==
  [("", false, ["duplicateContext", "duplicateArrow"])]

-- The document round-trips through its JSON text.
#guard match Json.parse brokenMap.toJson.compress >>= MapDoc.ofJson with
  | .ok M => M == brokenMap
  | .error _ => false

end DDD.Examples.Problems
