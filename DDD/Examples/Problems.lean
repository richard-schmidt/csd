import DDD.Report
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
- The report of a context map document with a broken context, a failing arrow
  and an arrow to a missing context (`brokenMap`). `cli/CsdExport.lean` writes
  it to `cli/test/broken-map.json`, which CI checks with `csd-check --json`.
-/

set_option linter.hashCommand false

namespace DDD.Examples.Problems

open DDD Lean

/-- A schema that breaks every condition of `WellFormed`. -/
def broken : Schema where
  entities := ["A", "B", "A"]
  refs := [⟨"b", "A", "B"⟩, ⟨"b", "A", "C"⟩, ⟨"x", "Z", "B"⟩]
  attrs := [⟨"name", "B", .string⟩, ⟨"v", "Y", .int⟩]
  eqns := [⟨"A", ["b", "name"], ["b"]⟩, ⟨"Q", [], []⟩]
  aggregates := [⟨"A", [⟨"B", "a"⟩]⟩, ⟨"B", []⟩, ⟨"W", []⟩]
  valueObjects := ["A", "V"]

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
    .boundary ⟨"x", "Z", "B"⟩ "A",
    .valueObjectAttrs "A",
    .valueObjectEntity "V"] := by decide

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

/-- Three contexts, one of them broken, and three arrows: the valid translation into
Payments, the failing one, and one to a context the document does not have. -/
def brokenMap : MapDoc where
  contexts := [("OrdersPL", Orders.published, false), ("Payments", Payments.schema, false),
    ("Broken", broken, false)]
  arrows := [("billing", "OrdersPL", "Payments", Integration.ordersPayments),
    ("billingToShipping", "OrdersPL", "Payments", Integration.ordersPaymentsBillToShipTo),
    ("dangling", "OrdersPL", "Nowhere", {})]

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
  [("OrdersPL", true, []), ("Payments", true, []),
   ("Broken", false, ["duplicateEntity", "duplicateGenerator", "referenceTarget",
     "referenceSource", "attributeSource", "equationNotParallel", "equationSource",
     "aggregateEntity", "aggregateOverlap", "missingOwner", "aggregateBoundary",
     "valueObjectAttributes", "valueObjectEntity"])]

#guard summary (brokenMap.report.getObjValD "arrows") ==
  [("billing", true, []), ("billingToShipping", false, ["equationImage"]),
   ("dangling", false, ["unknownSchema"])]

#guard brokenMap.report.getObjValD "failed" == (3 : Nat)

-- The document round-trips through its JSON text.
#guard match Json.parse brokenMap.toJson.compress >>= MapDoc.ofJson with
  | .ok M => M == brokenMap
  | .error _ => false

end DDD.Examples.Problems
