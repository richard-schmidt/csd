import DDD.Report

/-!
# Example: value objects, nested aggregates, keys and subtypes

The schema `sales`:

- `Address` is a value object with references: an address is its street, its
  city, its country and its customer, so two customers at the same street and
  city have two addresses. It is a member of the customer aggregate, owned
  through `customer`.
- The order aggregate is nested: order lines are owned by their order, and the
  discount of a line by the line (`LineDiscount.line`). Following the ownership
  references from a discount reaches the order in two steps.
- A line has at most one discount: `LineDiscount` is an intermediate entity type
  with the key `{line}`, its owner. An order has at most one coupon:
  `OrderCoupon` has the key `{order}`, so the reference from an order to a
  coupon is optional.
- An order has one line per product: `OrderLine` has the key
  `{order, product}`, so the products of an order form a set.
- `BusinessCustomer` is a subtype of `Customer`: its is-a reference `customer`
  is a key on its own, and the name of a business customer is reached through
  it (`["customer", "name"]`).
- Natural keys: orders by number, products by SKU, coupons and countries by
  code.

`state` satisfies every key (`state_keys`). Each of `twoLines`, `twoCoupons`,
`sameAddress` and `twoAccounts` breaks one key, and `keyViolations` names the
pair of entities. `broken` is a variant with an ownership cycle, an ownership
reference out of its aggregate, a key with an unknown field and a subtype
without its is-a reference; its problems are checked by `decide`.
-/

set_option linter.hashCommand false

namespace DDD.Examples.Structure

open DDD

/-- The schema. -/
def sales : Schema where
  entities := ["Country", "Customer", "Address", "BusinessCustomer", "Product", "Order",
    "OrderLine", "LineDiscount", "Coupon", "OrderCoupon"]
  refs := [⟨"country", "Address", "Country"⟩, ⟨"customer", "Address", "Customer"⟩,
    ⟨"customer", "BusinessCustomer", "Customer"⟩, ⟨"customer", "Order", "Customer"⟩,
    ⟨"order", "OrderLine", "Order"⟩, ⟨"product", "OrderLine", "Product"⟩,
    ⟨"line", "LineDiscount", "OrderLine"⟩, ⟨"order", "OrderCoupon", "Order"⟩,
    ⟨"coupon", "OrderCoupon", "Coupon"⟩]
  attrs := [⟨"code", "Country", .string⟩, ⟨"name", "Customer", .string⟩,
    ⟨"street", "Address", .string⟩, ⟨"city", "Address", .string⟩,
    ⟨"vatNumber", "BusinessCustomer", .string⟩, ⟨"sku", "Product", .string⟩,
    ⟨"name", "Product", .string⟩, ⟨"number", "Order", .string⟩,
    ⟨"placedOn", "Order", .date⟩, ⟨"quantity", "OrderLine", .int⟩,
    ⟨"percent", "LineDiscount", .decimal⟩, ⟨"code", "Coupon", .string⟩]
  aggregates := [⟨"Customer", [⟨"Address", "customer"⟩]⟩,
    ⟨"Order", [⟨"OrderLine", "order"⟩, ⟨"LineDiscount", "line"⟩, ⟨"OrderCoupon", "order"⟩]⟩]
  valueObjects := ["Address"]
  keys := [⟨"Country", ["code"]⟩, ⟨"Product", ["sku"]⟩, ⟨"Order", ["number"]⟩,
    ⟨"OrderLine", ["order", "product"]⟩, ⟨"LineDiscount", ["line"]⟩,
    ⟨"OrderCoupon", ["order"]⟩, ⟨"Coupon", ["code"]⟩]
  subtypes := [⟨"BusinessCustomer", "customer"⟩]

theorem wellFormed : sales.WellFormed := by decide

theorem acyclic : sales.Acyclic := by decide

/-- The discount of a line reaches the root of its aggregate in two steps. -/
example : sales.ownerIter ⟨"Order", [⟨"OrderLine", "order"⟩, ⟨"LineDiscount", "line"⟩,
    ⟨"OrderCoupon", "order"⟩]⟩ 2 "LineDiscount" = some "Order" := by decide

/-- The name of a business customer is reached through its is-a reference. -/
example : sales.tgt? (.entity "BusinessCustomer") ["customer", "name"] = some (.value .string) :=
  by decide

/-- The keys of `sales`: the declared keys, the value object `Address` with all its
fields, and the subtype. -/
example : sales.allKeys = sales.keys ++
    [⟨"Address", ["country", "customer", "street", "city"]⟩, ⟨"BusinessCustomer", ["customer"]⟩] :=
  by decide

/-! ## States -/

/-- A column of strings. -/
def strs (l : List String) : List (Σ _ : ValueType, Lit) := l.map fun s => ⟨.string, .text s⟩

/-- Two countries, three customers, one of them a business, three addresses (two
customers at the same street and city), two products, two orders with three
lines, a discount on the third line, and a coupon on the first order. -/
def state : FinState LitK where
  sizes := [("Country", 2), ("Customer", 3), ("Address", 3), ("BusinessCustomer", 1),
    ("Product", 2), ("Order", 2), ("OrderLine", 3), ("LineDiscount", 1), ("Coupon", 1),
    ("OrderCoupon", 1)]
  refs := [(("Address", "country"), [0, 0, 1]), (("Address", "customer"), [0, 1, 2]),
    (("BusinessCustomer", "customer"), [2]), (("Order", "customer"), [0, 2]),
    (("OrderLine", "order"), [0, 0, 1]), (("OrderLine", "product"), [0, 1, 0]),
    (("LineDiscount", "line"), [2]), (("OrderCoupon", "order"), [0]),
    (("OrderCoupon", "coupon"), [0])]
  attrs := [(("Country", "code"), strs ["CH", "DE"]),
    (("Customer", "name"), strs ["Ada", "Grace", "Acme"]),
    (("Address", "street"), strs ["Bahnhofstrasse 1", "Bahnhofstrasse 1", "Hauptstrasse 5"]),
    (("Address", "city"), strs ["Bern", "Bern", "Berlin"]),
    (("BusinessCustomer", "vatNumber"), strs ["DE123456789"]),
    (("Product", "sku"), strs ["P-1", "P-2"]), (("Product", "name"), strs ["Kettle", "Mug"]),
    (("Order", "number"), strs ["O-1", "O-2"]),
    (("Order", "placedOn"), [⟨.date, .text "2026-11-02"⟩, ⟨.date, .text "2026-11-03"⟩]),
    (("OrderLine", "quantity"), [⟨.int, .int 1⟩, ⟨.int, .int 2⟩, ⟨.int, .int 5⟩]),
    (("LineDiscount", "percent"), [⟨.decimal, .text "10"⟩]),
    (("Coupon", "code"), strs ["WELCOME"])]

theorem state_check : state.check sales = true := by decide

/-- `state` satisfies the keys of `sales`. -/
theorem state_keys : (state.toState state_check).Keys :=
  FinState.toState_keys wellFormed state_check (by decide)

/-- `state` with a column replaced. -/
def withRefs (X : FinState LitK) (g : String × String) (c : List Nat) : FinState LitK :=
  { X with refs := X.refs.map fun p => if p.1 = g then (g, c) else p }

/-- The first order has two lines for the first product. -/
def twoLines : FinState LitK := withRefs state ("OrderLine", "product") [0, 0, 0]

/-- The first order has two coupons. -/
def twoCoupons : FinState LitK :=
  { state with
    sizes := state.sizes.map fun p => if p.1 = "OrderCoupon" then ("OrderCoupon", 2) else p
    refs := (withRefs (withRefs state ("OrderCoupon", "order") [0, 0])
      ("OrderCoupon", "coupon") [0, 0]).refs }

/-- The first two addresses belong to the same customer, so they are one address
listed twice. -/
def sameAddress : FinState LitK := withRefs state ("Address", "customer") [0, 0, 2]

/-- Two business customers for one customer. -/
def twoAccounts : FinState LitK :=
  { state with
    sizes := state.sizes.map fun p =>
      if p.1 = "BusinessCustomer" then ("BusinessCustomer", 2) else p
    refs := (withRefs state ("BusinessCustomer", "customer") [2, 2]).refs
    attrs := state.attrs.map fun p =>
      if p.1 = ("BusinessCustomer", "vatNumber") then (p.1, strs ["DE123456789", "DE987654321"])
      else p }

#guard [twoLines, twoCoupons, sameAddress, twoAccounts].all (·.check sales)
#guard [twoLines, twoCoupons, sameAddress, twoAccounts].all (!·.checkKeys sales)

#guard twoLines.keyViolations sales == [(⟨"OrderLine", ["order", "product"]⟩, 0, 1)]
#guard twoCoupons.keyViolations sales == [(⟨"OrderCoupon", ["order"]⟩, 0, 1)]
#guard sameAddress.keyViolations sales ==
  [(⟨"Address", ["country", "customer", "street", "city"]⟩, 0, 1)]
#guard twoAccounts.keyViolations sales == [(⟨"BusinessCustomer", ["customer"]⟩, 0, 1)]

-- Two customers at the same street and city do not break the value object, whose
-- fields include its customer.
#guard state.checkValueObjects sales && !sameAddress.checkValueObjects sales

/-! ## A broken variant -/

/-- Lines owned by their discount and discounts by their line, a coupon link owned
through its coupon, which is outside the order aggregate, a key with an unknown
field, and a subtype whose is-a reference has another name. -/
def broken : Schema :=
  { sales with
    refs := sales.refs ++ [⟨"discount", "OrderLine", "LineDiscount"⟩]
    aggregates := [⟨"Customer", [⟨"Address", "customer"⟩]⟩,
      ⟨"Order", [⟨"OrderLine", "discount"⟩, ⟨"LineDiscount", "line"⟩,
        ⟨"OrderCoupon", "coupon"⟩]⟩]
    keys := sales.keys ++ [⟨"OrderLine", ["order", "item"]⟩]
    subtypes := [⟨"BusinessCustomer", "parent"⟩] }

example : broken.problems = [
    .ownerCycle "Order" ⟨"OrderLine", "discount"⟩,
    .ownerCycle "Order" ⟨"LineDiscount", "line"⟩,
    .missingOwner "Order" ⟨"OrderCoupon", "coupon"⟩,
    .keyField ⟨"OrderLine", ["order", "item"]⟩ "item",
    .subtypeRef ⟨"BusinessCustomer", "parent"⟩] := by decide

end DDD.Examples.Structure
