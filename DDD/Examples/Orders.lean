import DDD.PathEq

/-!
# Example: the Orders context

Customers, addresses, orders, order lines, and the products they refer to. A
product here is the Orders view of a catalog variant: its SKU, name and list
price. The status of an order is a project-defined value type, `OrderStatus`.
Addresses are value objects: an address is its street and city.

Two equations:

- an order is billed to its customer's address: `billTo = customer.address`;
- an order line keeps the SKU of its product: `sku = product.sku`, an equation
  ending in an attribute.

Aggregates: an order with its lines, each owning reference `order` pointing to
the root; customers, addresses and products on their own.

The published language of Orders (`published`): customers, addresses and orders,
with the first equation. It contains roots only (`published_rootsOnly`); order
lines belong to the order aggregate, so a published language with them fails the
check (`withLines_not_rootsOnly`).

The references have no cycle, so path equality is decided by
`Schema.pathEqAcyclic_iff`. Checked with `decide`: well-formedness, acyclicity,
that the billing city of a line's order is its customer's city, and that the
shipping city need not be. `withCustomerAddress` makes addresses members of the
customer aggregate; the references `billTo` and `shipTo` from orders then enter
that aggregate below its root, and the check fails.
-/

namespace DDD.Examples.Orders

open Schema

/-- The Orders schema. -/
def schema : Schema where
  entities := ["Customer", "Address", "Order", "OrderLine", "Product"]
  refs := [⟨"address", "Customer", "Address"⟩, ⟨"customer", "Order", "Customer"⟩,
    ⟨"billTo", "Order", "Address"⟩, ⟨"shipTo", "Order", "Address"⟩,
    ⟨"order", "OrderLine", "Order"⟩, ⟨"product", "OrderLine", "Product"⟩]
  attrs := [⟨"name", "Customer", .string⟩, ⟨"street", "Address", .string⟩,
    ⟨"city", "Address", .string⟩, ⟨"id", "Order", .uuid⟩, ⟨"placedOn", "Order", .date⟩,
    ⟨"status", "Order", .named "OrderStatus"⟩, ⟨"quantity", "OrderLine", .int⟩,
    ⟨"unitPrice", "OrderLine", .decimal⟩, ⟨"sku", "OrderLine", .string⟩,
    ⟨"sku", "Product", .string⟩, ⟨"name", "Product", .string⟩,
    ⟨"listPrice", "Product", .decimal⟩]
  eqns := [⟨"Order", ["billTo"], ["customer", "address"]⟩,
    ⟨"OrderLine", ["sku"], ["product", "sku"]⟩]
  aggregates := [⟨"Customer", []⟩, ⟨"Address", []⟩, ⟨"Order", [⟨"OrderLine", "order"⟩]⟩,
    ⟨"Product", []⟩]
  valueObjects := ["Address"]

theorem wellFormed : schema.WellFormed := by decide

theorem acyclic : schema.Acyclic := by decide

/-- The billing city of a line's order is the city of the order's customer: the
first equation, applied after the step `order`. -/
theorem billing_city :
    schema.PathEq ⟨.entity "OrderLine", by decide⟩ ["order", "billTo", "city"]
      ["order", "customer", "address", "city"] :=
  (pathEqAcyclic_iff wellFormed acyclic _ _ _).mp (by decide)

/-- The shipping city need not be the customer's city. -/
theorem shipping_city :
    ¬ schema.PathEq ⟨.entity "OrderLine", by decide⟩ ["order", "shipTo", "city"]
      ["order", "customer", "address", "city"] :=
  fun h => absurd ((pathEqAcyclic_iff wellFormed acyclic _ _ _).mpr h) (by decide)

/-- The second equation holds in `Schema.cat`. -/
theorem line_sku :
    schema.PathEq ⟨.entity "OrderLine", by decide⟩ ["sku"] ["product", "sku"] :=
  (pathEqAcyclic_iff wellFormed acyclic _ _ _).mp (by decide)

/-- Addresses as members of the customer aggregate, owned through `customer`. -/
def withCustomerAddress : Schema :=
  { schema with
    refs := ⟨"customer", "Address", "Customer"⟩ :: schema.refs
    aggregates := [⟨"Customer", [⟨"Address", "customer"⟩]⟩, ⟨"Order", [⟨"OrderLine", "order"⟩]⟩,
      ⟨"Product", []⟩] }

theorem withCustomerAddress_not_wellFormed : ¬ withCustomerAddress.WellFormed := by decide

/-! ## The published language -/

/-- The published language of Orders: customers, addresses and orders. -/
def published : Schema where
  entities := ["Customer", "Address", "Order"]
  refs := [⟨"address", "Customer", "Address"⟩, ⟨"customer", "Order", "Customer"⟩,
    ⟨"billTo", "Order", "Address"⟩, ⟨"shipTo", "Order", "Address"⟩]
  attrs := [⟨"name", "Customer", .string⟩, ⟨"street", "Address", .string⟩,
    ⟨"city", "Address", .string⟩, ⟨"id", "Order", .uuid⟩, ⟨"placedOn", "Order", .date⟩]
  eqns := [⟨"Order", ["billTo"], ["customer", "address"]⟩]
  aggregates := [⟨"Customer", []⟩, ⟨"Address", []⟩, ⟨"Order", []⟩]
  valueObjects := ["Address"]

theorem published_wellFormed : published.WellFormed := by decide

theorem published_acyclic : published.Acyclic := by decide

/-- Customers, addresses and orders are roots of Orders. -/
theorem published_rootsOnly : published.RootsOnly schema := by decide

/-- The published language with order lines. -/
def withLines : Schema :=
  { published with
    entities := published.entities ++ ["OrderLine"]
    refs := published.refs ++ [⟨"order", "OrderLine", "Order"⟩]
    attrs := published.attrs ++ [⟨"quantity", "OrderLine", .int⟩] }

/-- Order lines are members of the order aggregate, so they cannot be
published. -/
theorem withLines_not_rootsOnly : ¬ withLines.RootsOnly schema := by decide

end DDD.Examples.Orders
