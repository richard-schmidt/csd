import DDD.PathEq

/-!
# Example: the Shipping context

Shipments with their items, customers, addresses and carriers. A shipment names
the order it ships by the value `orderId`; its items carry what Shipping
declares about the shipped goods. Whether a shipment needs a signature is a
`bool`. Addresses are value objects.

No equations, so the schema is free. Aggregates: a shipment with its items,
owned through `shipment`; customers, addresses and carriers on their own.

Checked with `decide`: well-formedness and acyclicity, and that a shipment's
destination need not be its customer's address.
-/

namespace DDD.Examples.Shipping

open Schema

/-- The Shipping schema. -/
def schema : Schema where
  entities := ["Customer", "Address", "Shipment", "Item", "Carrier"]
  refs := [⟨"address", "Customer", "Address"⟩, ⟨"customer", "Shipment", "Customer"⟩,
    ⟨"destination", "Shipment", "Address"⟩, ⟨"carrier", "Shipment", "Carrier"⟩,
    ⟨"shipment", "Item", "Shipment"⟩]
  attrs := [⟨"name", "Customer", .string⟩, ⟨"street", "Address", .string⟩,
    ⟨"city", "Address", .string⟩, ⟨"orderId", "Shipment", .uuid⟩,
    ⟨"shippedOn", "Shipment", .date⟩, ⟨"trackingCode", "Shipment", .string⟩,
    ⟨"signatureRequired", "Shipment", .bool⟩, ⟨"quantity", "Item", .int⟩,
    ⟨"declaredValue", "Item", .decimal⟩, ⟨"sku", "Item", .string⟩,
    ⟨"description", "Item", .string⟩, ⟨"name", "Carrier", .string⟩]
  aggregates := [⟨"Customer", []⟩, ⟨"Address", []⟩, ⟨"Shipment", [⟨"Item", "shipment"⟩]⟩,
    ⟨"Carrier", []⟩]
  valueObjects := ["Address"]

theorem wellFormed : schema.WellFormed := by decide

theorem free : schema.eqns = [] := rfl

theorem acyclic : schema.Acyclic := by decide

/-- The destination of a shipment need not be its customer's address. -/
theorem destination_ne :
    ¬ schema.PathEq ⟨.entity "Shipment", by decide⟩ ["destination"] ["customer", "address"] :=
  fun h => absurd ((pathEqFree_iff wellFormed free _ _ _).mpr h) (by decide)

end DDD.Examples.Shipping
