import DDD.ContextMap
import DDD.Examples.Catalog
import DDD.Examples.Orders
import DDD.Examples.Payments
import DDD.Examples.Shipping
import Showcase.ContextMapNotifications

/-!
# Example: the four contexts and their lax integration

The context map of `Showcase/ContextMapNotifications.lean`: Catalog serves
Orders, and Orders serves Payments and Shipping. Each arrow carries a
translation from the upstream schema to the downstream one, checked valid with
`decide`. All three are anti-corruption layers:

- Catalog → Orders: a category, a product and a variant all go to the Orders
  product, which keeps the variant's SKU and list price, the product's name and
  the category's name; `parent`, `category` and `product` go to the identity.
- Orders → Payments: an order goes to an invoice, a customer to a payer, an
  order line and its product to one invoice line. The billing address is the
  payer's address.
- Orders → Shipping: an order goes to a shipment, an order line and its product
  to one item. The shipping address is the destination, the billing address the
  customer's address; the unit price and the list price are both the declared
  value. Sending the billing address to the destination instead violates the
  equation `billTo = customer.address` and fails the check.

`contextMap` puts the schemas and translations together, and `contextMap.diagram`
is the context map as a functor `Paths Domain ⥤ Cat`. The map has no cycle
(`rank`), so each context embeds into the lax integration fully faithfully and
injectively on objects (`nonInterference`). `refundOfOrder` is a reference
across contexts: from a refund in Payments to the order it refunds in Orders,
as the morphism `refund ⟶ T order` of Payments, where `T order` is the invoice.
-/

namespace DDD.Examples.Integration

open CategoryTheory ContextMapNotifications

/-! ## Translations -/

/-- Catalog → Orders. -/
def catalogOrders : Translation where
  entities := [("Category", "Product"), ("Variant", "Product")]
  gens := [⟨"Category", "parent", []⟩, ⟨"Category", "name", ["category"]⟩,
    ⟨"Product", "category", []⟩, ⟨"Variant", "product", []⟩,
    ⟨"Variant", "price", ["listPrice"]⟩]

/-- Orders → Payments. -/
def ordersPayments : Translation where
  entities := [("Customer", "Payer"), ("Order", "Invoice"), ("OrderLine", "InvoiceLine"),
    ("Product", "InvoiceLine")]
  gens := [⟨"Order", "customer", ["payer"]⟩, ⟨"Order", "billTo", ["payer", "address"]⟩,
    ⟨"Order", "id", ["orderId"]⟩, ⟨"Order", "placedOn", ["orderedOn"]⟩,
    ⟨"OrderLine", "order", ["invoice"]⟩, ⟨"OrderLine", "product", []⟩,
    ⟨"Product", "name", ["description"]⟩, ⟨"Product", "category", ["taxCategory"]⟩]

/-- Orders → Shipping. -/
def ordersShipping : Translation where
  entities := [("Order", "Shipment"), ("OrderLine", "Item"), ("Product", "Item")]
  gens := [⟨"Order", "billTo", ["customer", "address"]⟩, ⟨"Order", "shipTo", ["destination"]⟩,
    ⟨"Order", "id", ["orderId"]⟩, ⟨"Order", "placedOn", ["orderedOn"]⟩,
    ⟨"OrderLine", "order", ["shipment"]⟩, ⟨"OrderLine", "product", []⟩,
    ⟨"OrderLine", "unitPrice", ["declaredValue"]⟩, ⟨"Product", "name", ["description"]⟩,
    ⟨"Product", "listPrice", ["declaredValue"]⟩]

theorem catalogOrders_valid : catalogOrders.Valid Catalog.schema Orders.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Orders.wellFormed a h)
    (by decide)

theorem ordersPayments_valid : ordersPayments.Valid Orders.schema Payments.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Payments.wellFormed a h)
    (by decide)

theorem ordersShipping_valid : ordersShipping.Valid Orders.schema Shipping.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Shipping.wellFormed a h)
    (by decide)

/-- Orders → Shipping with the billing address sent to the destination. It is
not a translation: the equation `billTo = customer.address` of Orders goes to
`destination = customer.address`, which does not hold in Shipping. -/
def ordersShippingBillToDestination : Translation :=
  { ordersShipping with gens := ⟨"Order", "billTo", ["destination"]⟩ :: ordersShipping.gens }

theorem ordersShippingBillToDestination_not_valid :
    ¬ ordersShippingBillToDestination.Valid Orders.schema Shipping.schema := fun h =>
  absurd ((Translation.checkValid_iff
    (fun a l l' => Schema.pathEq_iff_of_free Shipping.wellFormed Shipping.free a l l')).mpr h)
    (by decide)

/-! ## The context map -/

/-- The arrows of the context map, as a quiver. -/
instance : Quiver Domain := ⟨fun u d => PLift (Arrow u d)⟩

/-- The schema of each context. -/
def schema : Domain → Schema
  | .Catalog => Catalog.schema
  | .Orders => Orders.schema
  | .Payments => Payments.schema
  | .Shipping => Shipping.schema

/-- The translation along each arrow. -/
def translation : Domain → Domain → Translation
  | .Catalog, .Orders => catalogOrders
  | .Orders, .Payments => ordersPayments
  | .Orders, .Shipping => ordersShipping
  | _, _ => {}

/-- The four contexts, their schemas and translations. -/
def contextMap : ContextMap Domain where
  schema := schema
  translation {u d} _ := translation u d
  wellFormed
    | .Catalog => Catalog.wellFormed
    | .Orders => Orders.wellFormed
    | .Payments => Payments.wellFormed
    | .Shipping => Shipping.wellFormed
  valid {u d} f := match u, d, f.down with
    | _, _, .catalog_orders => catalogOrders_valid
    | _, _, .orders_payments => ordersPayments_valid
    | _, _, .orders_shipping => ordersShipping_valid

/-- The context map as a functor from the free category of its arrows to `Cat`. -/
example : Paths Domain ⥤ Cat := contextMap.diagram

/-- Arrows go from a lower to a higher rank, so the map has no cycle. -/
def rank : Domain → Nat
  | .Catalog => 0
  | .Orders => 1
  | .Payments => 2
  | .Shipping => 2

theorem rank_lt {u d : Domain} (f : u ⟶ d) : rank u < rank d := by
  cases f.down <;> decide

/-- Lax non-interference for the four contexts. -/
theorem nonInterference (c : Domain) :
    (contextMap.embed c).Full ∧ (contextMap.embed c).Faithful ∧
      Function.Injective (contextMap.embed c).obj :=
  contextMap.nonInterference (endo_eq_id_of_rank rank rank_lt) c

/-! ## A reference across contexts -/

/-- The arrow from Orders to Payments, as a morphism of `J`. -/
def ordersToPayments : @Quiver.Hom (Paths Domain) _ .Orders .Payments :=
  (Paths.of Domain).map ⟨.orders_payments⟩

/-- The refund entity type, in the schema category of Payments. -/
def refund : (contextMap.schema .Payments).cat := Schema.obj _ ⟨.entity "Refund", by decide⟩

/-- The order entity type, in the schema category of Orders. -/
def order : (contextMap.schema .Orders).cat := Schema.obj _ ⟨.entity "Order", by decide⟩

/-- The image of the order in Payments is the invoice. -/
theorem translate_order :
    (contextMap.diagram.map ordersToPayments).obj order =
      Schema.obj Payments.schema ⟨.entity "Invoice", by decide⟩ := rfl

/-- A refund refers to the order it refunds: the reference `invoice` from a refund
to the image of the order. -/
def refundOfOrder :
    (contextMap.embed .Payments).obj refund ⟶ (contextMap.embed .Orders).obj order :=
  contextMap.ref ordersToPayments
    (Schema.mor (Payments.schema.pathOf Payments.wellFormed ⟨.entity "Refund", by decide⟩
      ⟨.entity "Invoice", by decide⟩ ["invoice"] (by decide)) ≫ eqToHom translate_order.symm)

/-- The reference lies over the arrow from Orders to Payments. -/
theorem projection_refundOfOrder :
    contextMap.projection.map refundOfOrder = ordersToPayments.op := rfl

end DDD.Examples.Integration
