import DDD.ContextMap
import DDD.Examples.Catalog
import DDD.Examples.Orders
import DDD.Examples.Payments
import DDD.Examples.Shipping
import Showcase.ContextMapNotifications

/-!
# Example: the context map and its lax integration

Seven contexts: Catalog, Orders, Payments and Shipping, the published languages
CatalogPL and OrdersPL of Catalog and Orders, and `Customers`, the kernel that
Orders and Shipping share (customers with a name and an address, addresses with
a street and a city). The arrows, with their translations checked valid with
`decide`:

- CatalogPL → Catalog and OrdersPL → Orders: each published language included
  in its owner by the empty translation. Both contain roots only
  (`catalog_publishes`, `orders_publishes`).
- CatalogPL → Orders, an anti-corruption layer: a variant and its product both
  go to the Orders product, which keeps the variant's SKU, its price as list
  price, and the product's name; `product` goes to the identity.
- OrdersPL → Payments, an anti-corruption layer: an order goes to an invoice, a
  customer to a payer, and the billing address to the payer's address. Sending
  the billing address to the invoice's shipping address instead violates the
  equation `billTo = customer.address` and fails the check.
- Customers → Orders and Customers → Shipping: the kernel included in both by
  the empty translation. `Customers` is marked as a kernel; `Gluing.lean` merges
  Orders and Shipping along it.

Each context lies in a domain of `Showcase/ContextMapNotifications.lean`
(`domain`): a published language in the domain of its owner, the kernel in
Orders. Each arrow refines a route of the Showcase map (`domainRoute`): an
arrow inside a domain refines the empty route, the others an arrow between
domains, Customers → Shipping the arrow from Orders to Shipping. This gives a
functor `toDomains : J ⥤ Paths Domain`, and events from the domain of an
upstream context reach the domain of each downstream one (`reaches`).

`contextMap` declares no equation between routes, so `contextMap.J` is the free
category on the arrows, and `contextMap.diagram` is the context map as a functor
`J ⥤ Cat`. The map has no cycle (`rank`), so each context embeds into the lax
integration fully faithfully and injectively on objects (`nonInterference`).
`refundOfOrder` is a reference across contexts: from a refund in Payments to
the order it refunds in OrdersPL, as the morphism `refund ⟶ T order` of
Payments, where `T order` is the invoice. `publishedOrder` is the reference
from an order of Orders to the same order of OrdersPL, along the inclusion.
-/

namespace DDD.Examples.Integration

open CategoryTheory
open ContextMapNotifications (Domain Reaches)

/-! ## Contexts, arrows and schemas -/

/-- The contexts. -/
inductive Context where
  | Catalog | CatalogPL | Orders | OrdersPL | Customers | Payments | Shipping
deriving DecidableEq, Repr

/-- The arrows of the context map, from upstream to downstream. -/
inductive Arrow : Context → Context → Type where
  | catalogPL_catalog : Arrow .CatalogPL .Catalog
  | catalogPL_orders : Arrow .CatalogPL .Orders
  | ordersPL_orders : Arrow .OrdersPL .Orders
  | ordersPL_payments : Arrow .OrdersPL .Payments
  | customers_orders : Arrow .Customers .Orders
  | customers_shipping : Arrow .Customers .Shipping

instance : Quiver Context := ⟨Arrow⟩

/-- The kernel shared by Orders and Shipping: customers and their addresses. -/
def customers : Schema where
  entities := ["Customer", "Address"]
  refs := [⟨"address", "Customer", "Address"⟩]
  attrs := [⟨"name", "Customer", .string⟩, ⟨"street", "Address", .string⟩,
    ⟨"city", "Address", .string⟩]
  aggregates := [⟨"Customer", []⟩, ⟨"Address", []⟩]
  valueObjects := ["Address"]

theorem customers_wellFormed : customers.WellFormed := by decide

/-- The schema of each context. -/
def schema : Context → Schema
  | .Catalog => Catalog.schema
  | .CatalogPL => Catalog.published
  | .Orders => Orders.schema
  | .OrdersPL => Orders.published
  | .Customers => customers
  | .Payments => Payments.schema
  | .Shipping => Shipping.schema

theorem wellFormed : ∀ c, (schema c).WellFormed
  | .Catalog => Catalog.wellFormed
  | .CatalogPL => Catalog.published_wellFormed
  | .Orders => Orders.wellFormed
  | .OrdersPL => Orders.published_wellFormed
  | .Customers => customers_wellFormed
  | .Payments => Payments.wellFormed
  | .Shipping => Shipping.wellFormed

/-! ## Translations -/

/-- CatalogPL → Orders. -/
def catalogOrders : Translation where
  entities := [("Variant", "Product")]
  gens := [⟨"Variant", "product", []⟩, ⟨"Variant", "price", ["listPrice"]⟩]

/-- OrdersPL → Payments. -/
def ordersPayments : Translation where
  entities := [("Customer", "Payer"), ("Order", "Invoice")]
  gens := [⟨"Order", "customer", ["payer"]⟩, ⟨"Order", "billTo", ["payer", "address"]⟩,
    ⟨"Order", "id", ["orderId"]⟩, ⟨"Order", "placedOn", ["orderedOn"]⟩]

/-- The translation along each arrow; the inclusions are the empty translation. -/
def translation : {u d : Context} → Arrow u d → Translation
  | _, _, .catalogPL_orders => catalogOrders
  | _, _, .ordersPL_payments => ordersPayments
  | _, _, _ => {}

theorem catalogOrders_valid : catalogOrders.Valid Catalog.published Orders.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Orders.wellFormed a h)
    (by decide)

theorem ordersPayments_valid : ordersPayments.Valid Orders.published Payments.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Payments.wellFormed a h)
    (by decide)

theorem valid : ∀ {u d : Context} (f : Arrow u d),
    (translation f).Valid (schema u) (schema d)
  | _, _, .catalogPL_catalog =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Catalog.wellFormed a h)
      (by decide)
  | _, _, .catalogPL_orders => catalogOrders_valid
  | _, _, .ordersPL_orders =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Orders.wellFormed a h)
      (by decide)
  | _, _, .ordersPL_payments => ordersPayments_valid
  | _, _, .customers_orders =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Orders.wellFormed a h)
      (by decide)
  | _, _, .customers_shipping =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Shipping.wellFormed a h)
      (by decide)

/-- OrdersPL → Payments with the billing address sent to the invoice's shipping
address. It is not a translation: the equation `billTo = customer.address` goes
to `shipTo = payer.address`, which does not hold in Payments. -/
def ordersPaymentsBillToShipTo : Translation :=
  { ordersPayments with gens := ⟨"Order", "billTo", ["shipTo"]⟩ :: ordersPayments.gens }

theorem ordersPaymentsBillToShipTo_not_valid :
    ¬ ordersPaymentsBillToShipTo.Valid Orders.published Payments.schema := fun h =>
  absurd ((Translation.checkValid_iff (fun a l l' =>
    Schema.pathEq_iff_of_acyclic Payments.wellFormed Payments.acyclic a l l')).mpr h)
    (by decide)

/-! ## The context map -/

/-- `Customers` is the only kernel. -/
def kernel : Context → Bool
  | .Customers => true
  | _ => false

/-- The seven contexts, their schemas and translations, and the kernel. -/
def contextMap : ContextMap Context where
  schema := schema
  translation := translation
  wellFormed := wellFormed
  valid := valid
  kernel := kernel
  inclusion f h := by cases f <;> first | rfl | cases h

/-- The context map as a functor from the category of contexts to `Cat`. -/
example : contextMap.J ⥤ Cat := contextMap.diagram

/-- Catalog publishes CatalogPL: an inclusion, and roots only. -/
theorem catalog_publishes : contextMap.Publishes Arrow.catalogPL_catalog := by decide

/-- Orders publishes OrdersPL: an inclusion, and roots only. -/
theorem orders_publishes : contextMap.Publishes Arrow.ordersPL_orders := by decide

/-- Arrows go from a lower to a higher rank, so the map has no cycle. -/
def rank : Context → Nat
  | .CatalogPL | .OrdersPL | .Customers => 0
  | _ => 1

theorem rank_lt {u d : Context} (f : u ⟶ d) : rank u < rank d := by
  cases f <;> decide

/-- Lax non-interference for the seven contexts. -/
theorem nonInterference (c : Context) :
    (contextMap.embed c).Full ∧ (contextMap.embed c).Faithful ∧
      Function.Injective (contextMap.embed c).obj :=
  contextMap.nonInterference (contextMap.endo_eq_id (endo_eq_id_of_rank rank rank_lt)) c

/-! ## The projection onto the Showcase map -/

/-- The arrows of the Showcase map, as a quiver. -/
instance : Quiver Domain := ⟨fun u d => PLift (ContextMapNotifications.Arrow u d)⟩

/-- The domain of each context. -/
def domain : Context → Domain
  | .Catalog | .CatalogPL => .Catalog
  | .Orders | .OrdersPL | .Customers => .Orders
  | .Payments => .Payments
  | .Shipping => .Shipping

/-- The route of the Showcase map that each arrow refines. -/
def domainRoute : {u d : Context} → Arrow u d → Quiver.Path (domain u) (domain d)
  | _, _, .catalogPL_catalog => .nil
  | _, _, .catalogPL_orders => Quiver.Hom.toPath ⟨.catalog_orders⟩
  | _, _, .ordersPL_orders => .nil
  | _, _, .ordersPL_payments => Quiver.Hom.toPath ⟨.orders_payments⟩
  | _, _, .customers_orders => .nil
  | _, _, .customers_shipping => Quiver.Hom.toPath ⟨.orders_shipping⟩

/-- The projection onto the Showcase map, as a functor on the category of
contexts. -/
def toDomains : contextMap.J ⥤ Paths Domain :=
  CategoryTheory.Quotient.lift _ (Paths.lift { obj := domain, map := domainRoute })
    fun _ _ _ _ h => False.elim h

theorem toDomains_obj (c : Context) : toDomains.obj (contextMap.ctx c) = domain c := rfl

theorem reaches_of_path {a b : Domain} : Quiver.Path a b → Reaches a b
  | .nil => .refl _
  | .cons p f => .up (reaches_of_path p) f.down

/-- Events from the domain of an upstream context reach the domain of each
downstream context. -/
theorem reaches {u d : Context} (f : u ⟶ d) : Reaches (domain u) (domain d) :=
  reaches_of_path (domainRoute f)

/-! ## References across contexts -/

/-- The arrow from OrdersPL to Payments, as a morphism of `J`. -/
def ordersToPayments : contextMap.ctx .OrdersPL ⟶ contextMap.ctx .Payments :=
  contextMap.arrow .ordersPL_payments

/-- The refund entity type, in the schema category of Payments. -/
def refund : (contextMap.schema .Payments).cat := Schema.obj _ ⟨.entity "Refund", by decide⟩

/-- The order entity type, in the schema category of OrdersPL. -/
def order : (contextMap.schema .OrdersPL).cat := Schema.obj _ ⟨.entity "Order", by decide⟩

/-- The image of the order in Payments is the invoice. -/
theorem translate_order :
    (contextMap.diagram.map ordersToPayments).obj order =
      Schema.obj Payments.schema ⟨.entity "Invoice", by decide⟩ := rfl

/-- A refund refers to the order it refunds: the reference `invoice` from a refund
to the image of the order. -/
def refundOfOrder :
    (contextMap.embed .Payments).obj refund ⟶ (contextMap.embed .OrdersPL).obj order :=
  contextMap.ref ordersToPayments
    (Schema.mor (Payments.schema.pathOf Payments.wellFormed ⟨.entity "Refund", by decide⟩
      ⟨.entity "Invoice", by decide⟩ ["invoice"] (by decide)) ≫ eqToHom translate_order.symm)

/-- The reference lies over the arrow from OrdersPL to Payments. -/
theorem projection_refundOfOrder :
    contextMap.projection.map refundOfOrder = ordersToPayments.op := rfl

/-- The order entity type, in the schema category of Orders. -/
def orderOfOrders : (contextMap.schema .Orders).cat := Schema.obj _ ⟨.entity "Order", by decide⟩

/-- The inclusion of OrdersPL sends its order to the order of Orders. -/
theorem include_order :
    (contextMap.diagram.map (contextMap.arrow .ordersPL_orders)).obj order = orderOfOrders := rfl

/-- An order of Orders refers to the order it publishes, along the inclusion. -/
def publishedOrder :
    (contextMap.embed .Orders).obj orderOfOrders ⟶ (contextMap.embed .OrdersPL).obj order :=
  contextMap.ref (contextMap.arrow .ordersPL_orders) (eqToHom include_order.symm)

end DDD.Examples.Integration
