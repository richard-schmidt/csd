import DDD.OpenMachine
import DDD.AggregateMachine
import DDD.Rename
import DDD.Events
import DDD.Examples.Merge
import DDD.Examples.Values

/-!
# Example: open systems

Three open schemas along the kernels of `Merge.lean`:

- `orders : Customers → Customers`: Orders, which takes customers in and shows its
  customers;
- `shipping : Customers → Addresses`: Shipping, which takes customers in and
  shows its addresses;
- `payments : Addresses → Addresses`: Payments, which takes addresses in and shows
  its addresses.

Each interface is included by the empty translation and contains roots only.
`orders ∘ shipping` glues Orders and Shipping along Customers, as
`Gluing.lean` does; with `payments`, the two composites of the three are
checked with `decide`, and their schema categories are isomorphic by
`assocIso`, compatibly with the legs. The identity on Customers composed with
`orders` gives back the schema category of Orders (`idCompIso`).

Qualified names: two ordering contexts that share customers, `orders` and a copy,
clash on every other name (`orders_clash`) and do not compose
(`not_orders_orders`). Qualifying the copy by `Store` keeps the names of
Customers and prefixes the others (`storeOrders`); the copy is isomorphic to
`orders` as an open schema (`storeOrdersIso`), and composes with it
(`orders_storeOrders`).

Machines: the conformist machines on `orders` and `shipping` take the customers
they receive into their state. Wired in series, Shipping receives the
customers of Orders one step late (`line_addresses`); the states stay in normal
form (`line_normal`). An update that would leave an order without its customer
fails the check and is refused (`refused`).

Aggregates: Orders has four aggregates (`orders_aggregates`), and both of its
equations cross them (`orders_cross`); the equation of Payments is internal to
the payment aggregate (`payments_internal`). A state of Orders is a compatible
family of aggregate states that satisfies the two equations (`contextEquiv`).
With a machine per aggregate, removing Ada is a step of the customer aggregate
that passes its check (`remove_ada`); the context then reports the open
reference of her order and the equation `billTo = customer.address` at that
order (`remove_ada_report`). A step that breaks a rule of its own aggregate is
refused (`bad_address_refused`).

Events: the projection `toDomains` of the example map sends the routes of `J` to
arrivals of events (`projection`). Payments invoices an order published by
OrdersPL; its events, the order's and the invoice's, become events of the
Orders and Payments domains (`invoice_domains`). No route of `J` leads from
OrdersPL to Customers, though both lie in the Orders domain
(`no_route_ordersPL_customers`), and none from Payments to Catalog
(`no_route_payments_catalog`, from `no_payment_events_in_catalog`).
-/

namespace DDD.Examples.Open

open CategoryTheory Schema Integration
open DDD.Examples.Values (K)

/-! ## Open schemas -/

/-- The inclusions of the kernels. -/
theorem addresses_shipping : ({} : Translation).Valid Merge.addresses Shipping.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Shipping.wellFormed a h)
    (by decide)

theorem addresses_payments : ({} : Translation).Valid Merge.addresses Payments.schema :=
  Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Payments.wellFormed a h)
    (by decide)

theorem addresses_wellFormed : Merge.addresses.WellFormed := by decide

/-- Orders, between customers in and customers out. -/
def orders : OpenSchema customers customers where
  S := Orders.schema
  wfI := customers_wellFormed
  wfO := customers_wellFormed
  wf := Orders.wellFormed
  inI := valid Arrow.customers_orders
  inO := valid Arrow.customers_orders
  rootsI := by decide
  rootsO := by decide

/-- Shipping, between customers in and addresses out. -/
def shipping : OpenSchema customers Merge.addresses where
  S := Shipping.schema
  wfI := customers_wellFormed
  wfO := addresses_wellFormed
  wf := Shipping.wellFormed
  inI := valid Arrow.customers_shipping
  inO := addresses_shipping
  rootsI := by decide
  rootsO := by decide

/-- Payments, between addresses in and addresses out. -/
def payments : OpenSchema Merge.addresses Merge.addresses where
  S := Payments.schema
  wfI := addresses_wellFormed
  wfO := addresses_wellFormed
  wf := Payments.wellFormed
  inI := addresses_payments
  inO := addresses_payments
  rootsI := by decide
  rootsO := by decide

theorem orders_shipping : orders.Composable shipping :=
  ⟨checkGluable_sound Orders.wellFormed Shipping.wellFormed (by decide), by decide, by decide,
    by decide⟩

theorem shipping_payments : shipping.Composable payments :=
  ⟨checkGluable_sound Shipping.wellFormed Payments.wellFormed (by decide), by decide, by decide,
    by decide⟩

theorem ordersShipping_payments : (orders.comp shipping orders_shipping).Composable payments :=
  ⟨checkGluable_sound orders_shipping.wf Payments.wellFormed (by decide), by decide, by decide,
    by decide⟩

theorem orders_shippingPayments : orders.Composable (shipping.comp payments shipping_payments) :=
  ⟨checkGluable_sound Orders.wellFormed shipping_payments.wf (by decide), by decide, by decide,
    by decide⟩

/-- The composite of Orders and Shipping is their gluing along Customers. -/
theorem ordersShipping_schema :
    (orders.comp shipping orders_shipping).S = glue Orders.schema Shipping.schema := rfl

theorem three_entities :
    ((orders.comp shipping orders_shipping).comp payments ordersShipping_payments).S.entities =
      ["Customer", "Address", "Order", "OrderLine", "Product", "Shipment", "Item", "Carrier",
        "Payer", "Invoice", "InvoiceLine", "Payment", "Refund"] := by
  decide

/-- The two composites of the three open schemas have isomorphic schema
categories, and the isomorphism commutes with the legs. -/
noncomputable def assoc :
    ((orders.comp shipping orders_shipping).comp payments ordersShipping_payments).S.cat ≅
      (orders.comp (shipping.comp payments shipping_payments) orders_shippingPayments).S.cat :=
  OpenSchema.assocIso orders shipping payments orders_shipping ordersShipping_payments
    shipping_payments orders_shippingPayments

example :
    ((orders.comp shipping orders_shipping).comp payments ordersShipping_payments).legI ⋙
        assoc.hom =
      (orders.comp (shipping.comp payments shipping_payments) orders_shippingPayments).legI :=
  OpenSchema.assocIso_legI _ _ _ _ _ _ _

/-- The identity on Customers. -/
def idCustomers : OpenSchema customers customers :=
  OpenSchema.id customers customers_wellFormed (by decide)

theorem idCustomers_orders : idCustomers.Composable orders :=
  ⟨checkGluable_sound customers_wellFormed Orders.wellFormed (by decide), by decide, by decide,
    by decide⟩

/-- Composing the identity with Orders gives back the schema category of Orders. -/
noncomputable example : (idCustomers.comp orders idCustomers_orders).S.cat ≅ Orders.schema.cat :=
  orders.idCompIso _ _ idCustomers_orders

/-! ## Qualified names -/

/-- Two ordering contexts that share customers clash on every other name. -/
theorem orders_clash : gluingClashes customers Orders.schema Orders.schema =
    ["Order", "OrderLine", "Product", "Order.customer", "Order.billTo", "Order.shipTo",
      "OrderLine.order", "OrderLine.product", "Order.id", "Order.placedOn", "Order.status",
      "OrderLine.quantity", "OrderLine.unitPrice", "OrderLine.sku", "Product.sku",
      "Product.name", "Product.listPrice"] := by
  decide

theorem not_orders_orders : ¬ orders.Composable orders := fun h =>
  absurd (h.gluable.entities "Order" (by decide) (by decide)) (by decide)

theorem storeOrders_check : orders.checkQualify "Store" = true := by decide

/-- The second ordering context, its names outside Customers qualified by `Store`. -/
def storeOrders : OpenSchema customers customers := orders.qualify storeOrders_check

theorem storeOrders_entities : storeOrders.S.entities =
    ["Customer", "Address", "Store.Order", "Store.OrderLine", "Store.Product"] := by
  decide

/-- The equations follow the names: `Store.billTo = Store.customer.address`. -/
theorem storeOrders_eqns : storeOrders.S.eqns =
    [⟨"Store.Order", ["Store.billTo"], ["Store.customer", "address"]⟩,
      ⟨"Store.OrderLine", ["Store.sku"], ["Store.product", "Store.sku"]⟩] := by
  decide

/-- The copy is isomorphic to `orders`, compatibly with the interfaces. -/
def storeOrdersIso : orders.Iso storeOrders := orders.qualifyIso storeOrders_check

example : Orders.schema.cat ≅ storeOrders.S.cat := storeOrdersIso.catIso

theorem orders_storeOrders : orders.Composable storeOrders :=
  ⟨checkGluable_sound Orders.wellFormed storeOrders.wf (by decide), by decide, by decide,
    by decide⟩

theorem two_orders_entities : (orders.comp storeOrders orders_storeOrders).S.entities =
    ["Customer", "Address", "Order", "OrderLine", "Product", "Store.Order", "Store.OrderLine",
      "Store.Product"] := by
  decide

/-! ## Machines -/

/-- The state of a schema with no entity. -/
def empty (S : Schema) : FinState K where
  sizes := S.entities.map (·, 0)
  refs := S.refs.map fun r => ((r.src, r.name), [])
  attrs := S.attrs.map fun a => ((a.src, a.name), [])

/-- One customer, Ada, at Main St in Bern. -/
def ada : FinState K where
  sizes := [("Customer", 1), ("Address", 1)]
  refs := [(("Customer", "address"), [0])]
  attrs := [(("Customer", "name"), [⟨.string, "Ada"⟩]),
    (("Address", "street"), [⟨.string, "Main St"⟩]), (("Address", "city"), [⟨.string, "Bern"⟩])]

def adaState : CheckedState K customers := ⟨ada, by decide⟩

def ordersStart : CheckedState K Orders.schema := ⟨empty Orders.schema, by decide⟩

def shippingStart : CheckedState K Shipping.schema := ⟨empty Shipping.schema, by decide⟩

/-- Orders and Shipping in series: Orders takes the customers it is given, Shipping
those Orders shows. -/
def line : Production.Machine ((orders.comp shipping orders_shipping).box K) :=
  (OpenMachine.conformist orders).comp (OpenMachine.conformist shipping) orders_shipping

/-- The addresses Shipping shows: none, none, then Ada's. Shipping receives Ada one
step after Orders. -/
theorem line_addresses :
    (line.run (ordersStart, shippingStart) [adaState, adaState]).map (·.1.size "Address") =
      [0, 0, 1] := by
  decide

/-- After three steps the state of Orders lists its five entity types and nothing
else: the conformist machine keeps its state in normal form. -/
theorem line_normal :
    (show CheckedState K Orders.schema × CheckedState K Shipping.schema from
      line.final (ordersStart, shippingStart) [adaState, adaState, adaState]).1.1.sizes.length =
      5 := by
  decide

/-- An order of customer 0, with no customer: the state fails the check. With Ada
as customer 0, it passes. -/
def orderOfAda : FinState K where
  sizes := [("Customer", 1), ("Address", 1), ("Order", 1), ("OrderLine", 0), ("Product", 0)]
  refs := [(("Customer", "address"), [0]), (("Order", "customer"), [0]), (("Order", "billTo"), [0]),
    (("Order", "shipTo"), [0]), (("OrderLine", "order"), []), (("OrderLine", "product"), [])]
  attrs := [(("Customer", "name"), [⟨.string, "Ada"⟩]),
    (("Address", "street"), [⟨.string, "Main St"⟩]), (("Address", "city"), [⟨.string, "Bern"⟩]),
    (("Order", "id"), [⟨.uuid, ⟨0⟩⟩]), (("Order", "placedOn"), [⟨.date, ⟨20000⟩⟩]),
    (("Order", "status"), [⟨.named "OrderStatus", "placed"⟩]),
    (("OrderLine", "quantity"), []), (("OrderLine", "unitPrice"), []), (("OrderLine", "sku"), []),
    (("Product", "sku"), []), (("Product", "name"), []), (("Product", "listPrice"), [])]

def orderOfAdaState : CheckedState K Orders.schema := ⟨orderOfAda, by decide⟩

def noCustomers : CheckedState K customers := ⟨empty customers, by decide⟩

/-- Taking no customers would leave the order without its customer: the update is
refused, and the state stays. -/
theorem refused : (OpenMachine.conformist orders).update orderOfAdaState noCustomers =
    orderOfAdaState :=
  OpenMachine.conformist_update_of_not_check _ _ _ (by decide)

/-! ## Aggregates -/

/-- The aggregates of Orders: customers, addresses, orders with their lines, and
products. -/
theorem orders_aggregates : Orders.schema.allAggregates =
    [⟨"Customer", []⟩, ⟨"Address", []⟩, ⟨"Order", [⟨"OrderLine", "order"⟩]⟩,
      ⟨"Product", []⟩] := by
  decide

/-- The aggregate schema of an order: the order and its lines, and the customers,
addresses and products it refers to, as identities. -/
theorem order_aggregate_entities :
    (Orders.schema.aggregateSchema ⟨"Order", [⟨"OrderLine", "order"⟩]⟩).entities =
      ["Order", "OrderLine", "Customer", "Address", "Product"] := by
  decide

/-- Both equations of Orders cross aggregates: `customer.address` and `product.sku`
leave the order aggregate through an identity. -/
theorem orders_cross : Orders.schema.crossAggregateEqns = Orders.schema.eqns := by decide

/-- The equation of Payments is internal to the payment aggregate: a refund and its
payment both belong to it, and both sides end at the identity of the invoice. -/
theorem payments_internal : Payments.schema.crossAggregateEqns = [] := by decide

theorem payment_aggregate_eqns :
    (Payments.schema.aggregateSchema ⟨"Payment", [⟨"Refund", "payment"⟩]⟩).eqns =
      Payments.schema.eqns := by
  decide

/-- A state of Orders is a compatible family of states of its four aggregate
schemas whose glued state satisfies the two equations across aggregates. -/
noncomputable example :
    Orders.schema.State K ≃ { X : { X : ∀ A : Orders.schema.Aggs,
        (Orders.schema.aggregateSchema A.1).State K // Compatible X } //
      ∀ q ∈ Orders.schema.crossAggregateEqns,
        Satisfies ((familyEquiv Orders.wellFormed (by decide)).symm X).F q } :=
  contextEquiv Orders.wellFormed (by decide)

/-- The customer aggregate. -/
def customerAgg : Orders.schema.Aggs := ⟨⟨"Customer", []⟩, by decide⟩

/-- A machine per aggregate of Orders: a command proposes a new state of the
aggregate. -/
def ordersAggregates (A : Orders.schema.Aggs) :
    Production.Machine ⟨FinState K, CheckedState K (Orders.schema.aggregateSchema A.1)⟩ :=
  aggregateMachine K Orders.wellFormed A fun _ m => m

/-- Orders as its aggregate machines side by side. -/
def ordersContext :
    Production.Machine ⟨Σ _ : Orders.schema.Aggs, FinState K, List Violation⟩ :=
  contextMachine ordersAggregates

/-- Ada with her order, as a state of each aggregate. -/
def adaParts : ∀ A : Orders.schema.Aggs, CheckedState K (Orders.schema.aggregateSchema A.1) :=
  orderOfAdaState.parts Orders.wellFormed

/-- The customer aggregate with Ada removed. -/
def noAda : FinState K where
  sizes := [("Customer", 0), ("Address", 1)]
  refs := [(("Customer", "address"), [])]
  attrs := [(("Customer", "name"), [])]

theorem noAda_check : noAda.check (Orders.schema.aggregateSchema customerAgg.1) = true := by
  decide

/-- Removing Ada is a step of the customer aggregate that passes its check. -/
theorem remove_ada : (ordersAggregates customerAgg).lens.update (adaParts customerAgg) noAda =
    CheckedState.normalize (aggregateSchema_wellFormed Orders.wellFormed customerAgg.2)
      ⟨noAda, noAda_check⟩ :=
  aggregateMachine_update_of_check _ _ _ _ _ noAda_check

/-- The context reports nothing before the step. After it, the context reports the
open reference of Ada's order, and the equation `billTo = customer.address`, which
no longer holds at that order. The same removal through the interface of Orders
is refused (`refused`). -/
theorem remove_ada_report : ordersContext.run adaParts [⟨customerAgg, noAda⟩] =
    [[], [.dangling "Order" "customer" 0 0,
      .eqn ⟨"Order", ["billTo"], ["customer", "address"]⟩ 0]] := by
  decide

/-- Ada's address set to an address the customer aggregate does not hold. -/
def badAddress : FinState K where
  sizes := [("Customer", 1), ("Address", 1)]
  refs := [(("Customer", "address"), [3])]
  attrs := [(("Customer", "name"), [⟨.string, "Ada"⟩])]

/-- A step that breaks a rule of its own aggregate is refused. -/
theorem bad_address_refused :
    (ordersAggregates customerAgg).lens.update (adaParts customerAgg) badAddress =
      adaParts customerAgg :=
  aggregateMachine_update_of_not_check _ _ _ _ _ (by decide)

/-! ## Events -/

open ContextMapNotifications (Level Reaches no_payment_events_in_catalog)

/-- The projection of the example map onto the Showcase map, through `toDomains`. -/
def projection : Projection contextMap where
  domain := domain
  reaches φ := reaches_of_path (toDomains.map φ)

/-- OrdersPL publishes an order. -/
def publishOrder : CEndpoint contextMap .OrdersPL Nat Nat where
  handle n := do
    CSvc.emit "OrderPublished" .low s!"order {n}"
    return n

/-- Payments invoices an order that OrdersPL publishes, along the arrow from OrdersPL
to Payments. -/
def invoiceOrder : CEndpoint contextMap .Payments Nat Unit where
  handle n := do
    let _ ← CSvc.call Arrow.ordersPL_payments publishOrder n
    CSvc.emit "InvoiceIssued" .high s!"invoice for order {n}"

theorem invoice_contexts : ((invoiceOrder.handle 7).run.2.map (·.context)) =
    [.OrdersPL, .Payments] := rfl

/-- Through the projection, the events come from the Orders and Payments domains. -/
theorem invoice_domains : (((invoiceOrder.handle 7).toSvc projection).run.2.map (·.domain)) =
    [.Orders, .Payments] := rfl

/-- The contexts reachable from OrdersPL. -/
def belowOrdersPL : Context → Bool
  | .OrdersPL | .Orders | .Payments => true
  | _ => false

theorem belowOrdersPL_path {u d : Context} (p : Quiver.Path u d) (hu : belowOrdersPL u = true) :
    belowOrdersPL d = true := by
  induction p with
  | nil => exact hu
  | cons p f ih => cases f <;> simp_all [belowOrdersPL]

/-- No route leads from OrdersPL to Customers, though both lie in the Orders domain:
no event of OrdersPL reaches Customers. -/
theorem no_route_ordersPL_customers :
    IsEmpty (contextMap.ctx .OrdersPL ⟶ contextMap.ctx .Customers) :=
  ⟨fun φ => by
    obtain ⟨p, -⟩ := contextMap.route_surjective φ
    have h := belowOrdersPL_path p rfl
    simp [belowOrdersPL] at h⟩

/-- No route leads from Payments to Catalog. -/
theorem no_route_payments_catalog :
    IsEmpty (contextMap.ctx .Payments ⟶ contextMap.ctx .Catalog) :=
  projection.isEmpty_hom no_payment_events_in_catalog

end DDD.Examples.Open
