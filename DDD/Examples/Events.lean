import DDD.Events
import DDD.Examples.Exchange

/-!
# Example: an event type and its occurrences

The published language of Orders publishes the event type `OrderPlaced`
(`Exchange.orderPlaced`): a placed order, its customer, and the instant. Its event
schema is the published language with the entity type `OrderPlaced`, a value
object with two references and an attribute (`orderPlaced_check`,
`orderPlaced_entities`). An event type over Orders that refers to a line of an
order, a member of the order aggregate, fails the check (`lineAdded_check`). An
event type without fields is not a value object, which needs a field; its one
occurrence says that it happened (`ordersClosed_check`, `closed_orders`).

An occurrence names the order and the customer by their numbers in the published
state (`placed`).

- In Orders: the published state is the view of the state of Orders, its
  restriction along OrdersPL → Orders, which converts. The occurrence passes its
  check there (`placed_orders`), and its order is an order of Orders
  (`placed_resolves_orders`).
- In Payments: the state of Payments with an invoice for the order agrees with
  Orders on the published language, so it accepts the same occurrence
  (`placed_payments`, from `Occurrence.checkAt_of_agree`); the order of the
  occurrence is an invoice of Payments (`placed_resolves_payments`).
- Refused: an occurrence that names an order that is not there (`dangling_refused`),
  one without its customer (`missing_refused`), and, in Payments before the invoice,
  the occurrence itself: Payments does not hold the order yet
  (`placed_not_yet_payments`).
- As a state: the published state with the occurrence is a state of the event
  schema with one entity of the event type (`placedState`, `placed_one`).
- Emitted: an endpoint of OrdersPL emits the occurrence, and Payments, which calls
  it along the arrow from OrdersPL, receives the event and issues its invoice when
  the occurrence resolves in its state (`receive_events`). A dangling occurrence
  gives no event (`receive_dangling`), and Payments before the invoice gets the
  event and issues nothing (`receive_not_yet`).
- In a certificate: the claims `eventType` and `occurrence` (`certificate`), and the
  problem of a dangling reference in the report.
-/

set_option linter.hashCommand false

namespace DDD.Examples.Events

open Lean Integration Exchange
open ContextMapNotifications (Level)

/-! ## The event type -/

theorem orderPlaced_check : orderPlaced.check Orders.published = true := by decide

theorem orderPlaced_entities : (orderPlaced.over Orders.published).entities =
    ["Customer", "Address", "Order", "OrderPlaced"] := by
  decide

/-- An occurrence is identified by all its fields: the event type is a value
object of its schema. -/
theorem orderPlaced_valueObject :
    "OrderPlaced" ∈ (orderPlaced.over Orders.published).valueObjects := by
  decide

/-- An event type over Orders that refers to a line of an order. -/
def lineAdded : EventType where
  name := "LineAdded"
  refs := [("line", "OrderLine")]

/-- A line is a member of the order aggregate, and a reference from outside an
aggregate goes to its root: the event type fails its check. -/
theorem lineAdded_check : lineAdded.check Orders.schema = false := by decide

/-- An event type without fields over the published language. -/
def ordersClosed : EventType where
  name := "OrdersClosed"

theorem ordersClosed_check : ordersClosed.check Orders.published = true := by decide

theorem ordersClosed_notValueObject :
    "OrdersClosed" ∉ (ordersClosed.over Orders.published).valueObjects := by
  decide

/-! ## Occurrences -/

/-- The first order was placed by the first customer, at an instant. -/
def placed : Occurrence LitK where
  refs := [("order", 0), ("customer", 0)]
  attrs := [("at", ⟨.timestamp, .text "2026-09-30T23:30:00Z"⟩)]

/-- The state of Orders, with its literals in normal form. -/
abbrev ordersX : FinState LitK := ordersState.normalize valueTypes

/-- The state of Payments with an invoice for the order. -/
abbrev paymentsX : FinState LitK := paymentsState.normalize valueTypes

/-- The state of Payments before the invoice. -/
abbrev paymentsX₀ : FinState LitK := paymentsNoInvoice.normalize valueTypes

/-- In Orders, the occurrence passes its check: over the view of the state of
Orders, whose date of the order is the date of its instant. -/
theorem placed_orders : placed.checkAt valueTypes ordersPublish Orders.published Orders.schema
    orderPlaced ordersX = true := by
  decide +kernel

/-- The order of the occurrence is an order of Orders, and its customer a customer. -/
theorem placed_resolves_orders {r : String × String} (hr : r ∈ orderPlaced.refs) :
    ∃ i, placed.refs.lookup r.1 = some i ∧ i < ordersX.size (ordersPublish.ent r.2) :=
  Occurrence.resolvesAt orderPlaced_check placed_orders hr

/-- Orders and Payments agree on the published language. -/
theorem views_eq : ordersX.vrestrictLit valueTypes ordersPublish Orders.published Orders.schema =
    paymentsX.vrestrictLit valueTypes ordersPayments Orders.published Payments.schema := by
  decide +kernel

/-- Payments, which agrees with Orders on the published language, accepts the
occurrence. -/
theorem placed_payments : placed.checkAt valueTypes ordersPayments Orders.published
    Payments.schema orderPlaced paymentsX = true :=
  (Occurrence.checkAt_of_agree views_eq).symm.trans placed_orders

/-- In Payments, the order of the occurrence is an invoice, and its customer a
payer. -/
theorem placed_resolves_payments :
    (∃ i, placed.refs.lookup "order" = some i ∧ i < paymentsX.size "Invoice") ∧
      ∃ i, placed.refs.lookup "customer" = some i ∧ i < paymentsX.size "Payer" :=
  ⟨Occurrence.resolvesAt orderPlaced_check placed_payments (r := ("order", "Order")) (by decide),
    Occurrence.resolvesAt orderPlaced_check placed_payments (r := ("customer", "Customer"))
      (by decide)⟩

/-- An occurrence that names a second order. -/
def dangling : Occurrence LitK := { placed with refs := [("order", 1), ("customer", 0)] }

/-- There is one order: the occurrence is refused. -/
theorem dangling_refused : dangling.checkAt valueTypes ordersPublish Orders.published
    Orders.schema orderPlaced ordersX = false :=
  Occurrence.check_eq_false_of_dangling orderPlaced_check (r := ("order", "Order")) (by decide)
    (i := 1) (by decide) (by decide +kernel)

/-- An occurrence without its customer is refused. -/
theorem missing_refused : ({ placed with refs := [("order", 0)] } : Occurrence LitK).checkAt
    valueTypes ordersPublish Orders.published Orders.schema orderPlaced ordersX = false :=
  Occurrence.check_eq_false_of_missing orderPlaced_check (r := ("customer", "Customer"))
    (by decide) (by decide)

/-- Before the invoice, Payments holds no order of the published language: the
occurrence does not resolve there. -/
theorem placed_not_yet_payments : placed.checkAt valueTypes ordersPayments Orders.published
    Payments.schema orderPlaced paymentsX₀ = false := by
  decide +kernel

/-- The occurrence of the event type without fields passes its check in Orders. -/
theorem closed_orders : ({} : Occurrence LitK).checkAt valueTypes ordersPublish
    Orders.published Orders.schema ordersClosed ordersX = true := by
  decide +kernel

/-- The published state with the occurrence, as a state of the event schema. -/
def placedState : (orderPlaced.over Orders.published).State LitK :=
  placed.toState orderPlaced
    (ordersX.vrestrictLit valueTypes ordersPublish Orders.published Orders.schema) placed_orders

/-- It has one entity of the event type. -/
theorem placed_one : (placed.state orderPlaced
    (ordersX.vrestrictLit valueTypes ordersPublish Orders.published Orders.schema)).size
      "OrderPlaced" = 1 :=
  Occurrence.size_state_name _ _ _

/-! ## Emission -/

/-- The published state of Orders. -/
abbrev published : FinState LitK :=
  ordersX.vrestrictLit valueTypes ordersPublish Orders.published Orders.schema

/-- OrdersPL emits an occurrence of `OrderPlaced` over the published state. -/
def placeOrder : CEndpoint contextMap .OrdersPL (Occurrence LitK) Bool where
  handle occ := CSvc.emitOccurrence orderPlaced published occ

/-- Payments, with the state `X`, receives the occurrence along the arrow from
OrdersPL and issues an invoice when the occurrence resolves in its state. -/
def receiveOrder (X : FinState LitK) : CEndpoint contextMap .Payments (Occurrence LitK) Bool where
  handle occ := do
    let emitted ← CSvc.call Arrow.ordersPL_payments placeOrder occ
    if emitted && occ.checkAt valueTypes ordersPayments Orders.published Payments.schema
        orderPlaced X then
      CSvc.emit "InvoiceIssued" .high occ.text
      return true
    else return false

/-- The contexts and names of the events of a run, with its result. -/
def trace (s : CSvc contextMap .Payments Bool) : Bool × List (Context × String) :=
  (s.run.1, s.run.2.map fun e => (e.context, e.label))

/-- Payments receives the occurrence from OrdersPL and issues its invoice. -/
theorem receive_events : trace ((receiveOrder paymentsX).handle placed) =
    (true, [(.OrdersPL, "OrderPlaced"), (.Payments, "InvoiceIssued")]) := by
  decide +kernel

/-- A dangling occurrence is not emitted. -/
theorem receive_dangling : trace ((receiveOrder paymentsX).handle dangling) = (false, []) := by
  decide +kernel

/-- Before the invoice, Payments gets the event and issues nothing. -/
theorem receive_not_yet : trace ((receiveOrder paymentsX₀).handle placed) =
    (false, [(.OrdersPL, "OrderPlaced")]) := by
  decide +kernel

#guard ((receiveOrder paymentsX).handle placed).run.2.map (·.payload) ==
  ["order = #0, customer = #0, at = 2026-09-30T23:30:00Z",
   "order = #0, customer = #0, at = 2026-09-30T23:30:00Z"]

/-! ## In a certificate -/

/-- The claims about the event type and its occurrence, in Orders and in Payments. -/
def certificate : Certificate where
  valueTypes := valueTypes
  schemas := [("Orders", Orders.schema), ("OrdersPL", Orders.published),
    ("Payments", Payments.schema)]
  states := [("XO", "Orders", ordersX), ("XP", "Payments", paymentsX),
    ("XP0", "Payments", paymentsX₀)]
  claims := [.valueTypes, .eventType "OrdersPL" orderPlaced,
    .occurrence "OrdersPL" "Orders" ordersPublish orderPlaced "XO" placed,
    .occurrence "OrdersPL" "Payments" ordersPayments orderPlaced "XP" placed]

#guard certificate.check

-- A dangling reference is named in the report, with the number of entities.
#guard !certificate.checkClaim
  (.occurrence "OrdersPL" "Orders" ordersPublish orderPlaced "XO" dangling)
#guard ((certificate.explain
    (.occurrence "OrdersPL" "Orders" ordersPublish orderPlaced "XO" dangling)).map fun p =>
    (p.getObjValD "kind", p.getObjValD "field", p.getObjValD "count")) ==
  [(Json.str "danglingReference", Json.str "order", ((1 : Nat) : Json))]
#guard ((certificate.explain
    (.occurrence "OrdersPL" "Payments" ordersPayments orderPlaced "XP0" placed)).map
    (·.getObjValD "kind")) == [.str "danglingReference"]

-- An event type that refers to a member of an aggregate, and one named after an
-- entity type.
#guard (({ certificate with claims := [] } : Certificate).explain
    (.eventType "Orders" lineAdded)).map (·.getObjValD "kind") == [.str "aggregateBoundary"]
#guard (({ certificate with claims := [] } : Certificate).explain
    (.eventType "OrdersPL" { orderPlaced with name := "Order" })).map (·.getObjValD "kind") ==
  [.str "eventName"]

-- An occurrence round-trips through its JSON text, with the types of its event type.
#guard match Json.parse placed.toJson.compress >>= Occurrence.fromJson orderPlaced with
  | .ok occ => occ == placed
  | .error _ => false

end DDD.Examples.Events
