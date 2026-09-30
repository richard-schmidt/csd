/-!
# Notifications that follow the context map

A service in a domain emits domain events and calls the endpoints of other domains.
The context map says which calls are allowed: a downstream domain may call its
upstream domains, never the reverse. Here that rule is a type:

* `Svc D α` is a computation running in domain `D`. It returns a value and the events
  it caused, and it carries a proof that every one of those events comes from `D` or
  from a domain upstream of `D`.
* `emit` tags an event with the domain it runs in; nothing else can create events.
* `call` needs an `Upstream U D` instance: a call against the context map does not
  compile.

Core Lean only; grew out of `NotificationsMonad.lean`.
-/

namespace ContextMapNotifications

inductive Domain where
  | Catalog | Orders | Payments | Shipping
deriving DecidableEq, Repr

/-- The context map as a closed list of arrows: `Arrow u d` means `u` is upstream of
`d`. Closed on purpose: facts such as "no path from Payments to Catalog" can only be
proved about a map nobody can extend elsewhere. -/
inductive Arrow : Domain → Domain → Prop
  | catalog_orders   : Arrow .Catalog .Orders
  | orders_payments  : Arrow .Orders .Payments
  | orders_shipping  : Arrow .Orders .Shipping

/-- What `call` asks for; Lean finds it from the arrows, or the call does not compile. -/
class Upstream (u d : Domain) : Prop where
  arrow : Arrow u d

instance : Upstream .Catalog .Orders := ⟨.catalog_orders⟩
instance : Upstream .Orders .Payments := ⟨.orders_payments⟩
instance : Upstream .Orders .Shipping := ⟨.orders_shipping⟩

/-- `Reaches a d`: an event from `a` may arrive in `d`, through zero or more arrows. -/
inductive Reaches : Domain → Domain → Prop
  | refl (d) : Reaches d d
  | up {a u d} : Reaches a u → Arrow u d → Reaches a d

inductive Level where
  | critical | high | medium | low
deriving DecidableEq, Repr

structure Event where
  domain  : Domain
  label   : String
  level   : Level
  payload : String
deriving DecidableEq, Repr

/-- A computation in domain `D`: a value, the events it caused in the order they
happened, and the proof that each event may arrive in `D`. -/
def Svc (D : Domain) (α : Type) : Type :=
  { r : α × List Event // ∀ e ∈ r.2, Reaches e.domain D }

namespace Svc

def run {D α} (s : Svc D α) : α × List Event := s.val

def pure {D α} (a : α) : Svc D α := ⟨(a, []), by simp⟩

/-- Sequencing: the events of the first step, then those of the second. -/
def bind {D α β} (s : Svc D α) (f : α → Svc D β) : Svc D β :=
  ⟨((f s.val.1).val.1, s.val.2 ++ (f s.val.1).val.2), by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact s.property e h
    · exact (f s.val.1).property e h⟩

instance (D) : Monad (Svc D) where
  pure := Svc.pure
  bind := Svc.bind

theorem ext {D α} {s t : Svc D α} (h : s.run = t.run) : s = t := Subtype.ext h

instance (D) : LawfulMonad (Svc D) := LawfulMonad.mk'
  (id_map := fun s => ext (by
    show ((s.val.1, s.val.2 ++ [])) = s.val
    simp))
  (pure_bind := fun a f => ext (by
    show ((f a).val.1, [] ++ (f a).val.2) = (f a).val
    simp))
  (bind_assoc := fun s f g => ext (by
    show ((g (f s.val.1).val.1).val.1, (s.val.2 ++ (f s.val.1).val.2) ++ (g (f s.val.1).val.1).val.2)
       = ((g (f s.val.1).val.1).val.1, s.val.2 ++ ((f s.val.1).val.2 ++ (g (f s.val.1).val.1).val.2))
    simp))

end Svc

/-- Emit an event. It is tagged with the domain the computation runs in, always. -/
def emit {D} (label : String) (level : Level) (payload : String) : Svc D Unit :=
  ⟨((), [⟨D, label, level, payload⟩]), by
    intro e he
    simp at he
    subst he
    exact .refl D⟩

/-- An endpoint of domain `D`. -/
structure Endpoint (D : Domain) (α β : Type) where
  handle : α → Svc D β

/-- Call an endpoint of `U` from `D`: only along an arrow of the context map. The
callee's events come back to the caller, in order. -/
def call {U D α β} [h : Upstream U D] (e : Endpoint U α β) (a : α) : Svc D β :=
  ⟨(e.handle a).val, fun ev hev => .up ((e.handle a).property ev hev) h.arrow⟩

/-! ## What the types guarantee -/

/-- Every event a service of `D` returns comes from `D` or from upstream of `D`. -/
theorem events_reach {D α} (s : Svc D α) : ∀ e ∈ s.run.2, Reaches e.domain D :=
  s.property

/-- Regrouping steps never loses, duplicates or reorders events. -/
theorem events_bind {D α β} (s : Svc D α) (f : α → Svc D β) :
    (s >>= f).run.2 = s.run.2 ++ (f s.run.1).run.2 := rfl

/-- Nothing in `Payments` can reach `Catalog`: no arrow leaves `Payments` toward it. -/
theorem no_payment_events_in_catalog : ¬ Reaches .Payments .Catalog := by
  intro h
  generalize ha : Domain.Payments = a at h
  generalize hd : Domain.Catalog = d at h
  induction h with
  | refl => cases ha; cases hd
  | up _ hu ih =>
    subst hd
    cases hu   -- the only arrow into Catalog would have to start somewhere: there is none

/-! ## The example: repricing an order line -/

structure ChangePrice where
  productId : Nat
  price     : Nat

def changePrice : Endpoint .Catalog ChangePrice Nat where
  handle c := do
    emit "PriceChanged" .low s!"product {c.productId} now costs {c.price}"
    return c.price

structure RepriceOrderLine where
  orderId   : Nat
  productId : Nat
  price     : Nat

def repriceOrderLine : Endpoint .Orders RepriceOrderLine Bool where
  handle c := do
    let p ← call changePrice ⟨c.productId, c.price⟩
    emit "OrderLineRepriced" .high s!"product {c.productId} in order {c.orderId} repriced to {p}"
    return true

#eval (repriceOrderLine.handle ⟨1, 2, 3⟩).run


/-! Catalog is upstream of Orders, so Catalog may not call Orders. The call is
rejected when it is written: no instance `Upstream Domain.Orders Domain.Catalog`.
(`#check_failure` itself fails if the term ever compiles.) -/
#check_failure (call repriceOrderLine ⟨1, 2, 3⟩ : Svc .Catalog Bool)

end ContextMapNotifications
