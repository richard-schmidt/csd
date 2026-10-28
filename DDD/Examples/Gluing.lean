import DDD.States
import DDD.Examples.Integration
import DDD.Examples.Values

/-!
# Example: Orders and Shipping glued along the Customers kernel

Strict integration of two contexts of the map in `Integration.lean`. Orders and
Shipping share the kernel `Customers`: customers with a name and an address,
addresses with a street and a city. Both include it with the same names, and
they share nothing else, so the two arrows out of the kernel glue (`gluing`,
from `ContextMap.kernelGluing`). The glued schema has the entity types of both,
the customer and address once, and the equations of both; its category is the
pushout of the images of the two arrows under `D` (`isPushout`).

Checked with `decide`: the gluing conditions, well-formedness and acyclicity of
the glued schema; with `decide +kernel`: strict non-interference, both legs are
fully faithful (`orders_fullyFaithful`, `shipping_fullyFaithful`). In the glued
schema the billing city of an order is still its customer's city. By the data
gluing theorem, a state of the glued schema with values in `Values.K` is a pair
of states of Orders and Shipping that agree on customers and addresses.

A failing kernel, outside the map: both contexts give customers a delivery
address besides their address, and Shipping assumes the two are equal while
Orders does not. The merge imposes Shipping's equation on Orders, so the leg
from Orders is not faithful (`delivery_not_faithful`), and the check fails.
-/

namespace DDD.Examples.Gluing

open CategoryTheory Schema Integration

/-- Orders and Shipping glued along the kernel. -/
def gluing : Gluing :=
  contextMap.kernelGluing Arrow.customers_orders Arrow.customers_shipping rfl (by decide)
    (by decide)

/-- The glued schema category is the pushout of the two inclusions of the
kernel. -/
theorem isPushout :
    IsPushout (contextMap.diagram.map (contextMap.arrow .customers_orders))
      (contextMap.diagram.map (contextMap.arrow .customers_shipping)) gluing.inl gluing.inr :=
  contextMap.isPushout_kernel _ _ _ _ _

theorem glued_entities : gluing.glued.entities =
    ["Customer", "Address", "Order", "OrderLine", "Product", "Shipment", "Item", "Carrier"] := by
  decide

theorem glued_acyclic : gluing.glued.Acyclic := by decide

/-- Strict non-interference for Orders. -/
theorem orders_fullyFaithful : gluing.inl.Full ∧ gluing.inl.Faithful :=
  Translation.checkFullyFaithful_sound Orders.wellFormed gluing.wf_glued Orders.acyclic
    glued_acyclic gluing.inl_valid (by decide +kernel)

/-- Strict non-interference for Shipping. -/
theorem shipping_fullyFaithful : gluing.inr.Full ∧ gluing.inr.Faithful :=
  Translation.checkFullyFaithful_sound Shipping.wellFormed gluing.wf_glued Shipping.acyclic
    glued_acyclic gluing.inr_valid (by decide +kernel)

/-- The equation of Orders still holds in the glued schema. -/
theorem billing_city :
    gluing.glued.PathEq ⟨.entity "Order", by decide⟩ ["billTo", "city"]
      ["customer", "address", "city"] :=
  (pathEqAcyclic_iff gluing.wf_glued glued_acyclic _ _ _).mp (by decide)

/-- Data gluing for the states of the examples. -/
example : gluing.glued.State Values.K ≃ { P : Orders.schema.State Values.K ×
    Shipping.schema.State Values.K //
      Translation.restrictState gluing.wf_left gluing.gluable.left P.1 =
        Translation.restrictState gluing.wf_right gluing.gluable.right P.2 } :=
  gluing.stateEquiv

/-! ## A failing kernel -/

/-- A delivery address for each customer. -/
def delivery : Ref := ⟨"deliveryAddress", "Customer", "Address"⟩

/-- The kernel with the delivery address. -/
def kernel₂ : Schema := { customers with refs := delivery :: customers.refs }

/-- Orders with a delivery address that may differ from the customer's address. -/
def orders₂ : Schema := { Orders.schema with refs := delivery :: Orders.schema.refs }

/-- Shipping, which delivers to the customer's address. -/
def shipping₂ : Schema :=
  { Shipping.schema with
    refs := delivery :: Shipping.schema.refs
    eqns := [⟨"Customer", ["deliveryAddress"], ["address"]⟩] }

theorem orders₂_wellFormed : orders₂.WellFormed := by decide

theorem orders₂_acyclic : orders₂.Acyclic := by decide

/-- The two glued along the kernel with the delivery address. The gluing
conditions hold: the delivery address is in the kernel. -/
def failing : Gluing where
  kernel := kernel₂
  left := orders₂
  right := shipping₂
  wf_kernel := by decide
  wf_left := orders₂_wellFormed
  wf_right := by decide
  wf_glued := by decide
  gluable := checkGluable_sound orders₂_wellFormed (by decide) (by decide)

theorem failing_acyclic : failing.glued.Acyclic := by decide

/-- The check fails for Orders. -/
theorem delivery_check : ({} : Translation).checkFullyFaithful orders₂ failing.glued = false := by
  decide +kernel

/-- The address of a customer, as a morphism of Orders. -/
def address : orders₂.obj ⟨.entity "Customer", by decide⟩ ⟶
    orders₂.obj ⟨.entity "Address", by decide⟩ :=
  orders₂.genMor "address" (by decide)

/-- The delivery address of a customer, as a morphism of Orders. -/
def deliveryAddress : orders₂.obj ⟨.entity "Customer", by decide⟩ ⟶
    orders₂.obj ⟨.entity "Address", by decide⟩ :=
  orders₂.genMor "deliveryAddress" (by decide)

/-- In Orders, the address and the delivery address differ. -/
theorem address_ne : address ≠ deliveryAddress := by
  intro h
  have hpe : orders₂.PathEq ⟨.entity "Customer", by decide⟩ ["address"] ["deliveryAddress"] :=
    ⟨_, _, _, rfl, rfl, h⟩
  exact absurd ((pathEqAcyclic_iff orders₂_wellFormed orders₂_acyclic _ _ _).mpr hpe)
    (by decide)

/-- In the glued schema they are equal: the equation of Shipping now holds for
Orders. -/
theorem address_glued : failing.inl.map address = failing.inl.map deliveryAddress := by
  simp only [address, deliveryAddress, Gluing.inl, genMor, Translation.functor_map_mor]
  apply PathEq.mor_eq
  rw [Translation.names_functorPath_empty, Translation.names_functorPath_empty]
  exact pathEq_sound failing.wf_glued _ (by decide)

/-- Strict non-interference fails: the leg from Orders is not faithful. -/
theorem delivery_not_faithful : ¬ failing.inl.Faithful := fun h =>
  address_ne (h.map_injective address_glued)

end DDD.Examples.Gluing
