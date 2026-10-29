import DDD.StateSigma
import DDD.Examples.Integration
import DDD.Examples.Values

/-!
# Example: `Σ_T` along the arrows of the context map

`Σ_T` pushes the states of an upstream context into a downstream one. On
attributed states it exists exactly when the downstream schema neither adds nor
identifies paths into value types out of the images of upstream entity types
(`Translation.isRightAdjoint_restrictStateFunctor_iff`; every value type of `K`
has two values, `nontrivial`).

- Customers → Orders, Customers → Shipping and OrdersPL → Payments are fully
  faithful (`checkFullyFaithful`, by `decide +kernel`), so `Σ_T` exists along them:
  a customer of the kernel is a customer of Orders with the same name and
  address, an order of the published language an invoice of Payments with the
  same order id, date, payer and addresses.
- OrdersPL → Orders has no `Σ_T`: an order of Orders has a status, of the value
  type `OrderStatus`, and no path of the published language leads from an order
  to that value type.
- CatalogPL → Orders has no `Σ_T`: a product of Orders has a list price, of type
  `decimal`, and a product of the published language of Catalog has a name only.

States of each schema have all limits and colimits; pushouts, which merge two
states along a shared sub-state, are computed pointwise.
-/

namespace DDD.Examples.Sigma

open CategoryTheory Limits Translation Integration
open DDD.Examples.Values (K Decimal Date Uuid)

/-- Every value type of `K` has two values. -/
instance nontrivial : ∀ v, Nontrivial (K v)
  | .int => inferInstanceAs (Nontrivial Int)
  | .decimal => ⟨⟨⟨0, 0, Or.inl rfl⟩, ⟨1, 0, Or.inl rfl⟩, by decide⟩⟩
  | .string => ⟨⟨"", "a", by decide⟩⟩
  | .date => ⟨⟨⟨0⟩, ⟨1⟩, by decide⟩⟩
  | .uuid => ⟨⟨⟨0⟩, ⟨1⟩, by decide⟩⟩
  | .bool => inferInstanceAs (Nontrivial Bool)
  | .named _ => show Nontrivial String from ⟨⟨"", "a", by decide⟩⟩

/-! ## Arrows with `Σ_T` -/

theorem customers_orders_attrBijective :
    AttrBijective Orders.wellFormed (valid Arrow.customers_orders) :=
  have h := checkFullyFaithful_sound customers_wellFormed Orders.wellFormed (by decide)
    Orders.acyclic (valid Arrow.customers_orders) (by decide +kernel)
  attrBijective_of_fullyFaithful h.1 h.2

theorem customers_shipping_attrBijective :
    AttrBijective Shipping.wellFormed (valid Arrow.customers_shipping) :=
  have h := checkFullyFaithful_sound customers_wellFormed Shipping.wellFormed (by decide)
    Shipping.acyclic (valid Arrow.customers_shipping) (by decide +kernel)
  attrBijective_of_fullyFaithful h.1 h.2

theorem ordersPayments_attrBijective : AttrBijective Payments.wellFormed ordersPayments_valid :=
  have h := checkFullyFaithful_sound Orders.published_wellFormed Payments.wellFormed
    Orders.published_acyclic Payments.acyclic ordersPayments_valid (by decide +kernel)
  attrBijective_of_fullyFaithful h.1 h.2

/-- `Σ_T ⊣ Δ_T` along Customers → Orders. -/
noncomputable def customersOrders :
    sigmaStateFunctor (K := K) customers_orders_attrBijective ⊣
      restrictStateFunctor Orders.wellFormed (valid Arrow.customers_orders) :=
  sigmaStateAdjunction customers_orders_attrBijective

/-- `Σ_T ⊣ Δ_T` along Customers → Shipping. -/
noncomputable def customersShipping :
    sigmaStateFunctor (K := K) customers_shipping_attrBijective ⊣
      restrictStateFunctor Shipping.wellFormed (valid Arrow.customers_shipping) :=
  sigmaStateAdjunction customers_shipping_attrBijective

/-- `Σ_T ⊣ Δ_T` along OrdersPL → Payments: orders become invoices. -/
noncomputable def ordersInvoices :
    sigmaStateFunctor (K := K) ordersPayments_attrBijective ⊣
      restrictStateFunctor Payments.wellFormed ordersPayments_valid :=
  sigmaStateAdjunction ordersPayments_attrBijective

/-! ## Arrows without `Σ_T` -/

/-- An order of the published language has no status. -/
theorem not_sigma_ordersPL_orders :
    ¬ (restrictStateFunctor (K := K) Orders.wellFormed
      (valid Arrow.ordersPL_orders)).IsRightAdjoint := by
  rw [isRightAdjoint_restrictStateFunctor_iff]
  exact not_attrBijective Orders.published_acyclic (e := "Order") (by decide) (l := ["status"])
    (v := .named "OrderStatus") (by decide) (by decide)

/-- A product of the published language of Catalog has no list price. -/
theorem not_sigma_catalogPL_orders :
    ¬ (restrictStateFunctor (K := K) Orders.wellFormed catalogOrders_valid).IsRightAdjoint := by
  rw [isRightAdjoint_restrictStateFunctor_iff]
  exact not_attrBijective (by decide) (e := "Product") (by decide) (l := ["listPrice"])
    (v := .decimal) (by decide) (by decide)

/-! ## Limits and colimits -/

example : HasLimits (Orders.schema.State K) := inferInstance

example : HasColimits (Orders.schema.State K) := inferInstance

/-- Pushouts of states, which merge two states along a shared sub-state, are
computed pointwise. -/
example : PreservesColimitsOfShape WalkingSpan
    (Schema.State.toEntity (S := Orders.schema) (K := K)) := inferInstance

/-- Pullbacks of states are computed pointwise. -/
example : PreservesLimitsOfShape WalkingCospan
    (Schema.State.toEntity (S := Orders.schema) (K := K)) := inferInstance

end DDD.Examples.Sigma
