import DDD.NormalForm
import DDD.Examples.Integration

/-!
# Example: the normal form of OrdersPL → Payments

The anti-corruption layer from the published language of Orders to Payments
(`Integration.ordersPayments`) renames customers to payers and orders to invoices,
and sends `customer`, `billTo`, `id` and `placedOn` to other paths of Payments. It
keeps the entity types apart, so it factors as an inclusion into a definitional
extension of Payments (`payments'`): Payments with payers named `Customer`,
invoices named `Order`, and the four derived generators with their equations, such
as `billTo = payer.address`.

Checked with `decide`: the normal form (`check`). The extension presents a
category isomorphic to that of Payments (`iso`), and the functor of the
translation is the inclusion followed by the isomorphism (`factor`). The published
language contains roots only of the extension (`rootsOnly`), and Payments, through
its extension, is an open schema with the published language of Orders as its
input (`paymentsOpen`). The translation from the published language of Catalog to
Orders sends variants and products to products, and has no normal form
(`catalogOrders_check`).
-/

namespace DDD.Examples.NormalForm

open CategoryTheory Schema Integration

/-- The definitional extension of Payments along OrdersPL → Payments. -/
abbrev payments' : Schema := ordersPayments.ext Orders.published Payments.schema

theorem derived : ordersPayments.derivedGens Orders.published =
    [("Order", "customer"), ("Order", "billTo"), ("Order", "id"), ("Order", "placedOn")] := by
  decide

theorem payments'_entities : payments'.entities =
    ["Customer", "Address", "Order", "InvoiceLine", "Payment", "Refund"] := by
  decide

/-- The billing address of an order is the address of its payer. -/
theorem billTo_eqn :
    (⟨"Order", ["billTo"], ["payer", "address"]⟩ : Equation) ∈ payments'.eqns := by
  decide

theorem check : ordersPayments.checkNormalForm Orders.published Payments.schema = true := by
  decide

/-- The normal form of OrdersPL → Payments. -/
def normalForm : ordersPayments.NormalForm Payments.wellFormed ordersPayments_valid :=
  Translation.normalForm Orders.published_wellFormed Payments.wellFormed ordersPayments_valid check

/-- The extension presents a category isomorphic to that of Payments. -/
def iso : payments'.cat ≅ Payments.schema.cat := normalForm.iso

/-- The functor of OrdersPL → Payments is the inclusion into the extension followed
by the isomorphism. -/
theorem factor : Translation.functor normalForm.wf normalForm.incl ⋙ iso.hom =
    Translation.functor Payments.wellFormed ordersPayments_valid :=
  normalForm.factor

/-- The published language of Orders contains roots only of the extension. -/
theorem rootsOnly : Orders.published.RootsOnly payments' := by decide

/-- Payments, through its extension, with the published language of Orders as its
input and nothing as its output. -/
def paymentsOpen : OpenSchema Orders.published emptySchema where
  S := payments'
  wfI := Orders.published_wellFormed
  wfO := by decide
  wf := normalForm.wf
  inI := normalForm.incl
  inO := Translation.checkValid_sound (fun a _ _ h => pathEq_sound normalForm.wf a h) (by decide)
  rootsI := rootsOnly
  rootsO := by decide

/-- CatalogPL → Orders sends variants and products to products: no normal form. -/
theorem catalogOrders_check :
    catalogOrders.checkNormalForm Catalog.published Orders.schema = false := by
  decide

end DDD.Examples.NormalForm
