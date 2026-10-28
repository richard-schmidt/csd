import DDD.PathEq

/-!
# Example: the Payments context

Invoices with their lines, payers and addresses, payments of invoices, and
refunds of payments. An invoice is the Payments view of an order; its lines
carry what Payments keeps of the ordered products.

One equation: a refund's invoice is the invoice of its payment,
`invoice = payment.invoice`.

Aggregates: an invoice with its lines, owned through `invoice`; a payment with
its refunds, owned through `payment`; payers and addresses on their own.

Checked with `decide`: well-formedness, acyclicity, and the equation in a
longer path.
-/

namespace DDD.Examples.Payments

open Schema

/-- The Payments schema. -/
def schema : Schema where
  entities := ["Payer", "Address", "Invoice", "InvoiceLine", "Payment", "Refund"]
  refs := [⟨"address", "Payer", "Address"⟩, ⟨"payer", "Invoice", "Payer"⟩,
    ⟨"shipTo", "Invoice", "Address"⟩, ⟨"invoice", "InvoiceLine", "Invoice"⟩,
    ⟨"invoice", "Payment", "Invoice"⟩, ⟨"payment", "Refund", "Payment"⟩,
    ⟨"invoice", "Refund", "Invoice"⟩]
  attrs := [⟨"name", "Payer", .string⟩, ⟨"street", "Address", .string⟩,
    ⟨"city", "Address", .string⟩, ⟨"orderId", "Invoice", .uuid⟩,
    ⟨"orderedOn", "Invoice", .date⟩, ⟨"quantity", "InvoiceLine", .int⟩,
    ⟨"unitPrice", "InvoiceLine", .decimal⟩, ⟨"listPrice", "InvoiceLine", .decimal⟩,
    ⟨"sku", "InvoiceLine", .string⟩, ⟨"description", "InvoiceLine", .string⟩,
    ⟨"taxCategory", "InvoiceLine", .string⟩, ⟨"amount", "Payment", .decimal⟩,
    ⟨"paidOn", "Payment", .date⟩, ⟨"amount", "Refund", .decimal⟩,
    ⟨"issuedOn", "Refund", .date⟩]
  eqns := [⟨"Refund", ["invoice"], ["payment", "invoice"]⟩]
  aggregates := [⟨"Payer", []⟩, ⟨"Address", []⟩, ⟨"Invoice", [⟨"InvoiceLine", "invoice"⟩]⟩,
    ⟨"Payment", [⟨"Refund", "payment"⟩]⟩]

theorem wellFormed : schema.WellFormed := by decide

theorem acyclic : schema.Acyclic := by decide

/-- A refund is paid back to the payer of its payment's invoice. -/
theorem refund_payer :
    schema.PathEq ⟨.entity "Refund", by decide⟩ ["invoice", "payer", "name"]
      ["payment", "invoice", "payer", "name"] :=
  (pathEqAcyclic_iff wellFormed acyclic _ _ _).mp (by decide)

end DDD.Examples.Payments
