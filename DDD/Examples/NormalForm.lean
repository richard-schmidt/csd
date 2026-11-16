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

An owner and a consumer composed along a published language: Catalog includes
its published language (`catalogOpen`), and a storefront reads it through an
anti-corruption layer that renames everything (`catalogStorefront`). The normal
form of that translation makes the storefront an open schema with the published
language as input (`storefrontOpen`), so the two compose by gluing
(`catalog_storefront`, `catalogWithStorefront`): one schema with the entity types
of Catalog, the generators of both, and the equations `name = title` and the like.
The published language of Orders is not composed this way: its translation into
Orders converts, and a translation that converts has no normal form.

Keys: `catalogStorefront` keeps the key of a variant by its SKU through the
renamed field `code` (`storefront_keysKept`), and `catalogOrders` keeps a key of a
variant by its product and SKU because `product` goes to the empty path
(`catalogOrders_keysKept`).
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

/-! ## An owner and a consumer composed along a published language -/

/-- A storefront, a second consumer of the published language of Catalog: listings
with a title, and offers of a listing with a code and an amount. -/
def storefront : Schema where
  entities := ["Listing", "Offer"]
  refs := [⟨"listing", "Offer", "Listing"⟩]
  attrs := [⟨"title", "Listing", .string⟩, ⟨"code", "Offer", .string⟩,
    ⟨"amount", "Offer", .decimal⟩]
  aggregates := [⟨"Listing", []⟩, ⟨"Offer", []⟩]
  keys := [⟨"Offer", ["code"]⟩]

theorem storefront_wellFormed : storefront.WellFormed := by decide

/-- CatalogPL → Storefront, an anti-corruption layer: a product is a listing, a
variant an offer. -/
def catalogStorefront : Translation where
  entities := [("Product", "Listing"), ("Variant", "Offer")]
  gens := [⟨"Product", "name", ["title"]⟩, ⟨"Variant", "product", ["listing"]⟩,
    ⟨"Variant", "sku", ["code"]⟩, ⟨"Variant", "price", ["amount"]⟩]

theorem catalogStorefront_valid : catalogStorefront.Valid Catalog.published storefront :=
  Translation.checkValid_sound (fun a _ _ h => pathEq_sound storefront_wellFormed a h) (by decide)

/-- The definitional extension of the storefront along CatalogPL → Storefront:
listings named `Product`, offers named `Variant`, and the derived generators
`name = title`, `product = listing`, `sku = code` and `price = amount`. -/
abbrev storefront' : Schema := catalogStorefront.ext Catalog.published storefront

theorem storefront_check :
    catalogStorefront.checkNormalForm Catalog.published storefront = true := by
  decide

/-- The normal form of CatalogPL → Storefront. -/
def storefrontNormalForm :
    catalogStorefront.NormalForm storefront_wellFormed catalogStorefront_valid :=
  Translation.normalForm Catalog.published_wellFormed storefront_wellFormed
    catalogStorefront_valid storefront_check

/-- Catalog, with nothing as its input and its published language as its output:
the owner includes its published language. -/
def catalogOpen : OpenSchema emptySchema Catalog.published where
  S := Catalog.schema
  wfI := by decide
  wfO := Catalog.published_wellFormed
  wf := Catalog.wellFormed
  inI := Translation.checkValid_sound (fun a _ _ h => pathEq_sound Catalog.wellFormed a h)
    (by decide)
  inO := Translation.checkValid_sound (fun a _ _ h => pathEq_sound Catalog.wellFormed a h)
    (by decide)
  rootsI := by decide
  rootsO := Catalog.published_rootsOnly

/-- The storefront, through its extension, with the published language of Catalog as
its input. -/
def storefrontOpen : OpenSchema Catalog.published emptySchema where
  S := storefront'
  wfI := Catalog.published_wellFormed
  wfO := by decide
  wf := storefrontNormalForm.wf
  inI := storefrontNormalForm.incl
  inO := Translation.checkValid_sound (fun a _ _ h => pathEq_sound storefrontNormalForm.wf a h)
    (by decide)
  rootsI := by decide
  rootsO := by decide

/-- Catalog and the storefront compose along the published language: they share its
names only, and the glued schema is well formed. -/
theorem catalog_storefront : catalogOpen.Composable storefrontOpen :=
  ⟨checkGluable_sound Catalog.wellFormed storefrontNormalForm.wf (by decide), by decide,
    by decide, by decide⟩

/-- The owner and the consumer as one schema: Catalog glued with the extension of
the storefront along the published language. A product has its Catalog fields and
the title of its listing, with `name = title`. -/
def catalogWithStorefront : OpenSchema emptySchema emptySchema :=
  catalogOpen.comp storefrontOpen catalog_storefront

theorem catalogWithStorefront_entities : catalogWithStorefront.S.entities =
    ["Category", "Product", "Variant", "Image"] := by
  decide

theorem name_title :
    (⟨"Product", ["name"], ["title"]⟩ : Equation) ∈ catalogWithStorefront.S.eqns := by
  decide

/-- The key of an offer by its code is a key of the variants in the composite. -/
theorem variant_code_key :
    (⟨"Variant", ["code"]⟩ : Key) ∈ catalogWithStorefront.S.keys := by
  decide

/-! ## Keys kept through renamed fields and through the empty path -/

/-- The published language of Catalog with the key of a variant by its SKU. -/
def keyedPublished : Schema := { Catalog.published with keys := [⟨"Variant", ["sku"]⟩] }

/-- CatalogPL → Storefront keeps the key: `sku` goes to `code`, the key of an
offer. -/
theorem storefront_keysKept : catalogStorefront.KeysKept keyedPublished storefront := by
  decide

/-- The published language with the key of a variant by its product and its SKU. -/
def keyedByProduct : Schema :=
  { Catalog.published with keys := [⟨"Variant", ["product", "sku"]⟩] }

/-- CatalogPL → Orders keeps this key although Orders declares no key with these
fields: `product` goes to the empty path, since a variant and its product are the
same product of Orders. -/
theorem catalogOrders_keysKept : catalogOrders.KeysKept keyedByProduct Orders.schema := by
  decide

/-- A storefront without the key of an offer does not keep the key of a variant. -/
theorem storefront_keysNotKept :
    catalogStorefront.keysNotKept keyedPublished { storefront with keys := [] } =
      [⟨"Variant", ["sku"]⟩] := by
  decide

end DDD.Examples.NormalForm
