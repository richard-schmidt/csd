import DDD.Merge
import DDD.Examples.Integration

/-!
# Example: merging Orders, Shipping and Payments along two kernels

The map of `Integration.lean` with a second kernel, `Addresses`: addresses with a
street and a city, the value object that Orders, Shipping and Payments all have.
It is included in the three by the empty translation. The kernels `Customers`
and `Addresses` and the three contexts form a component (`component`), with the
members in the order Orders, Shipping, Payments, Customers, Addresses:

- Shipping shares customers and addresses with Orders through `Customers`;
- Payments shares addresses with Orders through `Addresses`;
- the kernels include into Orders.

Checked with `decide`: the condition of the component, the arrows out of its
members, well-formedness and acyclicity of the glued schema. The glued schema
category is the colimit of `D` restricted to the component (`isColimit`).

The merged map (`merged`) has four contexts: the glued context, Catalog,
CatalogPL and OrdersPL. CatalogPL → Orders, OrdersPL → Orders and
OrdersPL → Payments become arrows into the glued context, each translation
composed with the inclusion of its target (`invoice_route`). The merged map has
no cycle, so each of its contexts embeds into its lax integration fully
faithfully (`merged_nonInterference`). Checked with `decide +kernel`: strict
non-interference for each member, every leg is fully faithful.
-/

namespace DDD.Examples.Merge

open CategoryTheory

/-! ## The map with a second kernel -/

/-- The contexts of `Integration.lean`, and the kernel `Addresses`. -/
inductive Context where
  | base (c : Integration.Context)
  | Addresses
deriving DecidableEq

/-- The arrows of `Integration.lean`, and the three inclusions of `Addresses`. -/
inductive Arrow : Context → Context → Type where
  | base {u d : Integration.Context} (f : Integration.Arrow u d) : Arrow (.base u) (.base d)
  | addresses_orders : Arrow .Addresses (.base .Orders)
  | addresses_shipping : Arrow .Addresses (.base .Shipping)
  | addresses_payments : Arrow .Addresses (.base .Payments)

instance : Quiver Context := ⟨Arrow⟩

/-- The kernel shared by Orders, Shipping and Payments: addresses with a street and
a city. -/
def addresses : Schema where
  entities := ["Address"]
  attrs := [⟨"street", "Address", .string⟩, ⟨"city", "Address", .string⟩]
  aggregates := [⟨"Address", []⟩]
  valueObjects := ["Address"]

/-- The schema of each context. -/
def schema : Context → Schema
  | .base c => Integration.schema c
  | .Addresses => addresses

theorem wellFormed : ∀ c, (schema c).WellFormed
  | .base c => Integration.wellFormed c
  | .Addresses => by decide

/-- The translation along each arrow; the inclusions of `Addresses` are the empty
translation. -/
def translation : {u d : Context} → Arrow u d → Translation
  | _, _, .base f => Integration.translation f
  | _, _, _ => {}

theorem valid : ∀ {u d : Context} (f : Arrow u d), (translation f).Valid (schema u) (schema d)
  | _, _, .base f => Integration.valid f
  | _, _, .addresses_orders =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Orders.wellFormed a h)
      (by decide)
  | _, _, .addresses_shipping =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Shipping.wellFormed a h)
      (by decide)
  | _, _, .addresses_payments =>
    Translation.checkValid_sound (fun a _ _ h => Schema.pathEq_sound Payments.wellFormed a h)
      (by decide)

/-- `Customers` and `Addresses` are the kernels. -/
def kernel : Context → Bool
  | .base c => Integration.kernel c
  | .Addresses => true

/-- The eight contexts, their schemas and translations, and the two kernels. -/
def contextMap : ContextMap Context where
  schema := schema
  translation := translation
  wellFormed := wellFormed
  valid := valid
  kernel := kernel
  inclusion f h := by
    cases f with
    | base f => exact Integration.contextMap.inclusion f h
    | _ => rfl

/-! ## The component -/

/-- The members of the component, in the order of the check. -/
def members : List Context :=
  [.base .Orders, .base .Shipping, .base .Payments, .base .Customers, .Addresses]

/-- The arrows out of the two kernels. -/
def links : List (Σ k d : Context, k ⟶ d) :=
  [⟨_, _, Arrow.base .customers_orders⟩, ⟨_, _, Arrow.base .customers_shipping⟩,
    ⟨_, _, Arrow.addresses_orders⟩, ⟨_, _, Arrow.addresses_shipping⟩,
    ⟨_, _, Arrow.addresses_payments⟩]

/-- Orders, Shipping and Payments with the two kernels. -/
def component : contextMap.Component where
  members := members
  links := links
  nonempty := by decide
  closed := by
    intro u d f
    cases f with
    | base f => cases f <;> decide
    | _ => decide
  kernels := by
    intro u d f
    cases f with
    | base f => cases f <;> decide
    | _ => decide
  check := by decide
  wf_glued := by decide

theorem glued_entities : component.glued.entities =
    ["Customer", "Address", "Order", "OrderLine", "Product", "Shipment", "Item", "Carrier",
      "Payer", "Invoice", "InvoiceLine", "Payment", "Refund"] := by
  decide

theorem glued_acyclic : component.glued.Acyclic := by decide

/-- The glued schema category is the colimit of `D` restricted to the component. -/
noncomputable example : Limits.IsColimit component.cocone := component.isColimit

/-! ## Strict non-interference -/

theorem orders_fullyFaithful :
    (component.leg ⟨.base .Orders, by decide⟩).Full ∧
      (component.leg ⟨.base .Orders, by decide⟩).Faithful :=
  component.leg_fullyFaithful _ Orders.acyclic glued_acyclic (by decide +kernel)

theorem shipping_fullyFaithful :
    (component.leg ⟨.base .Shipping, by decide⟩).Full ∧
      (component.leg ⟨.base .Shipping, by decide⟩).Faithful :=
  component.leg_fullyFaithful _ Shipping.acyclic glued_acyclic (by decide +kernel)

theorem payments_fullyFaithful :
    (component.leg ⟨.base .Payments, by decide⟩).Full ∧
      (component.leg ⟨.base .Payments, by decide⟩).Faithful :=
  component.leg_fullyFaithful _ Payments.acyclic glued_acyclic (by decide +kernel)

theorem customers_fullyFaithful :
    (component.leg ⟨.base .Customers, by decide⟩).Full ∧
      (component.leg ⟨.base .Customers, by decide⟩).Faithful :=
  component.leg_fullyFaithful _ (by decide) glued_acyclic (by decide +kernel)

theorem addresses_fullyFaithful :
    (component.leg ⟨.Addresses, by decide⟩).Full ∧
      (component.leg ⟨.Addresses, by decide⟩).Faithful :=
  component.leg_fullyFaithful _ (by decide) glued_acyclic (by decide +kernel)

/-! ## The merged map -/

/-- The map after the merge: the glued context, Catalog, CatalogPL and OrdersPL. -/
def merged : ContextMap (Merged members) := component.map

/-- OrdersPL → Payments becomes an arrow into the glued context: an order goes to
an invoice of the glued schema. -/
theorem invoice_route :
    merged.diagram.map (merged.arrow (u := .other (.base .OrdersPL) (by decide)) (d := .glued)
      ⟨⟨.base .Payments, by decide⟩, Arrow.base .ordersPL_payments⟩) =
      contextMap.diagram.map (contextMap.arrow (Arrow.base .ordersPL_payments)) ⋙
        component.leg ⟨.base .Payments, by decide⟩ :=
  component.diagram_into _ _ _

/-- Arrows go from a lower to a higher rank. -/
def rank : Context → Nat
  | .base c => Integration.rank c
  | .Addresses => 0

theorem rank_lt {u d : Context} (f : u ⟶ d) : rank u < rank d := by
  cases f with
  | base f => exact Integration.rank_lt f
  | _ => decide

/-- Lax non-interference for the merged map. -/
theorem merged_nonInterference (c : Merged members) :
    (merged.embed c).Full ∧ (merged.embed c).Faithful ∧ Function.Injective (merged.embed c).obj :=
  component.nonInterference rank rank_lt c

end DDD.Examples.Merge
