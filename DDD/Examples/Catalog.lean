import DDD.PathEq

/-!
# Example: the Catalog context

Categories, products and their variants. A category may have a parent category,
so the references have a cycle; there are no equations, so the schema is free
and path equality is equality of names (`Schema.pathEqFree_iff`).

Aggregates: a category on its own; a product with its variants, each owning
reference `product` pointing to the root.

Checked with `decide`: well-formedness, the cycle (`not_acyclic`), and two paths
to a category name that differ. `withFeatured` adds a reference from a category
to a variant, which enters the product aggregate below its root and fails the
check.
-/

namespace DDD.Examples.Catalog

open Schema

/-- The Catalog schema. -/
def schema : Schema where
  entities := ["Category", "Product", "Variant"]
  refs := [⟨"parent", "Category", "Category"⟩, ⟨"category", "Product", "Category"⟩,
    ⟨"product", "Variant", "Product"⟩]
  attrs := [⟨"name", "Category", .string⟩, ⟨"name", "Product", .string⟩,
    ⟨"sku", "Variant", .string⟩, ⟨"price", "Variant", .decimal⟩]
  aggregates := [⟨"Category", []⟩, ⟨"Product", [⟨"Variant", "product"⟩]⟩]

theorem wellFormed : schema.WellFormed := by decide

theorem free : schema.eqns = [] := rfl

/-- `parent` gives paths of every length. -/
theorem not_acyclic : ¬ schema.Acyclic := by decide

/-- The name of a variant's category and the name of its parent category are
different paths, so different morphisms of `Schema.cat`. -/
theorem category_name_ne_parent_name :
    ¬ schema.PathEq ⟨.entity "Variant", by decide⟩ ["product", "category", "name"]
      ["product", "category", "parent", "name"] :=
  fun h => absurd ((pathEqFree_iff wellFormed free _ _ _).mpr h) (by decide)

/-- The same path, named twice, presents one morphism. -/
theorem category_name_eq :
    schema.PathEq ⟨.entity "Variant", by decide⟩ ["product", "category", "name"]
      ["product", "category", "name"] :=
  (pathEqFree_iff wellFormed free _ _ _).mp (by decide)

/-- A category featuring one variant: a reference from outside the product
aggregate to one of its members. -/
def withFeatured : Schema :=
  { schema with refs := ⟨"featured", "Category", "Variant"⟩ :: schema.refs }

theorem withFeatured_not_wellFormed : ¬ withFeatured.WellFormed := by decide

end DDD.Examples.Catalog
