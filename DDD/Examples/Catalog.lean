import DDD.PathEq

/-!
# Example: the Catalog context

Categories, products, their variants and their images. A category may have a
parent category, so the references have a cycle; there are no equations, so the
schema is free and path equality is equality of names
(`Schema.pathEqFree_iff`).

Aggregates: a category on its own; a product with its images, each owning
reference `product` pointing to the root; a variant on its own, with a
reference `product` to its product. Whether an image is the primary one is a
`bool`.

The published language of Catalog (`published`) is what other contexts see:
products with their names, and variants with their SKU, price and product. It
contains roots only (`published_rootsOnly`).

Checked with `decide`: well-formedness, the cycle (`not_acyclic`), and two paths
to a category name that differ. `withFeatured` adds a reference from a category
to an image, which enters the product aggregate below its root and fails the
check.
-/

namespace DDD.Examples.Catalog

open Schema

/-- The Catalog schema. -/
def schema : Schema where
  entities := ["Category", "Product", "Variant", "Image"]
  refs := [⟨"parent", "Category", "Category"⟩, ⟨"category", "Product", "Category"⟩,
    ⟨"product", "Variant", "Product"⟩, ⟨"product", "Image", "Product"⟩]
  attrs := [⟨"name", "Category", .string⟩, ⟨"name", "Product", .string⟩,
    ⟨"sku", "Variant", .string⟩, ⟨"price", "Variant", .decimal⟩,
    ⟨"url", "Image", .string⟩, ⟨"primary", "Image", .bool⟩]
  aggregates := [⟨"Category", []⟩, ⟨"Product", [⟨"Image", "product"⟩]⟩, ⟨"Variant", []⟩]

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

/-- A category featuring one image: a reference from outside the product
aggregate to one of its members. -/
def withFeatured : Schema :=
  { schema with refs := ⟨"featured", "Category", "Image"⟩ :: schema.refs }

theorem withFeatured_not_wellFormed : ¬ withFeatured.WellFormed := by decide

/-! ## The published language -/

/-- The published language of Catalog: products and variants. -/
def published : Schema where
  entities := ["Product", "Variant"]
  refs := [⟨"product", "Variant", "Product"⟩]
  attrs := [⟨"name", "Product", .string⟩, ⟨"sku", "Variant", .string⟩,
    ⟨"price", "Variant", .decimal⟩]
  aggregates := [⟨"Product", []⟩, ⟨"Variant", []⟩]

theorem published_wellFormed : published.WellFormed := by decide

theorem published_free : published.eqns = [] := rfl

/-- Products and variants are roots of Catalog. -/
theorem published_rootsOnly : published.RootsOnly schema := by decide

end DDD.Examples.Catalog
