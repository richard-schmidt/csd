import DDD.ContextMap

/-!
# Example: a declared diamond

Four contexts. Catalog publishes variants with a SKU and a price; Sales and Search
both read them, and Reporting reads Sales and Search. The two routes from Catalog
to Reporting form a diamond.

- `declared`: Sales reports an item's SKU and unit price, Search reports a hit's
  SKU and price. Along both routes a variant goes to a row with its SKU and its
  price as amount, so the map declares the two routes equal, and the check
  accepts the declaration (`coherent_of_check`, by `decide`). In its category of
  contexts the two routes are one morphism (`routes_eq`).
- `searchByQuery`: Search reports a hit's SKU as the query that found it. The
  composites differ, since the SKU of a variant goes to `sku` along one route and
  to `query` along the other; the check fails, and since Reporting is free, the
  two routes have different functors (`routes_ne`). Such a diamond stays free: a
  row refers to a variant through each route separately.
-/

namespace DDD.Examples.Routes

open CategoryTheory

/-- The contexts. -/
inductive Context where
  | Catalog | Sales | Search | Reporting
deriving DecidableEq, Repr

/-- The arrows, from upstream to downstream. -/
inductive Arrow : Context → Context → Type where
  | catalog_sales : Arrow .Catalog .Sales
  | catalog_search : Arrow .Catalog .Search
  | sales_reporting : Arrow .Sales .Reporting
  | search_reporting : Arrow .Search .Reporting

instance : Quiver Context := ⟨Arrow⟩

/-- The schema of each context. -/
def schema : Context → Schema
  | .Catalog => { entities := ["Variant"]
                  attrs := [⟨"sku", "Variant", .string⟩, ⟨"price", "Variant", .decimal⟩]
                  aggregates := [⟨"Variant", []⟩] }
  | .Sales => { entities := ["Item"]
                attrs := [⟨"sku", "Item", .string⟩, ⟨"unitPrice", "Item", .decimal⟩,
                  ⟨"quantity", "Item", .int⟩]
                aggregates := [⟨"Item", []⟩] }
  | .Search => { entities := ["Hit"]
                 attrs := [⟨"sku", "Hit", .string⟩, ⟨"price", "Hit", .decimal⟩]
                 aggregates := [⟨"Hit", []⟩] }
  | .Reporting => { entities := ["Row"]
                    attrs := [⟨"sku", "Row", .string⟩, ⟨"query", "Row", .string⟩,
                      ⟨"amount", "Row", .decimal⟩, ⟨"count", "Row", .int⟩]
                    aggregates := [⟨"Row", []⟩] }

theorem wellFormed : ∀ c, (schema c).WellFormed
  | .Catalog => by decide
  | .Sales => by decide
  | .Search => by decide
  | .Reporting => by decide

theorem reporting_free : (schema .Reporting).eqns = [] := rfl

/-- The translations of `declared`. -/
def translation : {u d : Context} → Arrow u d → Translation
  | _, _, .catalog_sales => { entities := [("Variant", "Item")]
                              gens := [⟨"Variant", "price", ["unitPrice"]⟩] }
  | _, _, .catalog_search => { entities := [("Variant", "Hit")] }
  | _, _, .sales_reporting => { entities := [("Item", "Row")]
                                gens := [⟨"Item", "unitPrice", ["amount"]⟩,
                                  ⟨"Item", "quantity", ["count"]⟩] }
  | _, _, .search_reporting => { entities := [("Hit", "Row")]
                                 gens := [⟨"Hit", "price", ["amount"]⟩] }

/-- The translations of `searchByQuery`: Search reports the SKU of a hit as its
query. -/
def translationByQuery : {u d : Context} → Arrow u d → Translation
  | _, _, .search_reporting => { entities := [("Hit", "Row")]
                                 gens := [⟨"Hit", "price", ["amount"]⟩,
                                   ⟨"Hit", "sku", ["query"]⟩] }
  | _, _, f => translation f

theorem valid : ∀ {u d : Context} (f : Arrow u d),
    (translation f).Valid (schema u) (schema d)
  | _, _, f => Translation.checkValid_sound
    (fun a _ _ h => Schema.pathEq_sound (wellFormed _) a h) (by cases f <;> decide)

theorem validByQuery : ∀ {u d : Context} (f : Arrow u d),
    (translationByQuery f).Valid (schema u) (schema d)
  | _, _, f => Translation.checkValid_sound
    (fun a _ _ h => Schema.pathEq_sound (wellFormed _) a h) (by cases f <;> decide)

/-- The route through Sales. -/
def viaSales : Quiver.Path Context.Catalog Context.Reporting :=
  (Quiver.Hom.toPath (V := Context) Arrow.catalog_sales).cons Arrow.sales_reporting

/-- The route through Search. -/
def viaSearch : Quiver.Path Context.Catalog Context.Reporting :=
  (Quiver.Hom.toPath (V := Context) Arrow.catalog_search).cons Arrow.search_reporting

/-- The diamond, as an equation between routes. -/
def diamond : RouteEqn Context := ⟨.Catalog, .Reporting, viaSales, viaSearch⟩

/-- The composite along each route sends a variant to a row, its SKU to `sku` and
its price to `amount`. -/
theorem viaSales_translation :
    routeTranslation schema translation viaSales =
      { entities := [("Variant", "Row")]
        gens := [⟨"Variant", "sku", ["sku"]⟩, ⟨"Variant", "price", ["amount"]⟩] } := by
  decide

/-- The four contexts with the diamond declared. -/
def declared : ContextMap Context where
  schema := schema
  translation := translation
  wellFormed := wellFormed
  valid := valid
  routeEqns := RouteEqn.rel [diamond]
  coherent := coherent_of_check wellFormed valid [diamond] (by decide)

/-- In the category of contexts of `declared`, the two routes are one morphism. -/
theorem routes_eq : declared.route viaSales = declared.route viaSearch :=
  declared.route_eq (List.mem_singleton.mpr rfl)

/-- Arrows go from a lower to a higher rank. -/
def rank : Context → Nat
  | .Catalog => 0
  | .Sales | .Search => 1
  | .Reporting => 2

theorem rank_lt {u d : Context} (f : u ⟶ d) : rank u < rank d := by
  cases f <;> decide

/-- Lax non-interference for `declared`. -/
theorem nonInterference (c : Context) :
    (declared.embed c).Full ∧ (declared.embed c).Faithful ∧
      Function.Injective (declared.embed c).obj :=
  declared.nonInterference (declared.endo_eq_id (endo_eq_id_of_rank rank rank_lt)) c

/-- With Search reporting the SKU as the query, the check fails. -/
theorem check_byQuery : checkRouteEqn schema translationByQuery diamond = false := by
  decide

/-- With Search reporting the SKU as the query, the two routes have different
functors, so the diamond cannot be declared. -/
theorem routes_ne :
    (routeDiagram schema translationByQuery wellFormed validByQuery).map viaSales ≠
      (routeDiagram schema translationByQuery wellFormed validByQuery).map viaSearch :=
  routeDiagram_map_ne wellFormed validByQuery diamond
    (Schema.pathEq_iff_of_free (wellFormed _) reporting_free) check_byQuery

/-- `searchByQuery`, without the declaration. -/
def searchByQuery : ContextMap Context where
  schema := schema
  translation := translationByQuery
  wellFormed := wellFormed
  valid := validByQuery

end DDD.Examples.Routes
