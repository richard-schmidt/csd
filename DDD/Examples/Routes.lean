import DDD.MapCheck

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
- `document`: the same map as a context map document, with the equation as two
  lists of arrow names. It passes `MapDoc.check` (`document_check`), so it is a
  context map with the diamond declared (`documentMap`); with Search reporting the
  SKU as the query, the check of the declared equation fails
  (`documentByQuery_check`).
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
    (translation f).VValid {} (schema u) (schema d)
  | _, _, f => (Translation.checkValid_sound
    (fun a _ _ h => Schema.pathEq_sound (wellFormed _) a h) (by cases f <;> decide)).vvalid

theorem validByQuery : ∀ {u d : Context} (f : Arrow u d),
    (translationByQuery f).VValid {} (schema u) (schema d)
  | _, _, f => (Translation.checkValid_sound
    (fun a _ _ h => Schema.pathEq_sound (wellFormed _) a h) (by cases f <;> decide)).vvalid

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
    routeTranslation {} schema translation viaSales =
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
theorem check_byQuery : checkRouteEqn {} schema translationByQuery diamond = false := by
  decide

/-- With Search reporting the SKU as the query, the two routes have different
functors, so the diamond cannot be declared. -/
theorem routes_ne :
    (routeDiagram {} schema translationByQuery wellFormed validByQuery).map viaSales ≠
      (routeDiagram {} schema translationByQuery wellFormed validByQuery).map viaSearch :=
  routeDiagram_map_ne wellFormed validByQuery diamond
    (Schema.pathEqV_iff_of_free (wellFormed _) ((TypeList.checkSound_iff _).mp (by decide))
      reporting_free) check_byQuery

/-- `searchByQuery`, without the declaration. -/
def searchByQuery : ContextMap Context where
  schema := schema
  translation := translationByQuery
  wellFormed := wellFormed
  valid := validByQuery

/-! ## The diamond as a document -/

/-- The four contexts as a context map document that declares the diamond: the
equation is two lists of arrow names. -/
def document : MapDoc where
  contexts := [("Catalog", schema .Catalog, false), ("Sales", schema .Sales, false),
    ("Search", schema .Search, false), ("Reporting", schema .Reporting, false)]
  arrows := [("catalog_sales", "Catalog", "Sales", translation Arrow.catalog_sales),
    ("catalog_search", "Catalog", "Search", translation Arrow.catalog_search),
    ("sales_reporting", "Sales", "Reporting", translation Arrow.sales_reporting),
    ("search_reporting", "Search", "Reporting", translation Arrow.search_reporting)]
  routeEqns := [(["catalog_sales", "sales_reporting"], ["catalog_search", "search_reporting"])]

/-- The document passes its check, the declared equation included. -/
theorem document_check : document.check = true := by decide +kernel

/-- The document as a context map, with the diamond declared. -/
def documentMap : ContextMap document.Ctx := MapDoc.contextMap document_check

/-- The document with Search reporting the SKU as the query: the declared equation
fails, and the report names it. -/
def documentByQuery : MapDoc :=
  { document with
    arrows := document.arrows.map fun a =>
      if a.1 = "search_reporting" then
        (a.1, a.2.1, a.2.2.1, translationByQuery Arrow.search_reporting) else a }

theorem documentByQuery_check : documentByQuery.check = false := by decide +kernel

example : documentByQuery.checkRoutes = false ∧ documentByQuery.certificate.check = true := by
  decide +kernel

/-- An equation whose sides are not routes between the same contexts fails. -/
example : ({ document with routeEqns := [(["catalog_sales"], ["catalog_search"])] } :
    MapDoc).checkRoutes = false := by
  decide +kernel

end DDD.Examples.Routes
