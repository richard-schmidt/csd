import DDD.ClosureData
import DDD.Json

/-!
# Example: merging two states by their keys

A shop lists products, identified by their SKU, and variants of a product,
identified by their product and their size (`shop`).

- `first` and `second` are the lists of two sources. Both have the product `A`,
  and both have its variant of size `S`.
- Their merge is the closure of their sum (`merged`): the two entries of the
  product `A` are one product, and then the two variants of size `S` of that
  product are one variant. Three products and four variants remain.
- The merged list satisfies the keys, receives both lists, and is their coproduct
  among the states that satisfy the keys: two morphisms from the lists into such a
  state factor through it in one way (`merge`).
- `third` names the product `A` differently. The closure of its sum with `first`
  fails on the two names (`conflicting`), and no state that satisfies the keys
  receives both lists (`no_merge`).
- A list with the product `A` twice has a closure with it once (`deduplicated`),
  which is the closure of its state (`deduplicated_closure`).
- The terminal state of the shop does not satisfy the keys (`terminal_not_keys`).
-/

namespace DDD.Examples.Closure

open CategoryTheory

/-- Products with a SKU and a name, and variants of a product with a size. A
product is identified by its SKU, a variant by its product and its size. -/
def shop : Schema where
  entities := ["Product", "Variant"]
  refs := [⟨"product", "Variant", "Product"⟩]
  attrs := [⟨"sku", "Product", .string⟩, ⟨"name", "Product", .string⟩,
    ⟨"size", "Variant", .string⟩]
  keys := [⟨"Product", ["sku"]⟩, ⟨"Variant", ["product", "size"]⟩]

theorem shop_wellFormed : shop.WellFormed := by decide

/-- A column of texts. -/
def texts (ls : List String) : List (Σ _ : ValueType, Lit) := ls.map fun l => ⟨.string, .text l⟩

/-- A list of products and of variants, each variant with the number of its
product. -/
def list (products : List (String × String)) (variants : List (Nat × String)) : FinState LitK where
  sizes := [("Product", products.length), ("Variant", variants.length)]
  refs := [(("Variant", "product"), variants.map (·.1))]
  attrs := [(("Product", "sku"), texts (products.map (·.1))),
    (("Product", "name"), texts (products.map (·.2))),
    (("Variant", "size"), texts (variants.map (·.2)))]

/-- The list of the first source. -/
def first : FinState LitK := list [("A", "Mug"), ("B", "Plate")] [(0, "S"), (1, "M")]

/-- The list of the second source: the product `A` again, with two sizes. -/
def second : FinState LitK :=
  list [("A", "Mug"), ("C", "Bowl")] [(0, "S"), (0, "L"), (1, "S")]

/-- The product `A` under another name. -/
def third : FinState LitK := list [("A", "Cup")] []

theorem first_check : first.check shop = true := by decide

theorem second_check : second.check shop = true := by decide

theorem third_check : third.check shop = true := by decide

/-- The merged list: the products `A`, `B` and `C`, and four variants. -/
def mergedList : FinState LitK :=
  list [("A", "Mug"), ("B", "Plate"), ("C", "Bowl")] [(0, "S"), (1, "M"), (0, "L"), (2, "S")]

/-- The closure of the sum of the two lists: the two entries of `A` are one
product, and the two variants of size `S` of `A` are one variant. -/
theorem merged : (first.sum shop second).closure shop =
    .closed mergedList ⟨[("Product", [0, 1, 0, 2]), ("Variant", [0, 1, 0, 2, 3])]⟩ := by
  decide +kernel

theorem checkSum_first_second : FinState.checkSum shop first second = true := by decide +kernel

/-- The merged list satisfies the keys, receives the two lists, and is their
coproduct among the states that satisfy the keys. -/
theorem merge : ∃ (hM : mergedList.check shop = true)
    (i₁ : first.toState first_check ⟶ mergedList.toState hM)
    (i₂ : second.toState second_check ⟶ mergedList.toState hM),
    (mergedList.toState hM).Keys ∧
    ∀ {W : shop.State LitK}, W.Keys →
      ∀ (a : first.toState first_check ⟶ W) (b : second.toState second_check ⟶ W),
        ∃! m : mergedList.toState hM ⟶ W, i₁ ≫ m = a ∧ i₂ ≫ m = b :=
  FinState.merge_closed shop_wellFormed first_check second_check checkSum_first_second merged

/-- The sum of the first and the third list has the product `A` with two names. -/
theorem conflicting : (first.sum shop third).closure shop = .inconsistent "Product" "name" 0 2 := by
  decide +kernel

theorem checkSum_first_third : FinState.checkSum shop first third = true := by decide +kernel

/-- No state that satisfies the keys receives the first and the third list. -/
theorem no_merge {W : shop.State LitK} (hW : W.Keys) (a : first.toState first_check ⟶ W)
    (b : third.toState third_check ⟶ W) : False :=
  FinState.merge_inconsistent shop_wellFormed first_check third_check checkSum_first_third
    conflicting hW a b

/-- A list with the product `A` twice, and a variant of each entry. -/
def twice : FinState LitK := list [("A", "Mug"), ("A", "Mug")] [(0, "S"), (1, "S"), (1, "L")]

theorem twice_check : twice.check shop = true := by decide

theorem twice_not_keys : twice.checkKeys shop = false := by decide

/-- Its closure has the product once and two variants. -/
theorem deduplicated : twice.closure shop =
    .closed (list [("A", "Mug")] [(0, "S"), (0, "L")])
      ⟨[("Product", [0, 0]), ("Variant", [0, 0, 1])]⟩ := by
  decide +kernel

/-- The state of the result is the closure of the state of the list. -/
theorem deduplicated_closure :
    ∃ (hY : (list [("A", "Mug")] [(0, "S"), (0, "L")]).check shop = true)
      (hc : (twice.toState twice_check).Consistent),
      Nonempty ((twice.toState twice_check).closure hc ≅
        (list [("A", "Mug")] [(0, "S"), (0, "L")]).toState hY) := by
  obtain ⟨hY, hc, -, h⟩ := FinState.closure_closed shop_wellFormed twice_check deduplicated
  exact ⟨hY, hc, h⟩

/-! ## The terminal state -/

open Schema in
/-- The terminal state of the shop does not satisfy the keys: it has every profile
of a product, and two profiles with one SKU and two names are two products. So the
states that satisfy the keys have no terminal object here, and limits of empty
diagrams do not keep keys. -/
theorem terminal_not_keys : ¬ (State.terminal shop LitK).Keys := by
  classical
  intro h
  have he : "Product" ∈ shop.entities := by decide
  have hname : shop.step? (.entity "Product") "name" = some (.value .string) := by decide
  have hsku : shop.step? (.entity "Product") "sku" = some (.value .string) := by decide
  let nameMor : shop.obj ⟨.entity "Product", he⟩ ⟶ shop.valueObj .string :=
    shop.genMor (a := ⟨.entity "Product", he⟩) (b := ⟨.value .string, trivial⟩) "name" hname
  let φ : shop.Profile LitK (shop.obj ⟨.entity "Product", he⟩) := fun _ _ => .text "x"
  let ψ : shop.Profile LitK (shop.obj ⟨.entity "Product", he⟩) := fun v g =>
    if ∃ hv : v = .string, hv ▸ g = nameMor then .text "y" else .text "x"
  have key : φ = ψ := h ⟨"Product", ["sku"]⟩ (by decide) he φ ψ fun n hn b hb => by
    obtain rfl : n = "sku" := by simpa using hn
    obtain ⟨o, ho⟩ := b
    obtain rfl : o = .value .string := Option.some.inj (hb.symm.trans hsku)
    refine Profile.ext_value ?_
    change Lit.text "x" = if ∃ hv : ValueType.string = .string,
      hv ▸ (shop.genMor (a := ⟨.entity "Product", he⟩) (b := ⟨.value .string, ho⟩) "sku" hb ≫
        𝟙 _) = nameMor then Lit.text "y" else Lit.text "x"
    rw [Category.comp_id, if_neg]
    rintro ⟨_, heq⟩
    have hp : shop.PathEq ⟨.entity "Product", he⟩ ["sku"] ["name"] :=
      ⟨⟨.value .string, trivial⟩, shop.genPath _ _ "sku" hb, shop.genPath _ _ "name" hname,
        rfl, rfl, heq⟩
    have hd : shop.pathEqFree (.entity "Product") ["sku"] ["name"] = false := by decide
    exact absurd ((pathEqFree_iff shop_wellFormed rfl _ _ _).mpr hp) (by rw [hd]; simp)
  have hv := congrFun (congrFun key .string) nameMor
  change Lit.text "x" = if _ then _ else _ at hv
  rw [if_pos ⟨rfl, rfl⟩] at hv
  exact absurd hv (by decide)

end DDD.Examples.Closure
