import Showcase.SystemModel
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Union

namespace SystemExample

-- Power grid example

structure Plant where
  id : Nat
deriving DecidableEq, Repr

structure Transformer where
  id : Nat
  plantId : Nat
deriving DecidableEq, Repr

structure House where
  id : Nat
  transformerId : Nat
deriving DecidableEq, Repr

inductive GridAtom
  | plant : Plant -> GridAtom
  | trans : Transformer -> GridAtom
  | house : House -> GridAtom
deriving DecidableEq, Repr

inductive GridElement
  | collection : Finset GridAtom -> GridElement
  | everything
deriving DecidableEq

instance : Coe GridAtom GridElement where coe := fun a => GridElement.collection {a}

@[ext]
structure SubGrid where
  plants : Finset Plant
  transformers : Finset Transformer
  houses : Finset House
deriving DecidableEq

namespace SubGrid

def empty_grid : SubGrid := ⟨ {}, {}, {} ⟩

@[reducible]
def is_coherent (sg : SubGrid) : Prop :=
  (∀ t: Transformer, t ∈ sg.transformers →  ∃ p ∈ sg.plants, p.id = t.plantId)
   ∧ (∀ h : House, h ∈ sg.houses → ∃ t ∈ sg.transformers, t.id = h.transformerId)

postfix:80 "✓" => is_coherent

theorem empty_grid_is_coherent : empty_grid✓ := by
  simp [SubGrid.is_coherent, empty_grid]

@[reducible]
def add (sg sh : SubGrid) : SubGrid :=
  {
    plants := sg.plants ∪ sh.plants
    transformers := sg.transformers ∪ sh.transformers
    houses := sg.houses ∪ sh.houses
  }

infix:80 "⊕" => add

theorem add_comm : ∀ sg sh : SubGrid, (sg ⊕ sh) = (sh ⊕ sg) := by
  simp [add, Finset.union_comm]

theorem add_assoc : ∀ sg sh si : SubGrid, add (add sg sh) si = add sg (add sh si) := by
  simp [add, Finset.union_assoc]

instance : Std.Commutative add where comm := by exact add_comm

instance : Std.Associative add where assoc := by exact add_assoc

theorem add_empty_idemp : ∀ sg, (sg ⊕ empty_grid) = sg := by
  simp [empty_grid, add]

@[reducible]
def diff (sg sh : SubGrid) : SubGrid :=
  {
    plants := sg.plants ∩ sh.plants
    transformers := sg.transformers ∩ sh.transformers
    houses := sg.houses ∩ sh.houses
  }

infix:79 "⊝" => diff

theorem diff_comm : ∀ sg sh : SubGrid, (sg ⊝ sh) = (sh ⊝ sg) := by
  simp [diff, Finset.inter_comm]

theorem diff_assoc : ∀ sg sh si : SubGrid, diff (diff sg sh) si = diff sg (diff sh si) := by
  simp [diff, Finset.inter_assoc]

instance : Std.Commutative diff where comm := by exact diff_comm

instance : Std.Associative diff where assoc := by exact diff_assoc

theorem coherent_inter {sg sh : SubGrid} : sg✓ ∧ sh ✓ -> (sg ⊕ sh)✓ := by
  intro ⟨ h1, h2 ⟩
  simp only [is_coherent, Finset.mem_union] at *
  grind

@[simp]
def flatten (sg : SubGrid) : Finset GridAtom :=
  (sg.plants.image GridAtom.plant) ∪
  (sg.transformers.image GridAtom.trans) ∪
  (sg.houses.image GridAtom.house)

prefix:74 "♭" => flatten

@[simp]
def extract_elements (sg : SubGrid) : Finset GridElement :=
  (Finset.image (fun p => GridElement.collection {GridAtom.plant p}) sg.plants)
  ∪ (Finset.image (fun t => GridElement.collection {GridAtom.trans t}) sg.transformers)
  ∪ (Finset.image (fun h => GridElement.collection {GridAtom.house h}) sg.houses)

postfix:75 "↓" => extract_elements

@[simp]
def sub (g g' : SubGrid) : Prop :=
  g.plants ⊆ g'.plants ∧ g.transformers ⊆ g'.transformers ∧ g.houses ⊆ g'.houses

infix:72 " ⋖ " => sub

instance (sg sh : SubGrid) : Decidable (sg ⋖ sh) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma add_sub_add {sg sh tg th : SubGrid} (h1 : sg ⋖ sh) (h2 : tg ⋖ th) :
  (sg ⊕ tg) ⋖ (sh ⊕ th) := by
  simp only [sub] at *
  obtain ⟨ h1p, h1t, h1h ⟩ := h1
  obtain ⟨ h2p, h2t, h2h ⟩ := h2
  exact ⟨  Finset.union_subset_union h1p h2p,
   Finset.union_subset_union h1t h2t,
    Finset.union_subset_union h1h h2h ⟩

theorem sub_flat_sub {sg sh : SubGrid} : sg ⋖ sh → ♭sg ⊆ ♭sh:= by
  simp only [sub, flatten]
  intro h
  obtain ⟨ hp, ht, hh ⟩ := h
  gcongr
  · exact Finset.image_subset_image hp
  · exact Finset.image_subset_image ht
  · exact Finset.image_subset_image hh

def to_subgrid (a : GridAtom) : SubGrid := match a with
| .plant p => ⟨ {p}, {}, {} ⟩
| .trans t => ⟨ {}, {t}, {} ⟩
| .house h => ⟨ {}, {} ,{h} ⟩

def sharpen (a : Finset GridAtom) : SubGrid := a.fold (add) empty_grid to_subgrid

prefix:75 "♯" => sharpen

theorem empty_set_to_empty_grid : ♯∅ = empty_grid := by constructor

theorem emptygrid_sub (sg : SubGrid) : empty_grid ⋖ sg := by
  simp [sub, empty_grid, Finset.empty_subset]

@[simp]
lemma sharpen_insert {a : GridAtom} {sa : Finset GridAtom} (h : a ∉ sa) :
 ♯(insert a sa) = (to_subgrid a) ⊕ (♯sa) := Finset.fold_insert h

lemma sharpen_decompose {x : GridAtom} {b : Finset GridAtom} :
 x ∈ b -> ♯b = (to_subgrid x) ⊕ (♯(b.erase x)) := by
  intro h
  nth_rw 1 [← Finset.insert_erase h]
  rw [sharpen_insert (Finset.notMem_erase x b)]

theorem sub_refl (sg : SubGrid) : sg ⋖ sg := by
  simp [sub]

lemma sharpen_field_distrib {T : Type*} [DecidableEq T]
(a : Finset GridAtom) (f : SubGrid → Finset T)
  (h_empty : f empty_grid = ∅)
  (h_add : ∀ s1 s2, f (s1 ⊕ s2) = f s1 ∪ f s2) :
  f (♯ a) = a.biUnion (fun x => f (to_subgrid x)) := by
  induction a using Finset.induction_on with
  | empty => simp [sharpen, h_empty]
  | insert a sa ha h_ind =>
      simp [sharpen_insert ha, h_add, h_ind]

lemma sharpen_plants (a : Finset GridAtom) :
  (♯a).plants = a.biUnion (fun x => (to_subgrid x).plants) :=
  sharpen_field_distrib a (·.plants) rfl (fun _ _ => rfl)

lemma sharpen_transformers (a : Finset GridAtom) :
  (♯a).transformers = a.biUnion (fun x => (to_subgrid x).transformers) :=
  sharpen_field_distrib a (·.transformers) rfl (fun _ _ => rfl)

lemma sharpen_houses (a : Finset GridAtom) :
  (♯a).houses = a.biUnion (fun x => (to_subgrid x).houses) :=
  sharpen_field_distrib a (·.houses) rfl (fun _ _ => rfl)

theorem sub_trans (sg sh si : SubGrid) : sg ⋖ sh ∧ sh ⋖ si → sg ⋖ si := by
  intro ⟨ hgh, hhi ⟩
  simp only [sub] at *
  obtain ⟨ hp1, ht1, hh1 ⟩ := hgh
  obtain ⟨ hp2, ht2, hh2 ⟩ := hhi
  exact ⟨ Finset.Subset.trans hp1 hp2, Finset.Subset.trans ht1 ht2, Finset.Subset.trans hh1 hh2 ⟩

theorem sub_symm {sg sh : SubGrid} : (sg ⋖ sh ∧ sh ⋖ sg) ↔ (sg = sh) := by
  constructor
  · intro h
    obtain ⟨ h1, h2 ⟩ := h
    simp only [sub] at *
    let ⟨ h1p, h1t, h1h ⟩ := h1
    let ⟨ h2p, h2t, h2h ⟩ := h2
    have hp := Finset.Subset.antisymm h1p h2p
    have ht := Finset.Subset.antisymm h1t h2t
    have hh := Finset.Subset.antisymm h1h h2h
    (cases sg ; cases sh ; simp only [mk.injEq] at * ; exact ⟨ hp, ht, hh ⟩)
  · intro h
    rw [h]
    simp

end SubGrid

namespace Grid

open SubGrid

lemma flatten_subgrid_atom {a : GridAtom} : ♭(to_subgrid a) = {a} := by
  cases a <;> simp [to_subgrid, flatten]

lemma flatten_distrib {sg sh : SubGrid} : ♭(sg ⊕ sh) = ♭sg ∪ ♭sh := by
  simp only [flatten, Finset.image_union, Finset.union_assoc]
  grind

theorem flatten_sharpen_idemp (a : Finset GridAtom) : ♭♯a = a := by
  induction a using Finset.induction_on with
  | empty => simp [sharpen, empty_grid, flatten]
  | insert a sa ha h_ind =>
    rw [sharpen_insert ha, flatten_distrib, flatten_subgrid_atom, h_ind]
    rw [Finset.union_comm]
    simp

lemma flat_sub_plants {sg sh : SubGrid} (h : ♭sg ⊆ ♭sh) :
 sg.plants ⊆ sh.plants := by
  intro p hp
  have h_in : GridAtom.plant p ∈ ♭sg := by
    simp only [flatten, Finset.mem_union, Finset.mem_image]
    left; left
    exact ⟨p, hp, rfl⟩
  have hsh := h h_in
  simp only [flatten, Finset.mem_union, Finset.mem_image] at hsh
  rcases hsh with (⟨ p', hp', heq ⟩ | ⟨ t', ht', heq ⟩) | ⟨ h', hh', heq ⟩
  · cases heq
    exact hp'
  · contradiction
  · contradiction

lemma flat_sub_transformers {sg sh : SubGrid} (h : ♭sg ⊆ ♭sh) :
 sg.transformers ⊆ sh.transformers := by
  intro t hp
  have h_in : GridAtom.trans t ∈ ♭sg := by
    simp only [flatten, Finset.mem_union, Finset.mem_image]
    left; right
    exact ⟨t, hp, rfl⟩
  have hsh := h h_in
  simp only [flatten, Finset.mem_union, Finset.mem_image] at hsh
  rcases hsh with (⟨ p', hp', heq ⟩ | ⟨ t', ht', heq ⟩) | ⟨ h', hh', heq ⟩
  · contradiction
  · cases heq
    exact ht'
  · contradiction

lemma flat_sub_houses {sg sh : SubGrid} (h : ♭sg ⊆ ♭sh) :
 sg.houses ⊆ sh.houses := by
  intro hx hp
  have h_in : GridAtom.house hx ∈ ♭sg := by
    simp only [flatten, Finset.mem_union, Finset.mem_image]
    right
    exact ⟨hx, hp, rfl⟩
  have hsh := h h_in
  simp only [flatten, Finset.mem_union, Finset.mem_image] at hsh
  rcases hsh with (⟨ p', hp', heq ⟩ | ⟨ t', ht', heq ⟩) | ⟨ h', hh', heq ⟩
  · contradiction
  · contradiction
  · cases heq
    exact hh'

@[reducible]
def CoherentSubGrid := {sg : SubGrid // sg✓}

instance : Coe CoherentSubGrid SubGrid where
coe := fun g => g.val

@[reducible]
def minimal_covering_coherent_subgrid
(cg : CoherentSubGrid) (sg : SubGrid) (h : sg ⋖ cg := by assumption): CoherentSubGrid :=
  let m_trans := sg.transformers
  ∪ cg.val.transformers.filter (fun t => t.id ∈ sg.houses.image (fun h => h.transformerId))
  let m_plants := sg.plants
  ∪ cg.val.plants.filter (fun p => p.id ∈ ((m_trans.image (fun t => t.plantId))
  ∪ m_trans.image (fun t => t.id)))
  let m_houses := cg.val.houses ∩ sg.houses
  let m_sg : SubGrid := {
    plants := m_plants
    transformers := m_trans
    houses := m_houses
  };
  have h : m_sg✓ := by
    simp only [is_coherent, m_sg]
    constructor
    · intro t ht
      have t_in_cg : t ∈ cg.val.transformers := by
        simp only [m_trans, Finset.mem_union] at ht
        cases ht with
        | inl h_in_sg => exact h.2.1 h_in_sg
        | inr h_in_filter => simp only [Finset.mem_filter] at h_in_filter; exact h_in_filter.1
      obtain ⟨ p, p_in_cg, p_id ⟩ := cg.prop.1 t t_in_cg
      simp only [m_plants, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
      use p
      constructor
      · right ; refine ⟨p_in_cg, ?_⟩
        left; exact ⟨t, ht, p_id.symm ⟩
      · exact p_id
    · intro h_house hh
      simp only [Finset.mem_inter, m_houses] at hh
      have h_in_cg : h_house ∈ cg.val.houses := by exact hh.1
      have h_in_sg : h_house ∈ sg.houses := by exact hh.2
      obtain ⟨t, t_in_cg, t_id ⟩ := cg.prop.2 h_house h_in_cg
      use t
      constructor
      · simp only [Finset.mem_image, Finset.mem_union, Finset.mem_filter, m_trans]
        right; refine ⟨ t_in_cg, ?_⟩
        use h_house; exact ⟨ h_in_sg, t_id.symm ⟩
      · exact t_id
  ⟨m_sg, h⟩

infix:79 " ↘ "  => minimal_covering_coherent_subgrid

theorem subgrid_monotone {a b : Finset GridAtom} (h : a ⊆ b) : ♯a ⋖ ♯b := by
  simp only [sub, sharpen_plants, sharpen_transformers, sharpen_houses]
  exact ⟨ Finset.biUnion_subset_biUnion_of_subset_left _ h,
        Finset.biUnion_subset_biUnion_of_subset_left _ h,
        Finset.biUnion_subset_biUnion_of_subset_left _ h ⟩

structure PowerGrid where
  grid : CoherentSubGrid

instance {g : PowerGrid} : SystemModel.System SubGrid GridElement where
  top := .everything
  bot := GridElement.collection {}
  top_component := g.grid
  bot_component := empty_grid

  component c := c ⋖ g.grid
  entity e := e ∈ g.grid↓

  sub e f:= match e,f with
  | _, .everything => True
  | .everything, _ => False
  | .collection a, .collection b => a ⊆ b

  sub_component := sub

  part_of e c := match e with
  | .everything => False
  | .collection a => a ⊆ ♭c

  field_of e f := match e, f with
  | .collection a, .collection b => a ⊆ b
  | _, _ => False

  depends_on := fun c d => if h : d ⋖ g.grid then c ⋖ (g.grid ↘ d) else False

  meet e f := match e, f with
  | .everything, x | x, .everything => x
  | .collection a, .collection b => GridElement.collection (a ∩ b)

  join e f := match e,f with
  | .everything, _ | _, .everything => .everything
  | .collection a, .collection b => GridElement.collection (a ∪ b)

  meet_component c d := c ⊝ d
  join_component c d := c ⊕ d

  top_univ e := by cases e <;> simp
  bot_univ e := by cases e with
    | everything => simp
    | collection a => simp [Finset.empty_subset]
  top_component_univ := by simp
  bot_component_univ := by
    intro c h
    exact emptygrid_sub c

  sub_trans e f g h := by grind
  sub_component_refl := sub_refl
  sub_component_trans := by
    intro c d e ⟨ hcd, hde ⟩
    simp only [sub] at *
    obtain ⟨ p_hcd, t_hcd, h_hcd ⟩ := hcd
    obtain ⟨ p_hde, t_hde, h_hde ⟩ := hde
    exact ⟨ Finset.Subset.trans p_hcd p_hde ,
    ⟨Finset.Subset.trans t_hcd t_hde , Finset.Subset.trans h_hcd h_hde ⟩ ⟩

  part_of_sub := by
    intro sg x y he ⟨ hsub, hpart ⟩
    cases x with
    | everything => cases y with
      | everything => exact hpart
      | collection _ => contradiction
    | collection a => cases y with
      | everything => contradiction
      | collection => exact Finset.Subset.trans hsub hpart

  part_of_sub_component := by
    intro sg sh x hcomp _ h
    rw [sub] at hcomp
    cases x with
    | everything => simp at h
    | collection a =>
      obtain ⟨ hsub, hpart ⟩ := h
      obtain ⟨hsp, hst, hsh ⟩ := hsub
      simp only [flatten, Finset.union_assoc]
      simp only [flatten] at hpart
      have h_g_sub : sg.plants ⊆ sh.plants
      ∧ sg.transformers ⊆ sh.transformers
      ∧ sg.houses ⊆ sh.houses →
       Finset.image GridAtom.plant sg.plants
       ∪ Finset.image GridAtom.trans sg.transformers
       ∪ Finset.image GridAtom.house sg.houses ⊆
       Finset.image GridAtom.plant sh.plants
       ∪ Finset.image GridAtom.trans sh.transformers
       ∪ Finset.image GridAtom.house sh.houses  := by
        intro ⟨hp, ht, hh⟩
        gcongr
        · exact Finset.image_subset_image hp
        · exact Finset.image_subset_image ht
        · exact Finset.image_subset_image hh
      apply Finset.Subset.trans hpart
      simp only [← Finset.union_assoc]
      exact h_g_sub ⟨ hsp, hst, hsh ⟩
/-
  depends_on_univ := by
      intro sg sh ⟨comp_sg, comp_sh⟩
      use GridElement.collection (♭sg), GridElement.collection (♭sh)
      intro h_rel
      rcases h_rel with ⟨h_sg, h_sh, h_sub ⟩
      simp only [h_sh, h_sg] at *
      simp only [comp_sh, ↓reduceDIte]
      have h_plants := flat_sub_plants h_sub
      have h_trans := flat_sub_transformers h_sub
      have h_houses := flat_sub_houses h_sub
      refine ⟨ ?_, ?_, ?_ ⟩
      · simp
        sorry
      · sorry
-/

  meet_comm := by intros; cases_type* GridElement <;> simp [Finset.inter_comm]
  meet_assoc := by intros; cases_type* GridElement <;> simp [Finset.inter_assoc]
  meet_refl := by intros; cases_type* GridElement <;> simp
  meet_intro := by intros; cases_type* GridElement <;> simp
  meet_univ := by
    intros
    constructor
    · cases_type* GridElement <;> simp ; exact Finset.subset_inter
    · cases_type* GridElement <;> simp; exact Finset.subset_inter_iff.mp
  join_comm := by intros; cases_type* GridElement <;> simp [Finset.union_comm]
  join_assoc := by intros; cases_type* GridElement <;> simp [Finset.union_assoc]
  join_refl := by intros; cases_type* GridElement <;> simp


-- Concrete

def toySubGrid : SubGrid where
  plants := {
    {id := 1},
    {id := 2}
  }
  transformers := {
    {id := 1, plantId := 1},
    {id := 2, plantId := 1},
    {id := 3, plantId := 2},
    {id := 4, plantId := 2}
  }
  houses := {
    {id := 1, transformerId := 1},
    {id := 2, transformerId := 2},
    {id := 3, transformerId := 3},
    {id := 4, transformerId := 4},
    {id := 5, transformerId := 1},
    {id := 6, transformerId := 2},
    {id := 7, transformerId := 3},
    {id := 8, transformerId := 4}
  }

theorem toySubGrid_is_coherent : toySubGrid✓ := by
  constructor
  · intros; simp [toySubGrid] at *; grind
  · intros; simp [toySubGrid] at *; grind

instance myGrid : PowerGrid where
  grid := ⟨ toySubGrid, toySubGrid_is_coherent ⟩

def EState := SystemModel.G3State

def StateAssignment := GridElement -> EState

def universally_valid : StateAssignment := fun _ => .valid
def universally_fault : StateAssignment := fun _ => .faulty

end Grid

end SystemExample
