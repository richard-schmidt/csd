import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic

namespace Domains

@[ext]
structure Domain where
  name : String
deriving DecidableEq, Repr

@[ext]
structure Entity where
  name : String
deriving DecidableEq, Repr

@[ext]
structure DependentField where
  source : Entity
  target : Entity
deriving DecidableEq, Repr

@[ext]
structure DomainGraph where
  nodes : Set Domain
  downstream_from : Set (Domain × Domain)

@[ext]
structure DomainGraphHom (X Y : DomainGraph) where
  node_map : Domain -> Domain
  is_injective : ∀ x ∈ X.nodes, node_map x ∈ Y.nodes
  preserves_downstream_from : ∀ {x x'},
  (x, x') ∈ X.downstream_from → (node_map x, node_map x') ∈ Y.downstream_from

def DomainGraph.comp {X Y Z : DomainGraph} (F : DomainGraphHom X Y) (G : DomainGraphHom Y Z) :
 DomainGraphHom X Z :=
  {
    node_map := G.node_map ∘ F.node_map
    is_injective := fun x hx => G.is_injective _ (F.is_injective x hx)
    preserves_downstream_from := fun h =>
     G.preserves_downstream_from (F.preserves_downstream_from h)
  }

def DomainGraph.empty : DomainGraph :=
  {
    nodes := ∅
    downstream_from := ∅
  }

def DomainGraph.id (X : DomainGraph) : DomainGraphHom X X :=
  {
    node_map x := x
    is_injective := fun _ hx => hx
    preserves_downstream_from := fun h => h
  }

open CategoryTheory

instance : Category DomainGraph where
  Hom := DomainGraphHom
  id := DomainGraph.id
  comp := DomainGraph.comp

@[ext]
structure System where
  domains : Set Domain
  entities : Set Entity
  fields : Set DependentField
  fields_in_bounds : ∀ (f: DependentField), f ∈ fields → f.source ∈ entities ∧ f.target ∈ entities
  domain_map : entities -> domains

def System.empty : System :=
  {
    domains := ∅
    entities := ∅
    fields := ∅
    fields_in_bounds := by simp
    domain_map := fun e => False.elim (Set.notMem_empty e.val e.prop)
  }

def System.domainGraph {S : System} : DomainGraph :=
  {
    nodes := S.domains
    downstream_from := Set.image (
      fun (f : {f : DependentField // f ∈ S.fields}) =>
        let ⟨src_in_bound, tgt_in_bound⟩ := S.fields_in_bounds f.val f.prop
        let src : S.entities := ⟨f.val.source, src_in_bound⟩
        let tgt : S.entities := ⟨f.val.target, tgt_in_bound⟩
        (S.domain_map src, S.domain_map tgt)
      ) (Set.univ : Set { f // f ∈ S.fields})
  }

@[ext]
structure SystemHom (X Y : System) where
  domain_map : X.domains -> Y.domains
  entity_map : X.entities -> Y.entities
  field_map : X.fields -> Y.fields :=
    fun f : {f : DependentField // f ∈ X.fields} =>
      let ⟨src_in_bound, tgt_in_bound⟩ := X.fields_in_bounds f.val f.prop
      let src : Y.entities := entity_map ⟨f.val.source, src_in_bound⟩
      let tgt : Y.entities := entity_map ⟨f.val.target, tgt_in_bound⟩
      let f' : DependentField := {
        source := src.val
        target := tgt.val
      }
      sorry
      --⟨f', Y.fields_in_bounds f'⟩

@[simp]
def System.comp {X Y Z : System} (F : SystemHom X Y) (G : SystemHom Y Z) : SystemHom X Z :=
  {
    domain_map := G.domain_map ∘ F.domain_map
    entity_map := G.entity_map ∘ F.entity_map
  }

def System.id (X : System) : SystemHom X X :=
  {
    domain_map d := d
    entity_map e := e
  }



--def systemIdLeft {X Y : System} : (F : SystemHom X Y) -> System.comp (System.id X) F = F := by
--  intros
--  dsimp [System.comp, System.id]



instance : Category System where
  Hom := SystemHom
  id := System.id
  comp := System.comp
  id_comp := sorry --systemIdLeft
  comp_id := sorry

end Domains
