import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

universe u v

class GraphCat (E : Type u) : Type (u + 1) where
  hom (e1 e2 : E) : Type
  id : ∀ e : E, hom e e
  comp {e1 e2 e3 : E} (v1 : hom e1 e2) (v2 : hom e2 e3) : hom e1 e3
  id_idemp {e : E} : comp (id e) (id e) = id e
  id_comp_left {e1 e2 : E} {v : hom e1 e2} : comp (id e1) v = v
  id_comp_right {e1 e2 : E} {v : hom e1 e2} : comp v (id e2) = v

inductive Component where
| mk : String -> Component
deriving DecidableEq, Repr

structure System where
  components : Finset Component
  relations : Finset (Component × Component)

def id_closure (s : System) : System :=
  {
    components := s.components,
    relations := s.relations ∪ s.components.image (fun c => (c, c))
  }

instance {σ : System} : GraphCat Component where
  hom e1 e2 := {r : Component × Component // r ∈ (id_closure σ).relations ∧ r.1 = e1 ∧ r.2 = e2 }
  id e := by
    rw [id_closure, ← Set.coe_setOf]
