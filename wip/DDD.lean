import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Products.Basic

inductive ValueType where
  | Int
  | Float
  | String
  | Date
  | Uuid
deriving Repr, DecidableEq

structure EntityAtom where
  name : String
deriving Repr, DecidableEq

inductive Entity where
| atom : EntityAtom -> Entity
| prod : Entity -> Entity -> Entity
| bot : Entity
deriving BEq, Repr

def Entity.mkprod : Entity -> Entity -> Entity
| Entity.bot, x | x, Entity.bot => x
| x, y => Entity.prod x y

notation:81 x "Δ" y => Entity.mkprod x y

structure DomainAtom where
  name : String
deriving Repr, DecidableEq

inductive Domain where
| atom : DomainAtom -> Domain
| prod : Domain -> Domain -> Domain
| bot : Domain
deriving BEq, Repr

macro "⟦" s:str "⟧" : term => `(Domain.atom {name := $s})

def Domain.mkprod : Domain -> Domain -> Domain
| Domain.bot, x | x, Domain.bot => x
| x, y => Domain.prod x y

notation:80 x "⊗" y => Domain.mkprod x y

structure System where
  domains : Set Domain
  entities : Set Entity
  entity_inclusion : entities -> domains

@[ext]
structure System.Hom (S T : System) where
  δ : Domain -> Set Domain
  ε : Entity -> Set Entity

  δ_injective : ∀ d ∈ S.domains, δ d ⊆ T.domains
  ε_injective : ∀ e ∈ S.entities, ε e ⊆ T.entities

lemma System.Hom.map_inclusion {S T : System}
(F : System.Hom S T) :
 F.δ ∘ S.entity_inclusion = T.entity_inclusion ∘ F.ε :=
  sorry

def System.empty : System :=
  {
    domains := ∅
    entities := ∅
    entity_inclusion := by grind
  }

@[simp]
def System.Hom.id (S : System) : System.Hom S S :=
  {
    δ d := {d}
    ε e := {e}

    δ_injective := by simp
    ε_injective := by simp
  }

@[simp]
def System.Hom.comp {S T U : System} (F : System.Hom S T) (G : System.Hom T U) : System.Hom S U :=
  {
    δ d := ⋃ i ∈ F.δ d, G.δ i
    ε e := ⋃ i ∈ F.ε e, G.ε i

    δ_injective := by
      intros d hd fd hfd
      obtain hsub := F.δ_injective d hd
      rcases Set.mem_iUnion₂.mp hfd with ⟨i, hi, hfd_i⟩
      have hi_T : i ∈ T.domains := hsub hi
      exact G.δ_injective i hi_T hfd_i

    ε_injective := by
      intros e he fe hfe
      obtain hsub := F.ε_injective e he
      rcases Set.mem_iUnion₂.mp hfe with ⟨i, hi, hfe_i⟩
      have hi_T : i ∈ T.entities := hsub hi
      exact G.ε_injective i hi_T hfe_i
  }

open CategoryTheory

instance : Category System where
  Hom := System.Hom
  id := System.Hom.id
  comp := System.Hom.comp
