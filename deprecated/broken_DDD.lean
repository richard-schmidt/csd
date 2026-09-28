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

inductive DomainSyntax where
  | atom : (name : String) -> DomainSyntax
  | bot : DomainSyntax
  | meet : DomainSyntax -> DomainSyntax -> DomainSyntax
deriving Repr, DecidableEq

notation "⊥ₛ" => DomainSyntax.bot
notation d1 " Δₛ " d2 => DomainSyntax.meet d1 d2

inductive DomainRel : DomainSyntax -> DomainSyntax -> Prop where
  | refl (d : DomainSyntax) : DomainRel d d
  | symm {d1 d2 : DomainSyntax} : DomainRel d1 d2 -> DomainRel d2 d1
  | trans {d1 d2 d3 : DomainSyntax} : DomainRel d1 d2 -> DomainRel d2 d3 -> DomainRel d1 d3
  | comm (d1 d2 : DomainSyntax) : DomainRel (d1 Δₛ d2) (d2 Δₛ d1)
  | absorb (d : DomainSyntax) : DomainRel (d Δₛ ⊥ₛ) ⊥ₛ
  | meet_congr {d1 d2 d3 d4 : DomainSyntax} :
      DomainRel d1 d3 → DomainRel d2 d4 → DomainRel (d1 Δₛ d2) (d3 Δₛ d4)

instance domainSetoid : Setoid DomainSyntax where
  r := DomainRel
  iseqv := {
    refl := DomainRel.refl
    symm := DomainRel.symm
    trans := DomainRel.trans
  }

def Domain := Quotient domainSetoid

def toDomain (s : DomainSyntax) : Domain := Quotient.mk domainSetoid s
notation "⟦" s "⟧" => toDomain s

inductive Entity where
  | atom (name : String) (domain : Domain) : Entity
  | bot : Entity
  | prod : Entity -> Entity -> Entity

notation "⊥ₑ" => Entity.bot
notation e1 "Δₑ" e2 => Entity.prod e1 e2

@[simp]
def Entity.domain : Entity -> Domain :=
  fun e => match e with
  | ⊥ₑ => Quotient.mk domainSetoid ⊥ₛ
  | Entity.atom _ d => d
  | e1 Δₑ e2 => Quotient.mk domainSetoid (e1.domain.out Δₛ e2.domain.out)

inductive FieldType where
  | value : ValueType -> FieldType
  | entity : Entity -> FieldType
  | reference : Entity -> FieldType
deriving Repr, DecidableEq

structure Field (_ : Entity) where
  name : String
  type : FieldType
deriving Repr, DecidableEq

structure System where
  domains : Set Domain
  entities : Set Entity
  fields (e : Entity) : Set (Field e)
  completeness : ∀ e ∈ entities, e.domain ∈ domains

@[ext]
structure SystemHom (S T : System) where
  domain_map : Domain -> Set Domain
  entity_map : Entity -> Set Entity

  domain_injective : ∀ d ∈ S.domains, domain_map d ⊆ T.domains
  entity_injective : ∀ e ∈ S.entities, entity_map e ⊆ T.entities

@[simp]
def SystemHom.id (S : System) : SystemHom S S:=
  {
    domain_map d := {d}
    entity_map e := {e}

    domain_injective d hd := by
      rw [Set.subset_def]
      intros x' hx
      obtain he : x' = d := by
        exact hx
      rw [he]
      exact hd
    entity_injective e he := by
      rw [Set.subset_def]
      intros x' hx
      obtain he' : x' = e := by
        exact hx
      rw [he']
      exact he
  }

def System.empty : System :=
  {
    domains := ∅
    entities := ∅
    fields _ := ∅
    completeness := by simp
  }

@[simp]
def SystemHom.comp {S T U : System} (F : SystemHom S T) (G : SystemHom T U) : SystemHom S U :=
  {
    domain_map d := ⋃ i ∈ F.domain_map d, G.domain_map i
    entity_map e := ⋃ i ∈ F.entity_map e, G.entity_map i
    domain_injective := by
      intros d hd fd hfd
      obtain hsub := (F.domain_injective d hd)
      rcases Set.mem_iUnion₂.mp hfd with ⟨i, hi, hfd_i⟩
      have hi_T : i ∈ T.domains := hsub hi
      exact G.domain_injective i hi_T hfd_i
    entity_injective := by
      intros e he fe hfe
      obtain hsub := F.entity_injective e he
      rcases Set.mem_iUnion₂.mp hfe with ⟨i, hi, hfe_i⟩
      have hi_T : i ∈ T.entities := hsub hi
      exact G.entity_injective i hi_T hfe_i
  }

--@[simp]
---- Internal Coproduct
--def System.join (S T : System) : System :=
--  {
--    domains := S.domains ∪ T.domains
--    entities := S.entities ∪ T.entities
--    fields e := S.fields e ∪ T.fields e
--    completeness := by
--      intros e he
--      rw [Set.mem_union]
--      exact he.imp (S.completeness e) (T.completeness e)
--  }

@[simp]
-- Internal product
def System.meet (S T : System) : System :=
  {
    domains := {x | ∃ i1 ∈ S.domains, ∃ i2 ∈ T.domains, x = i1 Δ i2}
    entities := {x | ∃ i1 ∈ S.entities, ∃ i2 ∈ T.entities, x = i1 Δₑ i2}
    fields e := S.fields e ∩ T.fields e
    completeness := by
      intros e he
      sorry
  }

infix:80 "⊓" => System.meet
--infix:81 "⊔" => System.join

open CategoryTheory

instance SystemCat : Category System where
  Hom := SystemHom
  id := SystemHom.id
  comp := SystemHom.comp
  id_comp := by
    intros
    ext
    · dsimp [SystemHom.comp, SystemHom.id]
      simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
    · dsimp [SystemHom.comp, SystemHom.id]
      simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]

  comp_id := by
    intros S T F
    ext
    · dsimp [SystemHom.comp, SystemHom.id]
      simp only [Set.biUnion_of_singleton]
    · dsimp [SystemHom.comp, SystemHom.id]
      simp only [Set.biUnion_of_singleton]

@[ext]
lemma System.hom_ext {S T : System} (f g : S ⟶ T)
  (h_dom : f.domain_map = g.domain_map)
  (h_ent : f.entity_map = g.entity_map) : f = g := by
  exact SystemHom.ext h_dom h_ent

def meetFunctor : System × System ⥤ System where
  obj π := π.1 ⊓ π.2
  map {X Y} F := {
    domain_map d := {x | ∃ i1 ∈ F.1.domain_map d, ∃ i2 ∈ F.2.domain_map d, x = i1 Δ i2}
    entity_map e := {x | ∃ i1 ∈ F.1.entity_map e, ∃ i2 ∈ F.2.entity_map e, x = i1 Δₑ i2}
    domain_injective := by
      sorry
    entity_injective := by
      sorry
  }
  map_comp := sorry
