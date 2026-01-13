import Mathlib.Data.Finset.Basic

universe u v

class SmallGroupoid (A : Type u) : Type (u + 1) where
  carrier : Finset A
  ob := {x₀ : A // x₀ ∈ carrier}
  hom : ∀ _ _ : ob, Type
  comp : ∀ {x y z : ob}, hom x y -> hom y z -> hom x z
  id : ∀ x : ob, hom x x
  inv : ∀ {x y : ob}, hom x y -> hom y x
  assoc : ∀ {w x y z : ob} (f : hom w x) (g : hom x y) (h : hom y z),
  comp (comp f g ) h = comp f (comp g h)
  unitality : ∀ {x y : ob} (f : hom x y), comp f (id y) = f ∧ comp (id x) f = f
  left_inv : ∀ {x y : ob} (f : hom x y), comp (inv f) f = id y
  right_inv : ∀ {x y : ob} (f : hom x y), comp f (inv f) = id x


class SGFun {α : Type u} {β : Type v} (A : SmallGroupoid α) (B : SmallGroupoid β) :
Type ((max u v) + 1) where
  objectMap : A.ob -> B.ob
  homMap : ∀ {x y : A.ob}, (A.hom x y) -> (B.hom (objectMap x) (objectMap y))
  compMap : ∀ {x y z : A.ob} (f : A.hom x y) (g : A.hom y z),
   B.comp (homMap f) (homMap g) = homMap (A.comp f g)
  idMap : ∀ (x : A.ob), homMap (A.id x) = B.id (objectMap x)


class SGNat {α : Type u} {β : Type v}
  {A : SmallGroupoid α} {B : SmallGroupoid β}
  (F G : SGFun A B) : Type ((max u v) + 2) where
  η : ∀ (x : A.ob), B.hom (F.objectMap x) (G.objectMap x)
  homEq : ∀ {x y : A.ob} (f : A.hom x y),
    B.comp (F.homMap f) (η y) = B.comp (η x) (G.homMap f)


def sgNatComp
{α : Type u} {β : Type v}
{A : SmallGroupoid α} {B : SmallGroupoid β}
{F G H : SGFun A B}
(η₁ : SGNat F G) (η₂ : SGNat G H) : SGNat F H where
  η x := B.comp (η₁.η x) (η₂.η x)
  homEq {x y : A.ob} (f : A.hom x y) := by
    sorry
