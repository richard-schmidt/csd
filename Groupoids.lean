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
  η := fun x => B.comp (η₁.η x) (η₂.η x)
  homEq {x y : A.ob} (f : A.hom x y) := by
    rw [← B.assoc (F.homMap f) (η₁.η y) (η₂.η y)]
    rw [η₁.homEq f]
    rw [B.assoc (η₁.η x) (G.homMap f) (η₂.η y)]
    rw [η₂.homEq f]
    rw [B.assoc (η₁.η x) (η₂.η x) (H.homMap f)]


class HomGrpd {α : Type u} {β : Type v} (A : SmallGroupoid α) (B : SmallGroupoid β) :
Type ((max u v) + 3) where
  hom : ∀ (_ _ : SGFun A B), (Type ((max u v) + 2))
  comp : ∀ {F G H : SGFun A B}, hom F G -> hom G H -> hom F H
  assoc : ∀ {F G H I : SGFun A B} (α : hom F G) (β : hom G H) (σ : hom H I),
  comp (comp α β ) σ = comp α (comp β σ)
  id : ∀ {F : SGFun A B}, hom F F
  unitality : ∀ {F G : SGFun A B} (f : hom F G), comp f id = f ∧ comp id f = f


def TwoObGpd : SmallGroupoid ℕ where
  carrier := {1, 2}
  hom x y := PLift (x = y)
  comp f g := ⟨ Eq.trans f.down g.down ⟩
  id _ := ⟨rfl⟩
  inv f := ⟨f.down.symm⟩
  assoc _ _ _ := rfl
  unitality _ := ⟨rfl, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

def TwoIsoGpd : SmallGroupoid ℕ where
  carrier := {1, 2}
  hom _ _ := PLift (true)
  comp f g := ⟨ Eq.trans f.down g.down ⟩
  id _ := ⟨rfl⟩
  inv f := ⟨f.down.symm⟩
  assoc _ _ _ := rfl
  unitality _ := ⟨rfl, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

def F : SGFun TwoObGpd TwoIsoGpd where
 objectMap x := ⟨ 1, by simp ⟩
 homMap _ := ⟨ rfl ⟩
 compMap _ _ := rfl
 idMap _ := rfl

def G : SGFun TwoObGpd TwoIsoGpd where
 objectMap x := ⟨ 2, by simp ⟩
 homMap _ := ⟨ rfl ⟩
 compMap _ _ := rfl
 idMap _ := rfl

def NatFG : SGNat F G where
  η _ := ⟨ rfl ⟩
  homEq _ := rfl

instance : HomGrpd TwoObGpd TwoIsoGpd where
  hom F G := SGNat F G
  comp := sgNatComp
  id := {η := fun _ => ⟨ rfl ⟩ , homEq := fun _ => rfl}
  assoc := by intros; rfl
  unitality := by
    intros
    apply And.intro rfl
    exact rfl
