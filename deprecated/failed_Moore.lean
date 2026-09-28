import Showcase.Optics
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic


structure MooreObject α β where
  state : Type
  lens : Lens state state β α

@[ext]
structure MooreHom {α β} (X Y : MooreObject α β) where
  toFun : X.state -> Y.state
  univ_u : ∀ (s : X.state) (input : α),
   toFun (X.lens.update s input) = Y.lens.update (toFun s) input
  univ_r : ∀ (s : X.state),
   X.lens.view s = Y.lens.view (toFun s)

instance {α β} {X Y : MooreObject α β} : CoeFun (MooreHom X Y) (fun _ => X.state -> Y.state) :=
⟨fun f => f.toFun⟩

def mooreId {α β} (X : MooreObject α β) : MooreHom X X where
  toFun := id
  univ_u _ _ := rfl
  univ_r _ := rfl

def mooreComp {α β} {X Y Z : MooreObject α β} (f : MooreHom X Y) (g : MooreHom Y Z) :
 MooreHom X Z where
  toFun := g.toFun ∘ f.toFun
  univ_u _ _ := by
    dsimp
    rw [f.univ_u, g.univ_u]
  univ_r _ := by
    dsimp
    rw [f.univ_r, g.univ_r]

instance {α β} : Category (MooreObject α β) where
    Hom := MooreHom
    id := mooreId
    comp := mooreComp

def mooreTensorProd {α β α' β'} (X : MooreObject α β) (Y : MooreObject α' β') :
 MooreObject (α × α') (β × β') where
  state := X.state × Y.state
  lens := Lens.prod X.lens Y.lens

def mooreTensorProdHom {α β} {A B C D : MooreObject α β}
  (f : A ⟶ B) (g : C ⟶ D) : mooreTensorProd A C ⟶ mooreTensorProd B D :=
  {
    toFun := fun (a, c) => (f.toFun a, g.toFun c)
    univ_u := by
      rintro ⟨a, c⟩ ⟨i, j⟩
      dsimp [mooreTensorProd, Lens.prod]
      rw [f.univ_u, g.univ_u]
    univ_r := by
      rintro ⟨a, c⟩
      dsimp [mooreTensorProd, Lens.prod]
      rw [f.univ_r, g.univ_r]
  }

def BundledMoore := Σ (α β : Type), MooreObject α β

def mooreTensorUnit {α β} : MooreObject α β :=
  {
    state := Unit
    lens := {
      view := sorry -- β needs a terminal object ?
      update := fun _ _ => PUnit.unit
    }
  }

instance : MonoidalCategory BundledMoore where
  tensorObj := mooreTensorProd
  tensorHom f g := mooreTensorProdHom f g
  tensorUnit := mooreTensorUnit
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry
  whiskerLeft := sorry
  whiskerRight := sorry
