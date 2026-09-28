import Mathlib.Data.Finset.Basic

namespace Cats

class SmallCat (Obj : Type u) : Type (u + 1) where
  hom : ∀ _ _ : Obj, Type
  id : ∀ x, hom x x
  comp : ∀ {A B C : Obj}, hom A B -> hom B C -> hom A C
  id_left : ∀ {A B : Obj} (f : hom A B), comp (id A) f = f
  id_right : ∀ {A B : Obj} (f : hom A B),  comp f (id B) = f
  assoc : ∀ {A B C D} (f : hom A B) (g : hom B C) (h : hom C D),
    comp (comp f g) h = comp f (comp g h)

infixl:65 " ⟶ " => SmallCat.hom
notation g " ∘ " f  => SmallCat.comp f g

class MyPreorder (a : Type u) : Type (u + 1) where
  leq : a -> a -> Prop
  reflex : ∀ x, leq x x
  transitive : ∀ x y z, leq x y -> leq y z -> leq x z

instance PreorderCat A [MyPreorder A] : SmallCat A where
  hom a b := PLift (MyPreorder.leq a b)
  id a := ⟨ MyPreorder.reflex a ⟩
  comp { a b c } f g := ⟨ MyPreorder.transitive a b c f.down g.down ⟩
  id_left := by
    intro A B f
    simp
  id_right := by
    intro A B f
    simp
  assoc := by
    intro A B C f g h
    simp

class SmallFunctor {o₁ : Type u} {o₂ : Type v} (A : SmallCat o₁) (B : SmallCat o₂) :
Type ((max u v) + 2) where
  ob : o₁ -> o₂
  map : ∀ {X Y : o₁} , (X ⟶ Y) -> (ob X ⟶ ob Y)
  map_id : id ob  = ob
  map_com : ∀ {X Y Z : o₁} (f : X ⟶ Y) (g : Y ⟶ Z), map (g ∘ f)= (map g) ∘ (map f)

instance IdentityFunctor {o : Type} (A : SmallCat o) : SmallFunctor A A where
  ob X := X
  map f := f
  map_id := by simp
  map_com := by simp

end Cats
