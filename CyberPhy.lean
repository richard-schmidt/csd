import Categorical.Optics
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic

universe u v

structure Box where
  σᵢ : Type
  σₒ : Type

@[ext]
structure boxHom (A B : Box) where
  in_comp : A.σₒ × B.σᵢ -> A.σᵢ
  out_comp : A.σₒ -> B.σₒ

def boxTensorProd (A B : Box) : Box where
    σᵢ := A.σᵢ × B.σᵢ
    σₒ := A.σₒ × B.σₒ

def boxUnit : Box where
  σᵢ := Unit
  σₒ := Unit

infix:80 " ⊠ " => boxTensorProd

@[simp]
def boxComp {A B C : Box} (f : boxHom A B) (g : boxHom B C) : boxHom A C :=
  {
    in_comp := fun (x', z) => f.in_comp (x', (g.in_comp (f.out_comp x', z)))
    out_comp := fun x' => g.out_comp (f.out_comp x')
  }

def boxId (A : Box) : boxHom A A  :=
  {
    in_comp := fun (_, a_in) => a_in
    out_comp := id
  }

open CategoryTheory

-- Box is a Category

instance : Category Box where
  Hom := boxHom
  id := boxId
  comp := boxComp
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; ext <;> rfl

def boxTensorHom {A B C D : Box} (f : A ⟶ B) (g : C ⟶ D) : A ⊠ C ⟶ B ⊠ D :=
  {
   in_comp := fun (x, z) => (f.in_comp (x.1, z.1), g.in_comp (x.2, z.2))
   out_comp := fun x => (f.out_comp x.1, g.out_comp x.2)
  }

def boxTensorAssoc (A B C : Box) : (A ⊠ B) ⊠ C ≅ A ⊠ (B ⊠ C) :=
    {
      hom := {
        in_comp := fun (_, (a, (b, c))) => ((a, b), c)
        out_comp := fun ((a, b), c) => (a, (b, c))
      }
      inv := {
        in_comp := fun (_, ((a, b), c)) => (a, (b, c))
        out_comp := fun (a, (b, c)) => ((a, b), c)
      }

      hom_inv_id := by exact rfl
      inv_hom_id := by exact rfl
    }

def boxLeftUnitor : (A : Box) -> boxUnit ⊠ A ≅ A :=
  fun _ => {
    hom := {
      in_comp := fun (_, a) => (PUnit.unit, a)
      out_comp := fun (_, a) => a
    }
    inv := {
      in_comp := fun (_, (_, a)) => a
      out_comp := fun a => (PUnit.unit, a)
    }

    hom_inv_id := by exact rfl
    inv_hom_id := by exact rfl
  }

def boxRightUnitor : (A : Box) -> A ⊠ boxUnit ≅ A :=
  fun _ => {
    hom := {
      in_comp := fun (_, a) => (a, PUnit.unit)
      out_comp := fun (a, _) => a
    }
    inv := {
      in_comp := fun (_, (a, _)) => a
      out_comp := fun a => (a, PUnit.unit)
    }

    hom_inv_id := by exact rfl
    inv_hom_id := by exact rfl
  }

def boxWhiskerLeft : (A : Box) -> {B C : Box} -> (B ⟶ C) -> (A ⊠ B ⟶ A ⊠ C) :=
  fun _ _ _ f  => {
    in_comp := fun ((_, bₒ), (aᵢ, cᵢ)) => (aᵢ, f.in_comp (bₒ, cᵢ))
    out_comp := fun (aₒ, bₒ) => (aₒ, f.out_comp bₒ)
  }

def boxWhiskerRight : {A B : Box} -> (A ⟶ B) -> (C : Box) -> (A ⊠ C ⟶ B ⊠ C) :=
  fun f _ => {
    in_comp := fun ((aₒ, _), (bᵢ, cᵢ)) => (f.in_comp (aₒ, bᵢ), cᵢ)
    out_comp := fun (aₒ, cₒ) => (f.out_comp aₒ, cₒ)
  }

-- BoxCat is monoidal

instance : MonoidalCategory Box where
  tensorObj := boxTensorProd
  tensorHom := boxTensorHom
  tensorUnit := boxUnit
  associator := boxTensorAssoc
  leftUnitor := boxLeftUnitor
  rightUnitor := boxRightUnitor
  whiskerLeft := boxWhiskerLeft
  whiskerRight := boxWhiskerRight

-- Algebras on Box
open MonoidalCategory

structure BoxLaxMonoidalFunctor {ℂ} [Category ℂ] [MonoidalCategory ℂ] (F : Box ⥤ ℂ) where
  μ : ∀ (X Y : Box), (F.obj X ⊗ F.obj Y) ⟶ F.obj (X ⊗ Y) -- laxator
  ε : 𝟙_ ℂ ⟶ F.obj (𝟙_ Box) -- unit

-- Moore machines

structure MooreMachine where
  α : Type
  β : Type
  state : Type
  lens : Lens state state β α

def mooreUnit : MooreMachine :=
  {
    α := Unit
    β := Unit
    state := Unit
    lens := {
      view := id
      update := fun _ _ => PUnit.unit
    }
  }

@[ext]
structure MooreHom (X Y : MooreMachine) where
  s_map : X.state -> Y.state
  i_map : Y.α -> X.α
  o_map : X.β -> Y.β

  univ_u : ∀ (s : X.state) (input : Y.α),
   s_map (X.lens.update s (i_map input)) = Y.lens.update (s_map s) input
  univ_r : ∀ (s : X.state),
    o_map (X.lens.view s) = Y.lens.view (s_map s)

def mooreId (A : MooreMachine) : MooreHom A A :=
  {
    s_map := id
    i_map := id
    o_map := id
    univ_u := by simp
    univ_r := by simp
  }

def MooreComp {A B C : MooreMachine} (f : MooreHom A B) (g : MooreHom B C) : MooreHom A C :=
  {
    s_map := g.s_map ∘ f.s_map
    i_map := f.i_map ∘ g.i_map
    o_map := g.o_map ∘ f.o_map

    univ_u := by
      intros a_state α_c
      dsimp [Function.comp]
      rw [f.univ_u]
      rw [g.univ_u]

    univ_r := by
      intros a_state
      dsimp [Function.comp]
      rw [f.univ_r]
      rw [g.univ_r]
  }

instance : Category MooreMachine where
  Hom := MooreHom
  id := mooreId
  comp := MooreComp

def MooreTensorProd (X Y : MooreMachine) : MooreMachine :=
  {
    state := X.state × Y.state
    α := X.α × Y.α
    β := X.β × Y.β
    lens := Lens.prod X.lens Y.lens
  }

infix:80 " ⊠ " => MooreTensorProd

def MooreTensorHom {A B C D : MooreMachine} (f : A ⟶ B) (g : C ⟶ D) : (A ⊠ C) ⟶ (B ⊠ D) :=
  {
    s_map := fun (xₛ, cₛ) => (f.s_map xₛ, g.s_map cₛ)
    i_map := fun (bᵢ, dᵢ) => (f.i_map bᵢ, g.i_map dᵢ)
    o_map := fun (xₒ, cₒ) => (f.o_map xₒ, g.o_map cₒ)
    univ_u := by
      rintro ⟨a_state, c_state⟩ ⟨ b_input, d_input⟩
      dsimp [MooreTensorProd, Lens.prod]
      rw [f.univ_u, g.univ_u]
    univ_r := by
      rintro ⟨ a_state, c_state ⟩
      dsimp [MooreTensorProd, Lens.prod]
      rw [f.univ_r, g.univ_r]
  }

def MooreTensorAssoc (A B C : MooreMachine) : (A ⊠ B) ⊠ C ≅ A ⊠ (B ⊠ C) :=
  {
    hom := {
      s_map := fun ((a, b), c) => (a, (b, c))
      i_map := fun (a, (b, c)) => ((a, b), c)
      o_map := fun ((a, b), c) => (a, (b, c))
      univ_u := by
        rintro ⟨⟨a_state, b_state⟩, c_state⟩ ⟨a_input, ⟨b_input, c_input⟩⟩
        rfl
      univ_r := by
        rintro ⟨⟨a_state, b_state⟩, c_state⟩
        rfl
    }
    inv := {
      s_map := fun (a, (b, c)) => ((a, b), c)
      i_map := fun ((a, b), c) => (a, (b, c))
      o_map := fun (a, (b, c)) => ((a, b), c)
      univ_u := by
        rintro ⟨a_state, ⟨b_state, c_state⟩⟩ ⟨⟨a_input, b_input⟩, c_input⟩
        rfl
      univ_r := by
        rintro ⟨a_state, ⟨b_state, c_state⟩⟩
        rfl
    }
  }

def MooreLeftUnitor (X : MooreMachine) : mooreUnit ⊠ X ≅ X :=
  {
    hom := {
      s_map := fun (_, x) => x
      i_map := fun x => (PUnit.unit, x)
      o_map := fun (_, x) => x
      univ_u := by
        rintro _ _
        rfl
      univ_r := by
        rintro _
        rfl
    }
    inv := {
      s_map := fun x => (PUnit.unit, x)
      i_map := fun (_, x) => x
      o_map := fun x => (PUnit.unit, x)
      univ_u := by
        rintro _ _
        rfl
      univ_r := by
        rintro _
        rfl
    }
  }

def MooreRightUnitor (X : MooreMachine) : X ⊠ mooreUnit ≅ X :=
  {
    hom := {
      s_map := fun (x, _) => x
      i_map := fun x => (x, PUnit.unit)
      o_map := fun (x, _) => x
      univ_u := by
        rintro _ _
        rfl
      univ_r := by
        rintro _
        rfl
    }
    inv := {
      s_map := fun x => (x, PUnit.unit)
      i_map := fun (x, _) => x
      o_map := fun x => (x, PUnit.unit)
      univ_u := by
        rintro _ _
        rfl
      univ_r := by
        rintro _
        rfl
    }
  }

def MooreWhiskerLeft : (A : MooreMachine) -> {B C : MooreMachine} -> (B ⟶ C) -> (A ⊠ B ⟶ A ⊠ C) :=
  fun _ _ _ f => {
    s_map := fun (a, b) => (a, f.s_map b)
    i_map := fun (a, c) => (a, f.i_map c)
    o_map := fun (a, b) => (a, f.o_map b)
    univ_u := by
      rintro ⟨_, _⟩ ⟨_, _⟩
      dsimp [MooreTensorProd, Lens.prod]
      rw [f.univ_u]
    univ_r := by
      rintro ⟨_, _⟩
      dsimp [MooreTensorProd, Lens.prod]
      rw [f.univ_r]
  }

def MooreWhiskerRight : {A B : MooreMachine} -> (A ⟶ B) -> (C : MooreMachine) -> (A ⊠ C ⟶ B ⊠ C) :=
  fun f _ => {
    s_map := fun (a, c) => (f.s_map a, c)
    i_map := fun (b, c) => (f.i_map b, c)
    o_map := fun (a, c) => (f.o_map a, c)
    univ_u := by
      rintro ⟨_, _⟩ ⟨_, _⟩
      dsimp [MooreTensorProd, Lens.prod]
      rw [f.univ_u]
    univ_r := by
      rintro ⟨_, _⟩
      dsimp [MooreTensorProd, Lens.prod]
      rw [f.univ_r]
  }

instance : MonoidalCategory MooreMachine where
  tensorObj := MooreTensorProd
  tensorHom := MooreTensorHom
  tensorUnit := mooreUnit
  associator := MooreTensorAssoc
  leftUnitor := MooreLeftUnitor
  rightUnitor := MooreRightUnitor
  whiskerLeft := MooreWhiskerLeft
  whiskerRight := MooreWhiskerRight
