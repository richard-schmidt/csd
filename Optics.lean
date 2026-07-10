universe u u' v v'

class Lens (S : Type u)  (T : Type u') (A : Type v) (B : Type v') : Type ((max u (max u'(max v v'))) + 1) where
  view : S -> A
  update : S -> B -> T

namespace Lens

instance idLens {X S : Type u} : Lens X S X S where
  view := fun x => x
  update := fun _ s => s

def compose {S T A B X Y : Type u} (l₁ : Lens S T A B)  (l₂ : Lens A B X Y) : Lens S T X Y :=
  {
    view := l₂.view ∘ l₁.view
    update := fun s b => l₁.update s (l₂.update (l₁.view s) b)
  }

theorem idLensIdLeftView {S T A B} {l : Lens S T A B} : (compose idLens l).view = l.view := by simp
theorem idLensIdRightView {S T A B} {l : Lens S T A B} : (compose l idLens).view = l.view := by simp

theorem idLensIdLeftUpdate{S T A B} {l : Lens S T A B} : (compose idLens l).update = l.update := by simp
theorem idLensIdRightUpdate {S T A B} {l : Lens S T A B} : (compose l idLens).update = l.update := by simp

def prod {S T A B X Y V W : Type u} (l₁ : Lens S T A B) (l₂ : Lens X Y V W) : Lens (S × X) (T × Y) (A × V) (B × W) :=
  {
    view := fun (s, x) =>
      let a := l₁.view s
      let v := l₂.view x
      (a, v)
    update := fun (s, x) (b, w) =>
      let t := l₁.update s b
      let y := l₂.update x w
      (t, y)
  }

end Lens

structure ExState where
  state : List Int
deriving Repr

def updaterLens : Lens ExState ExState (List Int) (Int) :=
  {
    view := fun s => s.state
    update := fun in_state new_data => {state := in_state.state.append [new_data]}
  }

def s_in : ExState := {state := [1, 2]}

#eval updaterLens.view s_in
#eval updaterLens.update s_in 3
#eval (Lens.compose Lens.idLens updaterLens).update s_in 3

structure ExBundled where
  extra_data : Int
  wrapped_state : ExState
deriving Repr

def bundleLens : Lens ExBundled ExBundled ExState ExState :=
  {
    view := fun b => b.wrapped_state
    update := fun in_bundle new_state => {extra_data := in_bundle.extra_data, wrapped_state := new_state}
  }

def bundle_ex : ExBundled := {extra_data := 1, wrapped_state := s_in}

#eval bundle_ex
#eval (Lens.compose bundleLens updaterLens).update bundle_ex 3
