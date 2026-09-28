import Init.Core
import Showcase.HeytAlg

namespace SystemModel

universe u v

class System (Component : Type v) (Element : Type u) : Type ((max u v) + 1) where

  top : Element
  bot : Element

  top_component : Component
  bot_component : Component

  component : Component -> Prop -- component x ~ x ∈ system.components
  entity : Element -> Prop -- entity c ~ x ∈ system.entities

  sub : Element -> Element -> Prop -- sub x y ~ x ⊆ y for entities
  sub_component : Component -> Component -> Prop  -- x ⊆ y for components

  part_of : Element -> Component -> Prop -- entity to component relation
  field_of : Element -> Element -> Prop -- e is referenced in f

  depends_on : Component -> Component -> Prop  -- some part of c depends on some part of d

  meet : Element -> Element -> Element
  join : Element -> Element -> Element

  meet_component : Component -> Component -> Component
  join_component : Component -> Component -> Component

  top_univ : ∀ e : Element, sub e top -- top is a maximal element
  bot_univ : ∀ e : Element, sub bot e -- bot is a minimal element

  top_component_univ : ∀ c : Component, component c → sub_component c top_component
  bot_component_univ : ∀ c : Component, component c → sub_component bot_component c

  sub_trans : ∀ e f g : Element, sub e f ∧ sub f g → sub e g

  sub_component_refl : ∀ c : Component, sub_component c c
  sub_component_trans : ∀ c d e : Component, sub_component c d ∧ sub_component d e → sub_component c e

  part_of_sub : ∀ {c : Component} {e f : Element}, entity e → sub e f ∧ part_of f c → part_of e c
  part_of_sub_component : ∀ {c d : Component} {e : Element}, component c → entity e → sub_component c d ∧ part_of e c → part_of e d

  -- Would be great
  --depends_on_univ : ∀ c d : Component, component c ∧ component d → ∃ e f, part_of e c ∧ part_of f d ∧ field_of e f → depends_on c d

  meet_comm : ∀ {e f}, meet e f = meet f e
  meet_assoc : ∀ {e f g}, meet e (meet f g) = meet (meet e f) g
  meet_refl : ∀ {e}, meet e e = e
  meet_intro : ∀ {e f : Element}, sub (meet e f) e ∧ sub (meet e f) f
  meet_univ : ∀ {e f g : Element},  sub e f ∧ sub e g ↔ sub e (meet f g)

  join_comm : ∀ {e f}, join e f = join f e
  join_assoc : ∀ {e f g}, join e (join f g) = join (join e f) g
  join_refl : ∀ {e}, join e e = e

open System

infix:50 " ⊆ " => sub
infix:60 " ⊸ " => field_of
infix:65 " ⊓ " => meet
infix:70 " ⊔ " => join

infix:50 " ⊏ " => sub_component
infix:60 " ◃ " => depends_on
infix:65 " ⊠ " => meet_component
infix:70 " ⊞ " => join_component

section
  variable{Component : Type v}  {Element : Type u}
  variable [s : System Component Element]
  variable (e f : Element)

  theorem meet_idemp {e f : Element} : s.meet e ( s.meet e f) = s.meet e f := by
    rw [meet_assoc, meet_refl]

  theorem join_idemp {e f : Element} : s.join e (s.join e f) = s.join e f := by
    rw [join_assoc, join_refl]

end section

inductive State where
  | faulty
  | unknown
  | valid
deriving DecidableEq, Repr

open State

@[reducible]
def G3State := State

@[reducible]
def K3State := State

@[reducible]
def state_to_int : State -> Int
| .faulty => 0
| .unknown => 1
| .valid => 2

namespace G3
-- G3 logic
@[simp]
def state_le (S1 S2 : G3State) : Prop :=
 state_to_int S1 ≤ state_to_int S2
deriving Decidable

@[simp]
def state_meet : G3State -> G3State -> G3State
| S1, S2 => if state_le S1 S2 then S1 else S2

@[simp]
def state_join : G3State -> G3State -> G3State
| S1, S2 => if state_le S1 S2 then S2 else S1

@[simp]
def state_implies : G3State -> G3State -> G3State
| S1, S2 => if state_le S1 S2 then .valid else S2

scoped infix:50 " ◃ " => state_le
scoped infixl:65 " ⊔ " => state_join
scoped infixl:75 " ⊓ " => state_meet
scoped infixr:50 " ⊸ " => state_implies

@[simp]
def state_neg (S1 : G3State) : G3State := S1 ⊸ .faulty

scoped prefix:80 "¬" => state_neg

@[simp]
def state_box (S1 : G3State) : G3State := if S1 = .valid then .valid else .faulty

scoped prefix:79 "□" => state_box

@[simp]
def state_diamond (S1 : G3State) : G3State := ¬ ¬ S1

scoped prefix:78 "◇" => state_diamond

@[simp]
theorem state_bot_join (S1 : G3State) : S1 ⊔ .faulty = S1 :=
  by cases S1 <;> decide

@[simp]
theorem state_top_join (S1 : G3State) : S1 ⊔ .valid = .valid :=
  by cases S1 <;> decide

@[simp]
theorem state_bot_meet (S1 : G3State) : S1 ⊓ .faulty = .faulty :=
  by cases S1 <;> decide

@[simp]
theorem state_top_meet (S1 : G3State) : S1 ⊓ .valid = S1 :=
  by cases S1 <;> decide

@[simp]
theorem state_join_comm (S1 S2 : G3State) : S1 ⊔ S2 = S2 ⊔ S1 := by
  cases S1 <;> cases S2
  all_goals decide

@[simp]
theorem state_meet_comm (S1 S2 : G3State) : S1 ⊓ S2 = S2 ⊓ S1 := by
  cases S1 <;> cases S2
  all_goals decide

@[simp]
theorem state_meet_assoc (S1 S2 S3 : G3State) : (S1 ⊓ S2) ⊓ S3 = S1 ⊓ (S2 ⊓ S3) := by
  cases S1 <;> cases S2 <;> cases S3
  all_goals decide

@[simp]
theorem state_join_assoc (S1 S2 S3 : G3State) : S1 ⊔ (S2 ⊔ S3) = (S1 ⊔ S2) ⊔ S3:= by
  cases S1 <;> cases S2 <;> cases S3
  all_goals decide

@[simp]
theorem state_join_univ : ∀ S1 S2 S3 : G3State, S1 ⊔ S2 ◃ S3 ↔ S1 ◃ S3 ∧ S2 ◃ S3 :=
  fun S1 S2 S3 => Iff.intro
  (fun h : S1 ⊔ S2 ◃ S3 => show S1 ◃ S3 ∧ S2 ◃ S3 from
    (by cases S1 <;> cases S2 <;> cases S3 <;> (first | contradiction | decide)))
  (fun h : S1 ◃ S3 ∧ S2 ◃ S3 => show S1 ⊔ S2 ◃ S3 from
    (by cases S1 <;> cases S2 <;> cases S3 <;> (first | contradiction | decide)) )

@[simp]
theorem state_meet_univ : ∀ S1 S2 S3 : G3State, S1 ◃ S2 ⊓ S3 ↔ S1 ◃ S2 ∧ S1 ◃ S3 :=
  fun S1 S2 S3 => Iff.intro
    (fun h : S1 ◃ S2 ⊓ S3 => show S1 ◃ S2 ∧ S1 ◃ S3 from
      (by cases S1 <;> cases S2 <;> cases S3 <;> all_goals (first | contradiction | decide)))
    (fun h : S1 ◃ S2 ∧ S1 ◃ S3 => show S1 ◃ S2 ⊓ S3 from
      (by cases S1 <;> cases S2 <;> cases S3 <;> all_goals (first | contradiction | decide)))

@[simp]
theorem state_implies_univ (S1 S2 S3 : G3State) : ((S1 ⊓ S2) ◃ S3) ↔ (S1 ◃ (S2 ⊸ S3)) := by
  cases S1 <;> cases S2 <;> cases S3
  all_goals decide

@[simp]
theorem state_join_absorb (S1 S2 : G3State) : S1 ⊓ (S1 ⊔ S2) = S1 := by
cases S1 <;> cases S2 <;> decide

@[simp]
theorem state_meet_absorb (S1 S2 : G3State) : S1 ⊔ (S1 ⊓ S2) = S1 := by
  cases S1 <;> cases S2 <;> decide

@[simp]
theorem state_diamond_excluded_middle : ∀ S1 : G3State, (◇S1 ⊔ ¬S1) = .valid := by
  intro S1
  cases S1 <;> decide

@[simp]
theorem state_certainty : ∀ S1 : G3State, □S1 ◃ S1 := by
  intro S1
  cases S1 <;> decide

@[simp]
theorem state_box_idemp : ∀ S1 : G3State, □(□S1) = □S1 := by
intro S1
cases S1 <;> decide

@[simp]
theorem state_box_meet_distrib : ∀ S1 S2 : G3State, □(S1 ⊓ S2) = □S1 ⊓ □S2 := by
  intro S1 S2
  cases S1 <;> cases S2 <;> decide

@[simp]
theorem state_box_pessimist : □(.unknown) = .faulty := by decide

@[simp]
theorem state_possibility_refl : ∀ S1 : G3State, S1 ◃ ◇S1 := by
  intro S1
  cases S1 <;> decide

@[simp]
theorem state_diamond_join_distrib : ∀ S1 S2 : G3State, ◇(S1 ⊔ S2) = ◇S1 ⊔ ◇S2 := by
  intro S1 S2
  cases S1 <;> cases S2 <;> decide

@[simp]
theorem state_diamond_box_dual : ∀ S1 : G3State, ◇S1 = ¬(□(¬S1)) := by
  intro S1
  cases S1 <;> decide

end G3

instance {Component : Type v} (Element : Type u) [System Component Element] : HeytAlg.HeytAlg (Component -> Element -> G3State) where
  le S1 S2 := ∀ c, ∀ e, G3.state_le (S1 c e) (S2 c e)

  top _ _ := .valid
  bot _ _ := .faulty

  meet S1 S2 := fun c e => G3.state_meet (S1 c e) (S2 c e)

  join S1 S2 := fun c e => G3.state_join (S1 c e) (S2 c e)

  implies S1 S2 := fun c e => G3.state_implies (S1 c e) (S2 c e)

  le_refl S1 := by
    intro c e
    cases (S1 c e) <;> simp [G3.state_le]

  le_trans S1 S2 S3 := by
    intro h c e
    cases h1 : S1 c e <;> cases h2 : S2 c e <;> cases h3 : S3 c e
    <;> have H1 := h.1 c e
    <;> have H2 := h.2 c e
    <;> rw [h1, h2] at H1
    <;> rw [h2, h3] at H2
    <;> simp [G3.state_le] at *
    <;> first | assumption | contradiction | constructor

  le_symm S1 S2 := by
    constructor
    · intro h
      funext c e
      cases h1 : S1 c e <;> cases h2 : S2 c e
      <;> have H1 := h.1 c e
      <;> have H2 := h.2 c e
      <;> rw [h1, h2] at H1
      <;> rw [h2, h1] at H2
      <;> simp [G3.state_le] at *
      <;> first | rfl | contradiction
    · intro h
      rw [h]
      constructor <;> intro c e <;> cases (S2 c e) <;> simp [G3.state_le]

  bot_univ := by
    intro S1 c e
    rw [G3.state_le]
    cases S1 c e <;> decide

  top_univ := by
    intro S1 c e
    cases h : S1 c e
    <;> simp [G3.state_le] at *
    <;> decide

  join_comm S1 S2 := by
    funext c e
    apply G3.state_join_comm

  join_idemp S1 := by
    funext c e
    cases S1 c e
    <;> rfl

  join_intro S1 S2 := by
    constructor <;> intro c e <;> cases S1 c e <;> cases S2 c e
    <;> simp [G3.state_le] at *
    <;> decide

  join_univ S1 S2 S3 := by
    constructor
    · intro h
      constructor
      · intro c e; exact (G3.state_join_univ ..).mp (h c e) |>.left
      · intro c e; exact (G3.state_join_univ ..).mp (h c e) |>.right
    · rintro ⟨ h1, h2 ⟩ c e
      apply (G3.state_join_univ ..).mpr
      exact ⟨ h1 c e, h2 c e⟩

  join_bot S1 := by
    funext c e
    exact G3.state_bot_join _

  join_top S1 := by
    funext c e
    exact G3.state_top_join _

  join_assoc S1 S2 S3:= by
    funext
    exact G3.state_join_assoc ..

  meet_comm S1 S2 := by
    funext c e
    apply G3.state_meet_comm

  meet_idemp S1 := by
    funext c e
    cases S1 c e
    <;> rfl

  meet_intro S1 S2 := by
    constructor <;> intro c e <;> cases S1 c e <;> cases S2 c e
    <;> simp [G3.state_le] at *
    <;> decide

  meet_univ S1 S2 S3 := by
    constructor
    · intro ⟨ h1, h2 ⟩ c e
      apply (G3.state_meet_univ ..).mpr
      exact ⟨ h1 c e, h2 c e⟩
    · rintro h
      constructor
      · intro c e; exact (G3.state_meet_univ ..).mp (h c e) |>.left
      · intro c e; exact (G3.state_meet_univ ..).mp (h c e) |>.right

  meet_bot S1 := by
    funext c e
    rw [G3.state_meet_comm]
    exact G3.state_bot_meet _

  meet_top S1 := by
    funext c e
    rw [G3.state_meet_comm]
    exact G3.state_top_meet _

  meet_assoc S1 S2 S3 := by
    funext
    exact G3.state_meet_assoc ..

  implies_univ S1 S2 S3 := by
    constructor
    · intro h c e
      exact (G3.state_implies_univ (S1 c e) (S2 c e) (S3 c e)).mp (h c e)
    . intro h c e
      exact (G3.state_implies_univ (S1 c e) (S2 c e) (S3 c e)).mpr (h c e)

  join_absorb S1 S2:= by
    funext
    exact G3.state_join_absorb ..

  meet_absorb S1 S2 := by
    funext
    exact  G3.state_meet_absorb ..

end
end SystemModel
