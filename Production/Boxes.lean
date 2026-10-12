import Production.Station

/-!
# Composable production systems, part 2: interfaces and wiring

A station seen from outside is a box: what goes in, what comes out
(`CyberPhy.Box`). A box morphism `f : A ⟶ B` says how the inner box `A` sits
inside the outer box `B`: what `B` shows, read from what `A` shows
(`out_comp`), and what `A` receives, from what `A` shows and what `B` receives
(`in_comp`). The second argument of `in_comp` is feedback.

This module only wires boxes: no machine runs here. Part 3 puts machines in
the boxes (`Production.Wiring`).
-/

namespace Production

open CyberPhy CategoryTheory MonoidalCategory

/-- The machining station from outside: it receives signals and shows its light. -/
def machiningBox : Box := ⟨Signal, Status⟩

/-- The assembly station from outside: it watches machining's light and shows its own. -/
def assemblyBox : Box := ⟨Status, Status⟩

/-- The line of the two stations from outside: signals in, assembly's light out. -/
def lineBox : Box := ⟨Signal, Status⟩

/-- The wiring of a serial connection: the outer input goes to the first box,
the first box's output to the second box's input, and the outer output is the
second box's output. -/
def serialBox (I X O : Type) :
    boxHom (boxTensorProd ⟨I, X⟩ ⟨X, O⟩) ⟨I, O⟩ where
  in_comp := fun ((x, _), i) => (i, x)
  out_comp := fun (_, o) => o

/-- Machining feeds assembly, nothing more: the line's signals go to machining,
machining's light to assembly. -/
def serialLine : machiningBox ⊗ assemblyBox ⟶ lineBox :=
  serialBox Signal Status Status

/-- Machining feeds assembly, with a handoff: when machining shows `blocked`
and assembly shows `idle`, the line releases the finished part itself, in place
of the outer signal of that step. Machining's input now depends on assembly's
output: feedback. -/
def handoffLine : machiningBox ⊗ assemblyBox ⟶ lineBox where
  in_comp := fun (((m, a), sig) : (Status × Status) × Signal) =>
    (if m = .blocked ∧ a = .idle then .release else sig, m)
  out_comp := fun (_, a) => a

/-- The two wirings show the same thing: they differ only in what machining
receives. -/
example : serialLine.out_comp = handoffLine.out_comp := rfl

/-- Without the handoff, a blocked machining station next to an idle assembly
station receives what the line sends; with it, it receives `release`. -/
example : serialLine.in_comp ((.blocked, .idle), .arrive) = (.arrive, .blocked) := rfl
example : handoffLine.in_comp ((.blocked, .idle), .arrive) = (.release, .blocked) := rfl

/-- Wiring composes: the line inside a cell, the cell inside a plant, is the
same nesting whichever way it is grouped (the category laws of `Box`, by `rfl`
in `CyberPhy`). -/
example {A B C D : Box} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h

end Production
