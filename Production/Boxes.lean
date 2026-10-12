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
def serialWiring (I X O : Type) : (⟨I, X⟩ ⊗ ⟨X, O⟩ : Box) ⟶ ⟨I, O⟩ where
  in_comp := fun ((x, _), i) => (i, x)
  out_comp := fun (_, o) => o

/-- Machining feeds assembly, with a handoff: when machining shows `blocked`
and assembly shows `idle`, the line releases the finished part itself, unless
the line is signalling a fault. Machining's input now depends on assembly's
output: feedback. -/
def handoffWiring : machiningBox ⊗ assemblyBox ⟶ lineBox where
  in_comp := fun (((m, a), sig) : (Status × Status) × Signal) =>
    (if sig ≠ .fault ∧ m = .blocked ∧ a = .idle then .release else sig, m)
  out_comp := fun (_, a) => a

/-- The handoff never hides a fault: a fault from the line reaches machining,
whatever the two stations show. -/
theorem handoff_keeps_fault (m a : Status) :
    handoffWiring.in_comp ((m, a), .fault) = (.fault, m) := rfl

/-- Apart from that, the handoff only ever replaces the line's signal by
`release`, and only when machining is blocked. -/
theorem handoff_replaces (m a : Status) (sig : Signal) :
    (handoffWiring.in_comp ((m, a), sig)).1 = sig ∨
      ((handoffWiring.in_comp ((m, a), sig)).1 = .release ∧ m = .blocked) := by
  simp only [handoffWiring]
  split <;> simp_all

/-- A blocked station ignores every signal except `fault` and `release`. So
the signal the handoff replaces would have changed nothing. -/
theorem blocked_ignores (d : Nat) (sig : Signal) (hf : sig ≠ .fault) (hr : sig ≠ .release) :
    step ⟨.blocked, d⟩ sig = ⟨.blocked, d⟩ := by
  cases sig <;> simp_all [step]

end Production
