import Production.Boxes

/-!
# Composable production systems, part 3: composing machines by wiring

A machine with a given interface (a `Box`) is a state type and a lens from the
state to the box's outputs and inputs. A box morphism `f : A ⟶ B` says how an
inner box sits inside an outer one; `wire f` turns a machine with interface `A`
into a machine with interface `B`, with the same state. Wiring is lens
composition: a box morphism is itself a lens.

- `Machines : Box ⥤ Type 1`: wiring along the identity changes nothing, and
  wiring along `f ≫ g` is wiring along `f`, then `g`. Both by `rfl`.
- `serial M N`: `M` feeds `N`. It is not a new primitive: it is `M` and `N`
  side by side, wired into one box.
- `run_serial`: running the composite is running `M`, then running `N` on what
  `M` showed, one step late.
- Side by side (`par`) respects the monoidal structure of `Box` up to a
  relabelling of the states (`Machine.Iso`), not as an equation: the two
  groupings of three machines have the state types `(S₁ × S₂) × S₃` and
  `S₁ × (S₂ × S₃)`, which are isomorphic but not equal.
-/

namespace Production

open Optics CyberPhy CategoryTheory MonoidalCategory

/-- A machine with interface `B`: a state, what the state shows (`view`), and
how an input changes it (`update`). -/
structure Machine (B : Box) where
  state : Type
  lens : Lens state state B.σₒ B.σᵢ

/-- A box morphism read as a lens: outer outputs from inner outputs, inner
inputs from inner outputs and outer inputs. -/
def boxLens {A B : Box} (f : boxHom A B) : Lens A.σₒ A.σᵢ B.σₒ B.σᵢ where
  view := f.out_comp
  update o b := f.in_comp (o, b)

/-- Put a machine with interface `A` inside the outer box `B`. -/
def wire {A B : Box} (f : A ⟶ B) (M : Machine A) : Machine B where
  state := M.state
  lens := Lens.compose M.lens (boxLens f)

theorem wire_view {A B : Box} (f : A ⟶ B) (M : Machine A) (s : M.state) :
    (wire f M).lens.view s = f.out_comp (M.lens.view s) := rfl

theorem wire_update {A B : Box} (f : A ⟶ B) (M : Machine A) (s : M.state) (b : B.σᵢ) :
    (wire f M).lens.update s b = M.lens.update s (f.in_comp (M.lens.view s, b)) := rfl

/-- Machines and wiring form a functor from boxes to types: the laws hold by
definition. -/
def Machines : Box ⥤ Type 1 where
  obj := Machine
  map f := wire f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The same machine as one of csd's bundled Moore machines. -/
def Machine.toMoore {B : Box} (M : Machine B) : MooreMachine where
  α := B.σᵢ
  β := B.σₒ
  state := M.state
  lens := M.lens

/-- A csd Moore machine as a machine with its interface as a box. -/
def Machine.ofMoore (M : MooreMachine) : Machine ⟨M.α, M.β⟩ where
  state := M.state
  lens := M.lens

/-- What a machine shows while it is fed `inputs` (part 1's `run`). -/
def Machine.run {B : Box} (M : Machine B) (s : M.state) (inputs : List B.σᵢ) : List B.σₒ :=
  Production.run M.toMoore s inputs

/-- The state after all the inputs (part 1's `final`). -/
def Machine.final {B : Box} (M : Machine B) (s : M.state) (inputs : List B.σᵢ) : M.state :=
  Production.final M.toMoore s inputs

/-- Two machines side by side: pairs of states, inputs and outputs. -/
def Machine.par {A B : Box} (M : Machine A) (N : Machine B) : Machine (A ⊗ B) where
  state := M.state × N.state
  lens := Lens.prod M.lens N.lens

/-- The empty machine: nothing in, nothing out, nothing inside. -/
def Machine.unit : Machine boxUnit where
  state := Unit
  lens := { view := fun _ => (), update := fun _ _ => () }

/-! ## Serial composition -/

/-- `M` feeds `N`: both side by side, wired along `serialWiring` (part 2). -/
def serial {I X O : Type} (M : Machine ⟨I, X⟩) (N : Machine ⟨X, O⟩) :
    Machine ⟨I, O⟩ :=
  wire (serialWiring I X O) (M.par N)

infixr:70 " ≫ₛ " => serial

/-- One step of the composite: `M` takes the outer input, `N` takes what `M`
showed before the step. -/
theorem serial_update {I X O : Type} (M : Machine ⟨I, X⟩) (N : Machine ⟨X, O⟩)
    (m : M.state) (n : N.state) (i : I) :
    (M ≫ₛ N).lens.update (m, n) i = (M.lens.update m i, N.lens.update n (M.lens.view m)) :=
  rfl

/-- The composite shows what `N` shows. -/
theorem serial_view {I X O : Type} (M : Machine ⟨I, X⟩) (N : Machine ⟨X, O⟩)
    (m : M.state) (n : N.state) :
    (M ≫ₛ N).lens.view (m, n) = N.lens.view n :=
  rfl

/-- Running the composite is running `M`, then running `N` on what `M` showed,
one step late: `N` never sees `M`'s last output. -/
theorem run_serial {I X O : Type} (M : Machine ⟨I, X⟩) (N : Machine ⟨X, O⟩)
    (m : M.state) (n : N.state) (inputs : List I) :
    (M ≫ₛ N).run (m, n) inputs = N.run n (M.run m inputs).dropLast := by
  induction inputs generalizing m n with
  | nil => rfl
  | cons i is ih =>
    have hne : M.run (M.lens.update m i) is ≠ [] := by
      cases is <;> simp [Machine.run, run]
    change N.lens.view n :: (M ≫ₛ N).run (M.lens.update m i, N.lens.update n (M.lens.view m)) is
      = N.run n (M.lens.view m :: M.run (M.lens.update m i) is).dropLast
    rw [ih, List.dropLast_cons_of_ne_nil hne]
    rfl

/-! ## Side by side, up to relabelling the states -/

/-- Two machines with the same interface that differ only in how their states
are labelled: a bijection of states that commutes with `view` and `update`. -/
structure Machine.Iso {B : Box} (M N : Machine B) where
  equiv : M.state ≃ N.state
  view : ∀ s, N.lens.view (equiv s) = M.lens.view s
  update : ∀ s b, equiv (M.lens.update s b) = N.lens.update (equiv s) b

/-- Isomorphic machines show the same thing on every run. -/
theorem Machine.Iso.run {B : Box} {M N : Machine B} (e : Machine.Iso M N)
    (s : M.state) (inputs : List B.σᵢ) : N.run (e.equiv s) inputs = M.run s inputs := by
  induction inputs generalizing s <;>
    simp_all [Machine.run, Production.run, Machine.toMoore, e.view, ← e.update]

/-- Wiring two machines side by side along `f ⊗ g` is wiring each one, then
putting them side by side: an equation, the states are the same. -/
theorem wire_tensor {A B C D : Box} (f : A ⟶ B) (g : C ⟶ D) (M : Machine A) (N : Machine C) :
    wire (f ⊗ₘ g) (M.par N) = (wire f M).par (wire g N) :=
  rfl

/-- Grouping three machines one way or the other gives the same machine, up to
relabelling the states. -/
def Machine.parAssoc {A B C : Box} (M : Machine A) (N : Machine B) (P : Machine C) :
    Machine.Iso (wire (α_ A B C).hom ((M.par N).par P)) (M.par (N.par P)) where
  equiv := Equiv.prodAssoc _ _ _
  view _ := rfl
  update _ _ := rfl

/-- The empty machine on the left changes nothing, up to relabelling. -/
def Machine.parUnitLeft {A : Box} (M : Machine A) :
    Machine.Iso (wire (λ_ A).hom (Machine.unit.par M)) M where
  equiv := Equiv.punitProd _
  view _ := rfl
  update _ _ := rfl

/-- The empty machine on the right changes nothing, up to relabelling. -/
def Machine.parUnitRight {A : Box} (M : Machine A) :
    Machine.Iso (wire (ρ_ A).hom (M.par Machine.unit)) M where
  equiv := Equiv.prodPUnit _
  view _ := rfl
  update _ _ := rfl

/-! ## Machining feeds assembly -/

/-- Inside the assembly station: the last light it saw on machining, its own
status (`idle` or `processing`), and how many products it has finished. -/
structure Assembly where
  seen : Status
  status : Status
  done : Nat
  deriving Repr

/-- One step of assembly. A product in progress is finished (assembling takes
one step). A part has come when machining's light goes from `blocked` to
`idle` (machining handed it on); then assembly starts on it. -/
def assemblyStep (s : Assembly) (upstream : Status) : Assembly :=
  let arrived := s.seen = .blocked ∧ upstream = .idle
  { seen := upstream
    status := if arrived then .processing else .idle
    done := if s.status = .processing then s.done + 1 else s.done }

/-- The assembly station: it reads a `Status` and shows a `Status`. -/
def assembly : Machine ⟨Status, Status⟩ where
  state := Assembly
  lens := { view := Assembly.status, update := assemblyStep }

def assemblyStart : Assembly := { seen := .idle, status := .idle, done := 0 }

/-- The two stations in series: nobody releases machining's part but the line. -/
def serialLine : Machine lineBox := Machine.ofMoore machining ≫ₛ assembly

/-- The two stations with part 2's handoff: the line releases machining's part
when assembly is idle. -/
def handoffLine : Machine lineBox := wire handoffWiring ((Machine.ofMoore machining).par assembly)

/-- An operator who loads machining whenever they can. Nobody sends `release`. -/
def loading : List Signal := [.arrive, .finish, .arrive, .arrive, .finish, .arrive, .arrive]

/-- In series only, the line stops at the first finished part: machining stays
blocked and assembly never works. -/
example : serialLine.run (start, assemblyStart) loading =
    [.idle, .idle, .idle, .idle, .idle, .idle, .idle, .idle] := by
  rfl

example : (serialLine.final (start, assemblyStart) loading).1.status = .blocked := by
  rfl

/-- With the handoff, the parts flow, and assembly starts one step after
machining hands a part on (steps 3 and 6). -/
example : handoffLine.run (start, assemblyStart) loading =
    [.idle, .idle, .idle, .idle, .processing, .idle, .idle, .processing] := by
  rfl

/-- Two parts handed on by machining, one product finished, the second in
assembly. -/
example : (handoffLine.final (start, assemblyStart) loading).1.done = 2 := by
  rfl

example : (handoffLine.final (start, assemblyStart) loading).2.done = 1 := by
  rfl

end Production
