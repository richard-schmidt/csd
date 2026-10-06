import Showcase.CyberPhy

/-!
# Composable production systems, part 1: a station as a Moore machine

A machining station on a production line, written as one of csd's Moore
machines (`CyberPhy.MooreMachine`: a state, and a lens whose `view` is what the
station shows and whose `update` is how an input changes the state).

`run` feeds a list of inputs to a machine and lists what it shows. The timing
convention, used by the whole series: the output depends only on the current
state, so `run` shows the start state first and then one output per input
(n inputs, n + 1 outputs).
-/

namespace Production

open Optics CyberPhy

/-- The light on the station. -/
inductive Status where
  | idle
  | processing
  | blocked   -- a finished part is waiting for the next station to take it
  | failed
  deriving Repr, DecidableEq

/-- What the line tells the station. -/
inductive Signal where
  | arrive    -- a raw part is put on the station
  | finish    -- the machining cycle ends
  | release   -- the next station takes the finished part
  | fault     -- the station breaks down
  | repair    -- maintenance puts it back in service
  deriving Repr, DecidableEq

/-- Inside the station: its status, and how many parts it has handed on. The
counter is internal: the light does not show it. -/
structure Machining where
  status : Status
  done : Nat
  deriving Repr

/-- One step. An input the current status has no use for changes nothing. -/
def step (s : Machining) : Signal → Machining
  | .fault => { s with status := .failed }
  | .repair => if s.status = .failed then { s with status := .idle } else s
  | .arrive => if s.status = .idle then { s with status := .processing } else s
  | .finish => if s.status = .processing then { s with status := .blocked } else s
  | .release =>
      if s.status = .blocked then { status := .idle, done := s.done + 1 } else s

/-- The machining station as a Moore machine: it shows its status only. -/
def machining : MooreMachine where
  α := Signal
  β := Status
  state := Machining
  lens := { view := Machining.status, update := step }

/-- What a machine shows while it is fed `inputs` from state `s`: the view of
`s`, then the view after each input. -/
def run (M : MooreMachine) (s : M.state) : List M.α → List M.β
  | [] => [M.lens.view s]
  | a :: as => M.lens.view s :: run M (M.lens.update s a) as

/-- The state after all the inputs. -/
def final (M : MooreMachine) (s : M.state) (inputs : List M.α) : M.state :=
  inputs.foldl M.lens.update s

/-- n inputs, n + 1 outputs. -/
theorem run_length (M : MooreMachine) (s : M.state) (inputs : List M.α) :
    (run M s inputs).length = inputs.length + 1 := by
  induction inputs generalizing s with
  | nil => rfl
  | cons a as ih => simp [run, ih]

/-- The first output is what the start state shows. -/
theorem run_head (M : MooreMachine) (s : M.state) (inputs : List M.α) :
    (run M s inputs).head? = some (M.lens.view s) := by
  cases inputs <;> rfl

/-- The last output is what the final state shows. -/
theorem run_getLast (M : MooreMachine) (s : M.state) (inputs : List M.α) :
    (run M s inputs).getLast? = some (M.lens.view (final M s inputs)) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      simp only [run] at ih ⊢
      rw [List.getLast?_cons_cons]
      exact ih (M.lens.update s a)

/-- One shift on the station: a part, a breakdown, a repair, the next part. -/
def shift : List Signal :=
  [.arrive, .finish, .release, .arrive, .fault, .finish, .repair, .arrive]

def start : Machining := { status := .idle, done := 0 }

/-- What the station shows during the shift. `finish` while failed is
ignored: the part in it is lost with the breakdown. -/
example : run machining start shift =
    [.idle, .processing, .blocked, .idle, .processing, .failed, .failed, .idle, .processing] := by
  rfl

/-- After the shift, one part was handed on. -/
example : (final machining start shift).done = 1 := by rfl

/-- A failed station shows `failed` until it is repaired, whatever else
happens. -/
theorem failed_until_repair (s : Machining) (h : s.status = .failed)
    (inputs : List Signal) (hr : Signal.repair ∉ inputs) :
    ∀ o ∈ run machining s inputs, o = .failed := by
  induction inputs generalizing s with
  | nil =>
    intro o ho
    simp only [run, List.mem_singleton] at ho
    subst ho
    exact h
  | cons a as ih =>
    intro o ho
    simp only [List.mem_cons, not_or] at hr
    have hs : (step s a).status = .failed := by
      cases a <;> simp [step, h] at hr ⊢
    simp only [run, List.mem_cons] at ho
    rcases ho with ho | ho
    · subst ho
      exact h
    · exact ih (step s a) hs hr.2 o ho

end Production
