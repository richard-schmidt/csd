import DDD.Open
import DDD.Data
import Production.Wiring

/-!
# Machines on open schemas

A machine on an open schema `X : I → O` (`OpenMachine`) is a machine of
`Production/Wiring.lean` whose state is a finite state of the schema of `X` that
passes the check (`CheckedState`), so that `FinState.toState` sends it to an
attributed state. It reads checked states of `I` and shows the restriction of
its state to `O`. Machines live in `Type`; attributed states live in `Type 1`,
which is why the state is a finite one.

- The interface of a machine on `X` is the box of checked states of `I` in and
  of `O` out (`OpenSchema.box`). For `X : I → M` and `Y : M → O`, the serial
  wiring of `Production` takes the boxes of `X` and `Y` to the box of their
  composite: `OpenMachine.comp` is a machine on the box of `X ∘ Y`.
- One step of the composite: the machine on `X` takes the input, the machine on
  `Y` takes what the machine on `X` showed before the step (`comp_update`). The
  data `X` publishes on `M` reaches `Y` one step late.
- A checked state of the glued schema splits into a state of `X` and one of `Y`
  (`OpenSchema.split`). The two agree on `M` up to isomorphism of attributed
  states (`split_agree`), and the composite machine started from the split shows
  what the glued state shows on `O` (`comp_view_split`) and reads what it reads
  on `I` (`split_toI`). Restricting twice along inclusions is restricting once
  (`CheckedState.restrictRestrictIso`).
- Serial composition is associative up to relabelling the states
  (`serialAssoc`), as composition of open schemas is associative up to an
  isomorphism of schema categories.
-/

namespace DDD

open CategoryTheory Production CyberPhy Optics

variable (K : ValueType → Type) [∀ v, DecidableEq (K v)]

/-- The finite states that pass the check for `S`. -/
def CheckedState (S : Schema) : Type := { X : FinState K // X.check S = true }

variable {K}

namespace Translation

omit [∀ v, DecidableEq (K v)] in
/-- Restriction along composite inclusions: restricting along `A ⊆ B`, then along
`B ⊆ C`, is restricting along `A ⊆ C`. -/
theorem restrictState_empty_comp {A B C : Schema} (hB : B.WellFormed) (hC : C.WellFormed)
    (h₁ : ({} : Translation).Valid A B) (h₂ : ({} : Translation).Valid B C)
    (h₃ : ({} : Translation).Valid A C) (Y : C.State K) :
    restrictState hB h₁ (restrictState hC h₂ Y) = restrictState hC h₃ Y := by
  refine Schema.State.ext' ?_ fun _ _ => rfl
  change functor hB h₁ ⋙ functor hC h₂ ⋙ Y.F = functor hC h₃ ⋙ Y.F
  rw [← Functor.assoc, functor_empty_comp_empty hB hC h₁ h₂ h₃]

end Translation

namespace CheckedState

variable {S A B C : Schema}

/-- The attributed state of a checked state. -/
def toState (x : CheckedState K S) : S.State K := x.1.toState x.2

/-- Restriction along an inclusion. -/
def restrict (hA : A.WellFormed) (h : ({} : Translation).Valid A B) (x : CheckedState K B) :
    CheckedState K A :=
  ⟨x.1.restrict {} A B, FinState.restrict_check hA x.2 h⟩

/-- The state of a restriction is the restriction of the state, up to
isomorphism. -/
noncomputable def restrictIso (hA : A.WellFormed) (hB : B.WellFormed)
    (h : ({} : Translation).Valid A B) (x : CheckedState K B) :
    (x.restrict hA h).toState ≅ Translation.restrictState hB h x.toState :=
  FinState.restrictIso hA hB x.2 h

/-- Restricting twice along inclusions is restricting along the composite
inclusion, up to isomorphism of attributed states. -/
noncomputable def restrictRestrictIso (hA : A.WellFormed) (hB : B.WellFormed)
    (hC : C.WellFormed) (h₁ : ({} : Translation).Valid A B) (h₂ : ({} : Translation).Valid B C)
    (h₃ : ({} : Translation).Valid A C) (x : CheckedState K C) :
    ((x.restrict hB h₂).restrict hA h₁).toState ≅ (x.restrict hA h₃).toState :=
  (restrictIso hA hB h₁ _).trans <|
    ((Translation.restrictStateFunctor hB h₁).mapIso (restrictIso hB hC h₂ x)).trans <|
      (eqToIso (Translation.restrictState_empty_comp hB hC h₁ h₂ h₃ x.toState)).trans
        (restrictIso hA hC h₃ x).symm

end CheckedState

namespace OpenSchema

variable {I M O : Schema}

variable (K) in
/-- The interface of a machine on an open schema from `I` to `O`: checked states of
`I` in, checked states of `O` out. -/
abbrev box (_ : OpenSchema I O) : Box := ⟨CheckedState K I, CheckedState K O⟩

section

variable (X : OpenSchema I O)

/-- The restriction of a state of `X` to its input interface. -/
def toI (x : CheckedState K X.S) : CheckedState K I := x.restrict X.wfI X.inI

/-- The restriction of a state of `X` to its output interface. -/
def toO (x : CheckedState K X.S) : CheckedState K O := x.restrict X.wfO X.inO

end

/-- A state of the composite `X ∘ Y`, split into a state of `X` and a state of `Y`. -/
def split (X : OpenSchema I M) (Y : OpenSchema M O) (h : Composable X Y)
    (g : CheckedState K (X.comp Y h).S) : CheckedState K X.S × CheckedState K Y.S :=
  (g.restrict X.wf (X.gluing Y h).inl_valid, g.restrict Y.wf (X.gluing Y h).inr_valid)

variable (X : OpenSchema I M) (Y : OpenSchema M O) (h : Composable X Y)

/-- The inclusion of `M` in the composite. -/
theorem kernel_valid : ({} : Translation).Valid M (X.comp Y h).S :=
  Translation.empty_valid_trans X.wfO h.wf X.inO (X.gluing Y h).inl_valid

/-- The two parts of a split state agree on `M`: their restrictions to `M` are
isomorphic, both to the restriction of the glued state. -/
noncomputable def split_agree (g : CheckedState K (X.comp Y h).S) :
    (X.toO (X.split Y h g).1).toState ≅ (Y.toI (X.split Y h g).2).toState :=
  (CheckedState.restrictRestrictIso X.wfO X.wf h.wf X.inO (X.gluing Y h).inl_valid
      (kernel_valid X Y h) g).trans
    (CheckedState.restrictRestrictIso Y.wfI Y.wf h.wf Y.inI (X.gluing Y h).inr_valid
      (kernel_valid X Y h) g).symm

/-- The part of a split state in `X`, restricted to `I`, is the glued state
restricted to `I`, up to isomorphism. -/
noncomputable def split_toI (g : CheckedState K (X.comp Y h).S) :
    (X.toI (X.split Y h g).1).toState ≅ ((X.comp Y h).toI g).toState :=
  CheckedState.restrictRestrictIso X.wfI X.wf h.wf X.inI (X.gluing Y h).inl_valid
    (X.comp Y h).inI g

end OpenSchema

/-- A machine on an open schema `X : I → O`: a state of the schema of `X`, updated
by checked states of `I`. -/
structure OpenMachine (K : ValueType → Type) [∀ v, DecidableEq (K v)] {I O : Schema}
    (X : OpenSchema I O) where
  update : CheckedState K X.S → CheckedState K I → CheckedState K X.S

namespace OpenMachine

variable {I M N O : Schema} {X : OpenSchema I M} {Y : OpenSchema M O}

/-- The machine of `Production`: it shows the restriction of its state to the
output interface. -/
def toMachine (A : OpenMachine K X) : Machine (X.box K) where
  state := CheckedState K X.S
  lens := { view := X.toO, update := A.update }

/-- The composite of machines on `X` and on `Y`: serial wiring, on the box of
`X ∘ Y`. -/
def comp (A : OpenMachine K X) (B : OpenMachine K Y) (h : X.Composable Y) :
    Machine ((X.comp Y h).box K) :=
  A.toMachine ≫ₛ B.toMachine

variable (A : OpenMachine K X) (B : OpenMachine K Y) (h : X.Composable Y)

/-- The composite shows what the machine on `Y` shows. -/
theorem comp_view (s : CheckedState K X.S) (t : CheckedState K Y.S) :
    (A.comp B h).lens.view (s, t) = Y.toO t := rfl

/-- One step of the composite: the machine on `X` takes the input, the machine on
`Y` takes what the machine on `X` showed before the step. -/
theorem comp_update (s : CheckedState K X.S) (t : CheckedState K Y.S) (i : CheckedState K I) :
    (A.comp B h).lens.update (s, t) i = (A.update s i, B.update t (X.toO s)) := rfl

/-- Running the composite is running the machine on `X`, then the machine on `Y`
on what it showed, one step late (`Production.run_serial`). -/
theorem comp_run (s : CheckedState K X.S) (t : CheckedState K Y.S)
    (inputs : List (CheckedState K I)) :
    (A.comp B h).run (s, t) inputs = B.toMachine.run t (A.toMachine.run s inputs).dropLast :=
  run_serial A.toMachine B.toMachine s t inputs

/-- Started from a split state of the glued schema, the composite shows what the
glued state shows on `O`, up to isomorphism. -/
noncomputable def comp_view_split (g : CheckedState K (X.comp Y h).S) :
    ((A.comp B h).lens.view (X.split Y h g)).toState ≅ ((X.comp Y h).toO g).toState :=
  CheckedState.restrictRestrictIso Y.wfO Y.wf h.wf Y.inO (X.gluing Y h).inr_valid
    (X.comp Y h).inO g

end OpenMachine

namespace FinState

/-- `s` with the entities and generators of `M` taken from `m`: lookups find the
entries of `m` first. -/
def overwrite (M : Schema) (s m : FinState K) : FinState K where
  sizes := M.entities.map (fun e => (e, m.size e)) ++ s.sizes
  refs := M.refs.map (fun r => ((r.src, r.name), (m.refCol r.src r.name).getD [])) ++ s.refs
  attrs := M.attrs.map (fun a => ((a.src, a.name), (m.attrCol a.src a.name).getD [])) ++ s.attrs

end FinState

namespace OpenMachine

variable {I O : Schema}

/-- The conformist machine on `X`: it takes the data of its input interface into
its state, and keeps its state when the result fails the check. -/
def conformist (X : OpenSchema I O) : OpenMachine K X where
  update s m := if h : (s.1.overwrite I m.1).check X.S = true then ⟨_, h⟩ else s

theorem conformist_update_of_check (X : OpenSchema I O) (s : CheckedState K X.S)
    (m : CheckedState K I) (h : (s.1.overwrite I m.1).check X.S = true) :
    (conformist X).update s m = ⟨_, h⟩ := dif_pos h

/-- An update that would break the invariants of the schema is refused. -/
theorem conformist_update_of_not_check (X : OpenSchema I O) (s : CheckedState K X.S)
    (m : CheckedState K I) (h : ¬ (s.1.overwrite I m.1).check X.S = true) :
    (conformist X).update s m = s := dif_neg h

end OpenMachine

/-- Serial composition is associative up to relabelling the states. -/
def serialAssoc {I X Y O : Type} (M₁ : Machine ⟨I, X⟩) (M₂ : Machine ⟨X, Y⟩)
    (M₃ : Machine ⟨Y, O⟩) : Machine.Iso ((M₁ ≫ₛ M₂) ≫ₛ M₃) (M₁ ≫ₛ (M₂ ≫ₛ M₃)) where
  equiv := Equiv.prodAssoc _ _ _
  view _ := rfl
  update _ _ := rfl

end DDD
