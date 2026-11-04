import DDD.Data
import DDD.VStates

/-!
# Finite states with conversions

A finite state of `S` with values in an interpretation `I` (`FinState I.K`)
extends to a state with conversions (`Schema.State.vext`). `FinState.evalV`
follows a path of `S.vcat L`: generators through the columns of the state,
conversions through `I`. `FinState.evalV_vmor`: following the names of a path is
applying the state with conversions to the path.
-/

namespace DDD

open CategoryTheory Schema

namespace FinState

variable {L : TypeList} (I : Interp L) {S : Schema} (X : FinState I.K)

/-- One step along a generator of `S`, through the columns, or along a conversion,
through `I`. -/
def vstep (S : Schema) : Elem I.K → String → Option (Elem I.K)
  | .ent e i, n => X.step S (.ent e i) n
  | .val v k, n =>
    match h : L.conv? v n with
    | some w => some (.val w (I.F.map (L.convMor n h) k))
    | none => none

/-- Following a list of names of generators and conversions. -/
def evalV (S : Schema) : Elem I.K → List String → Option (Elem I.K)
  | x, [] => some x
  | x, n :: ns => (X.vstep I S x n).bind fun y => evalV S y ns

theorem evalV_append (x : Elem I.K) (l m : List String) :
    X.evalV I S x (l ++ m) = (X.evalV I S x l).bind fun y => X.evalV I S y m := by
  induction l generalizing x with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.cons_append, evalV]
    cases X.vstep I S x n with
    | none => rfl
    | some y => exact ih y

theorem evalV_singleton (x : Elem I.K) (n : String) : X.evalV I S x [n] = X.vstep I S x n := by
  simp only [evalV]
  cases X.vstep I S x n <;> rfl

variable [∀ v, DecidableEq (I.K v)]

/-- Applying the state with conversions of `X` to the morphism of a path is following
its names through the columns of `X` and the conversions of `I`. -/
theorem evalV_vmor (hS : S.WellFormed) (hX : X.check S = true) {a b : S.VObj L}
    (p : Quiver.Path a b) (x : X.Carrier ⟨a.1, a.2⟩) :
    X.evalV I S x.1 (vnames p) =
      some (((X.toState hX).vext I hS).F.map (vmor p) x : X.Carrier ⟨b.1, b.2⟩).1 := by
  induction p with
  | nil =>
    change some x.1 = some (((X.toState hX).vext I hS).F.map (𝟙 _) x : X.Carrier _).1
    rw [CategoryTheory.Functor.map_id]
    rfl
  | cons p e ih =>
    rename_i c d
    rw [vnames_cons, evalV_append, ih, Option.bind_some, evalV_singleton, vmor_cons,
      CategoryTheory.Functor.map_comp, types_comp_apply]
    generalize (((X.toState hX).vext I hS).F.map (vmor p) x : X.Carrier ⟨c.1, c.2⟩) = y
    obtain ⟨⟨e₀⟩ | ⟨v⟩, hc⟩ := c
    · obtain ⟨_ | _, hy⟩ := y
      · exact step_stepIn hX (show S.step? (.entity e₀) e.1 = some d.1 from e.2) ⟨_, hy⟩
      · exact absurd (show X.Has _ (.entity e₀) from hy) (by simp [Has])
    · obtain ⟨⟨_⟩ | ⟨w⟩, hd⟩ := d
      · exact absurd e.2 not_vstep?_value_entity
      obtain ⟨_ | ⟨v', k⟩, hy⟩ := y
      · exact absurd (show X.Has _ (.value v) from hy) (by simp [Has])
      have hv : v' = v := hy
      subst hv
      have hc' := conv?_of_vstep? e.2
      change (match h : L.conv? v' e.1 with
        | some w => some (Elem.val w (I.F.map (L.convMor e.1 h) k))
        | none => none) = _
      split
      · rename_i w' h'
        obtain rfl : w' = w := Option.some.inj (h'.symm.trans hc')
        rfl
      · rename_i h'
        exact absurd (h'.symm.trans hc') (by simp)

end FinState

end DDD
