import DDD.ContextMap
import Showcase.ContextMapNotifications

/-!
# Events along the category of contexts

`Showcase/ContextMapNotifications.lean` types services by domain: a computation in
a domain returns events, each from that domain or from a domain upstream of it
(`Svc`). Here the same discipline is stated for the contexts of a context map,
with the routes of `J` in place of the arrows between domains.

- `CSvc M c α`: a computation in the context `c`. Each event it returns carries
  the context it comes from, and there is a route of `J` from that context to
  `c`: an event of a context reaches only the contexts downstream of it.
- `CSvc.emit` tags an event with the context it runs in (the identity route);
  `CSvc.callAlong` calls an endpoint of an upstream context along a morphism of
  `J`, and extends the routes of the callee's events by it. `CSvc.call` calls
  along an arrow of the map.
- A `Projection` sends contexts to the domains of the Showcase map and routes of
  `J` to arrivals of events (`Reaches`), as `toDomains` does for the example map.
  `CSvc.toSvc` turns a computation in a context into a computation in its
  domain; it commutes with `pure`, `bind` and `emit`. When the projection gives
  no arrival from the domain of `u` to that of `d`, there is no route from `u`
  to `d` (`Projection.isEmpty_hom`).
-/

namespace DDD

open CategoryTheory
open ContextMapNotifications (Domain Level Event Svc Reaches)

variable {C : Type} [Quiver C] (M : ContextMap C)

/-- An event, tagged with the context it comes from. -/
structure CEvent (C : Type) where
  context : C
  label : String
  level : Level
  payload : String

/-- A computation in the context `c`: a value, the events it caused in the order
they happened, and for each event a route of `J` from its context to `c`. -/
def CSvc (c : C) (α : Type) : Type :=
  { r : α × List (CEvent C) // ∀ e ∈ r.2, Nonempty (M.ctx e.context ⟶ M.ctx c) }

namespace CSvc

variable {M} {c : C}

def run {α : Type} (s : CSvc M c α) : α × List (CEvent C) := s.val

protected def pure {α : Type} (a : α) : CSvc M c α := ⟨(a, []), by simp⟩

/-- Sequencing: the events of the first step, then those of the second. -/
protected def bind {α β : Type} (s : CSvc M c α) (f : α → CSvc M c β) : CSvc M c β :=
  ⟨((f s.val.1).val.1, s.val.2 ++ (f s.val.1).val.2), by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact s.property e h
    · exact (f s.val.1).property e h⟩

instance : Monad (CSvc M c) where
  pure := CSvc.pure
  bind := CSvc.bind

theorem ext {α : Type} {s t : CSvc M c α} (h : s.run = t.run) : s = t := Subtype.ext h

instance : LawfulMonad (CSvc M c) := LawfulMonad.mk'
  (id_map := fun s => ext (by
    change (s.val.1, s.val.2 ++ []) = s.val
    simp))
  (pure_bind := fun a f => ext (by
    change ((f a).val.1, [] ++ (f a).val.2) = (f a).val
    simp))
  (bind_assoc := fun s f g => ext (by
    change ((g (f s.val.1).val.1).val.1,
        (s.val.2 ++ (f s.val.1).val.2) ++ (g (f s.val.1).val.1).val.2) =
      ((g (f s.val.1).val.1).val.1,
        s.val.2 ++ ((f s.val.1).val.2 ++ (g (f s.val.1).val.1).val.2))
    simp))

/-- Each event a computation in `c` returns comes from a context with a route to
`c`. -/
theorem routes {α : Type} (s : CSvc M c α) :
    ∀ e ∈ s.run.2, Nonempty (M.ctx e.context ⟶ M.ctx c) :=
  s.property

/-- Emit an event in `c`: it is tagged with `c`, along the identity route. -/
def emit (label : String) (level : Level) (payload : String) : CSvc M c Unit :=
  ⟨((), [⟨c, label, level, payload⟩]), by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨𝟙 _⟩⟩

end CSvc

/-- An endpoint of the context `u`. -/
structure CEndpoint (u : C) (α β : Type) where
  handle : α → CSvc M u β

namespace CSvc

variable {M}

/-- Call an endpoint of `u` from `c` along a morphism of `J` from `u` to `c`. The
callee's events come back to the caller in order, their routes followed by the
morphism. -/
def callAlong {u c : C} {α β : Type} (φ : M.ctx u ⟶ M.ctx c) (e : CEndpoint M u α β) (a : α) :
    CSvc M c β :=
  ⟨(e.handle a).val, fun ev hev =>
    let ⟨ψ⟩ := (e.handle a).property ev hev
    ⟨ψ ≫ φ⟩⟩

/-- Call an endpoint of `u` from `c` along an arrow of the context map. -/
def call {u c : C} {α β : Type} (f : u ⟶ c) (e : CEndpoint M u α β) (a : α) : CSvc M c β :=
  callAlong (M.arrow f) e a

end CSvc

/-- A projection of the category of contexts onto the Showcase map: a domain for
each context, and for each route of `J` the arrival of events from the domain of
its source in the domain of its target. -/
structure Projection where
  domain : C → Domain
  reaches : ∀ {u d : C}, (M.ctx u ⟶ M.ctx d) → Reaches (domain u) (domain d)

variable {M}

/-- The event of the Showcase map for an event of a context: tagged with the domain
of its context. -/
def CEvent.toEvent (P : Projection M) (e : CEvent C) : Event :=
  ⟨P.domain e.context, e.label, e.level, e.payload⟩

namespace CSvc

variable (P : Projection M) {c : C}

/-- A computation in a context, as a computation in its domain. -/
def toSvc {α : Type} (s : CSvc M c α) : Svc (P.domain c) α :=
  ⟨(s.val.1, s.val.2.map (CEvent.toEvent P)), by
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    obtain ⟨φ⟩ := s.property e' he'
    exact P.reaches φ⟩

theorem toSvc_run {α : Type} (s : CSvc M c α) :
    (s.toSvc P).run = (s.run.1, s.run.2.map (CEvent.toEvent P)) := rfl

theorem toSvc_pure {α : Type} (a : α) :
    (pure a : CSvc M c α).toSvc P = (pure a : Svc (P.domain c) α) :=
  ContextMapNotifications.Svc.ext rfl

theorem toSvc_bind {α β : Type} (s : CSvc M c α) (f : α → CSvc M c β) :
    (s >>= f).toSvc P = s.toSvc P >>= fun a => (f a).toSvc P :=
  ContextMapNotifications.Svc.ext (by
    change ((f s.val.1).val.1, (s.val.2 ++ (f s.val.1).val.2).map (CEvent.toEvent P)) =
      ((f s.val.1).val.1, s.val.2.map (CEvent.toEvent P) ++
        (f s.val.1).val.2.map (CEvent.toEvent P))
    rw [List.map_append])

theorem toSvc_emit (label : String) (level : Level) (payload : String) :
    (emit (M := M) (c := c) label level payload).toSvc P =
      ContextMapNotifications.emit label level payload :=
  ContextMapNotifications.Svc.ext rfl

end CSvc

/-- Without an arrival from the domain of `u` in that of `d`, there is no route
from `u` to `d`: no event of `u` reaches `d`. -/
theorem Projection.isEmpty_hom (P : Projection M) {u d : C}
    (h : ¬ Reaches (P.domain u) (P.domain d)) : IsEmpty (M.ctx u ⟶ M.ctx d) :=
  ⟨fun φ => h (P.reaches φ)⟩

end DDD
