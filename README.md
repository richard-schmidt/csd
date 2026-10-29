# Categorical System Design

[![Lean Action CI](https://github.com/richard-schmidt/csd/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/richard-schmidt/csd/actions/workflows/lean_action_ci.yml)

Formal models of software and system architecture in **Lean 4 + Mathlib**.

Architects describe systems with diagrams and prose: bounded contexts, components, dependencies, message flows, notification schemes. This repository states those notions as mathematical objects (categories, lenses, lattices, monoidal structures), so that properties such as composability, coherence and fault propagation become statements that Lean checks.

The repository is organised as a research notebook: a small **showcase** of finished pieces, then the sketches they grew out of.

## Showcase

Every module in [`Showcase/`](Showcase/) builds with no `sorry`.

### Systems with three-valued fault states

[`SystemModel.lean`](Showcase/SystemModel.lean) · [`SystemExample.lean`](Showcase/SystemExample.lean) · [`HeytAlg.lean`](Showcase/HeytAlg.lean)

<!-- Motivation: to be written. -->

An axiomatic `System` class covers components, elements, and the part-of / depends-on / field-of relations. The state of an element is a truth value in **Gödel's three-valued logic** (`valid / unknown / faulty`), with modal operators □ ("certainly") and ◇ ("possibly"). State assignments over a system are proven to form a Heyting algebra.

```lean
theorem state_box_pessimist : □(.unknown) = .faulty
theorem state_diamond_box_dual : ∀ S1 : G3State, ◇S1 = ¬(□(¬S1))

instance {Component : Type v} (Element : Type u) [System Component Element] :
    HeytAlg.HeytAlg (Component -> Element -> G3State)
```

The worked example models a **power grid** (plants → transformers → houses) as coherent sub-grids, with proven algebraic laws, and instantiates the `System` class.

### Cyber-physical composition

[`CyberPhy.lean`](Showcase/CyberPhy.lean)

<!-- Motivation: to be written. -->

It defines boxes (typed input/output interfaces) and **Moore machines**, and makes each a Mathlib `MonoidalCategory`: parallel composition is the tensor product, and the associator, unitors and whiskering are all constructed explicitly. It also includes lax monoidal functors out of boxes.

```lean
instance : MonoidalCategory Box
instance : MonoidalCategory MooreMachine
```

### Lenses and agents

[`Optics.lean`](Showcase/Optics.lean) · [`Agents.lean`](Showcase/Agents.lean) · [`AgentsTests.lean`](Showcase/AgentsTests.lean)

<!-- Motivation: to be written. -->

Lenses (`view` / `update`) are defined with composition, products and identity laws. A stateful agent is a lens over a hidden state. Agents fuse in parallel and communicate through channels (put / copy / merge / barrier / filter). The examples run with `#eval`.

```lean
structure SimpleAgent I O where
  stateSignature : Type
  state : stateSignature
  agentLens : Lens stateSignature stateSignature O I

def fuse {I₁ O₁ I₂ O₂} (a₁ : SimpleAgent I₁ O₁) (a₂ : SimpleAgent I₂ O₂) :
  SimpleAgent (I₁ × I₂) (O₁ × O₂)
```

### A notification monad

[`NotificationsMonad.lean`](Showcase/NotificationsMonad.lean)

<!-- Motivation: to be written. -->

Commands that emit domain events are modelled as a writer-style monad. An endpoint belongs to a domain. Calling it runs the command, tags its notification with that domain, and carries along every upstream notification. For example, repricing an order line in `Orders` triggers a price change in `Catalog`, and the caller receives both events.

```lean
def Notify (T : Type) : Type := T × List DomainNotification
instance : Monad Notify

structure Endpoint (D : Domain) (InType : Type) (OutType : Type)
```

### Notifications that follow the context map

[`ContextMapNotifications.lean`](Showcase/ContextMapNotifications.lean)

The notification monad above, with the context map as a type. `Svc D α` is a computation in domain `D`: a value, the events it caused in the order they happened, and a proof that each event comes from `D` or from a domain upstream of `D`. `emit` is the only way to create an event and tags it with `D`. `call` needs an `Upstream U D` instance, so a call against the context map does not compile. `Svc D` is proven a lawful monad; `deliver` merges the events of one command (three, in the refund example) into one message for the user without losing any the user should see; and a closed map lets negative facts be proved (no event from Payments ever reaches Catalog). Core Lean only.

```lean
def Svc (D : Domain) (α : Type) : Type :=
  { r : α × List Event // ∀ e ∈ r.2, Reaches e.domain D }
instance (D) : LawfulMonad (Svc D)

def call {U D α β} [h : Upstream U D] (e : Endpoint U α β) (a : α) : Svc D β
theorem no_payment_events_in_catalog : ¬ Reaches .Payments .Catalog
```

## Production systems

[`Production/`](Production/) is the code of the series "Composable production systems" on richardschmidt.pro, one module per part, built on the Moore machines of `CyberPhy.lean`. No `sorry`.

- [`Station.lean`](Production/Station.lean): a machining station as a Moore machine, `run` and its timing convention (n inputs, n + 1 outputs), and a station that stays failed until repaired.
- [`Boxes.lean`](Production/Boxes.lean): the line's stations as boxes, and two ways to wire them: in series, and in series with a handoff in which machining's input depends on assembly's output (feedback). Wiring only, no behaviour. The handoff never hides a fault (`handoff_keeps_fault`), and the signal it replaces would have changed nothing (`blocked_ignores`).
- [`Wiring.lean`](Production/Wiring.lean): a machine with a box as its interface, wiring as lens composition, and the functor `Box ⥤ Type 1` (its laws hold by `rfl`). Serial composition is two machines side by side, wired into one box; `run_serial` proves that the second machine sees the first one step late. In series only, the line stops at the first finished part; with the handoff, parts flow. Side by side is associative and unital up to relabelling the states, not as an equation.

```lean
def wire {A B : Box} (f : A ⟶ B) (M : Machine A) : Machine B
theorem run_serial (M : Machine ⟨I, X⟩) (N : Machine ⟨X, O⟩) (m n inputs) :
    (M ≫ₛ N).run (m, n) inputs = N.run n (M.run m inputs).dropLast
```

## DDD

[`DDD/`](DDD/) models bounded contexts as finitely presented categories, context maps as diagrams of them, and the integration of contexts into larger systems, with a Julia side (Catlab) whose results Lean checks. [`DDD/README.md`](DDD/README.md) describes the structures, the theorems and checks, and the roadmap. `sorry` is allowed.

Phases 1 to 3 are done, revised after a review of their decisions. A schema is a finite presentation (entity types, references, attributes into shared value types, equations, aggregates, value objects) with a well-formedness check that `decide` runs, and `Schema.cat` is the category it presents. Path equality is decided for schemas without equations and for acyclic schemas. A translation between schemas is checked valid the same way and induces a functor. A context map sends each context to its schema category and each arrow to such a functor, on the category of contexts presented by its arrows and declared equations between routes; its lax integration is a Grothendieck construction into which every context of a map without cycles embeds fully faithfully. Published languages are contexts that contain aggregate roots only. Two schemas glued along a shared kernel give a pushout in `Cat` (the bridge theorem), and the two arrows out of a kernel context glue their targets into the pushout of their images; states of the glued schema are pairs of states that agree on the kernel (data gluing), and a decidable check tells whether a merge leaves each context unchanged. The Catalog, Orders, Payments and Shipping schemas in [`Examples/`](DDD/Examples/), a context map with their published languages and a shared kernel that refines the map of `ContextMapNotifications.lean`, and the gluing of Orders and Shipping along that kernel are checked this way.

Declared equations between routes are checked rather than proved: the two routes of each equation induce the same functor, which a decidable comparison of the composite translations shows. Phase 4 connects the library to Catlab. Lean exports the example map as JSON ([`cli/CsdExport.lean`](cli/CsdExport.lean)); [`julia/`](julia/) glues the schemas as acset pushouts, restricts finite states along translations and searches for homomorphisms between them, and writes a certificate of claims; `csd-check` ([`cli/CsdCheck.lean`](cli/CsdCheck.lean)) checks each claim with a checker proved sound. Finite states, in the shape of acsets, are states of the schema they pass the check for, and restriction on them agrees with restriction of states up to isomorphism. CI runs the three steps on each push. [`DDD/docs/approach.md`](DDD/docs/approach.md) describes the approach in depth, with diagrams.

A kernel shared by more than two contexts, or contexts that share several kernels, merge as a component. The union of the member schemas is the colimit of `D` restricted to the component, when the members share names only through kernels, a condition checked along the list of members; it rests on a covering theorem that glues functors out of any number of agreeing parts. The merged map has the component as one context, with each arrow into a member composed with the leg of the member. [`Examples/Merge.lean`](DDD/Examples/Merge.lean) merges Orders, Shipping and Payments along the Customers kernel and a second kernel, Addresses, and checks the merged map.

```lean
def Schema.cat (S : Schema) : Cat := Cat.of (CategoryTheory.Quotient S.rel)
theorem pathEqAcyclic_iff (hS : S.WellFormed) (hA : S.Acyclic) (a : S.Obj) (l l' : List String) :
    S.pathEqAcyclic a.1 l l' = true ↔ S.PathEq a l l'
def Translation.functor (hS' : S'.WellFormed) (hT : T.Valid S S') : S.cat ⥤ S'.cat
theorem ContextMap.nonInterference (hJ : ∀ (c : M.J) (f : c ⟶ c), f = 𝟙 c) (c : C) :
    (M.embed c).Full ∧ (M.embed c).Faithful ∧ Function.Injective (M.embed c).obj
theorem Gluing.isPushout : IsPushout (C := Cat.{0, 0}) D.ι₁ D.ι₂ D.inl D.inr
theorem ContextMap.isPushout_kernel :
    IsPushout (M.diagram.map (M.arrow f₁)) (M.diagram.map (M.arrow f₂))
      (M.kernelGluing f₁ f₂ hk hc hwf).inl (M.kernelGluing f₁ f₂ hk hc hwf).inr
def Gluing.stateEquiv : D.glued.State K ≃ { P : D.left.State K × D.right.State K //
    restrictState _ _ P.1 = restrictState _ _ P.2 }
def FinState.toState (hX : X.check S = true) : S.State K
def FinState.restrictIso (hS : S.WellFormed) (hS' : S'.WellFormed) (hX : X.check S' = true)
    (hT : T.Valid S S') :
    (X.restrict T S S').toState (restrict_check hS hX hT) ≅ restrictState hS' hT (X.toState hX)
theorem Certificate.checkClaim_sound (cl : Claim) (h : c.checkClaim cl = true) : c.Holds cl
noncomputable def ContextMap.Component.isColimit : IsColimit P.cocone  -- apex (glueAll members).cat
```

## Sketches

The modules in [`Sketches/`](Sketches/) build, but are drafts. Some proofs are still `sorry`, and they say so.

| Module | Content |
|---|---|
| [`Domains.lean`](Sketches/Domains.lean) | Context maps as domain graphs (an upstream/downstream relation) and systems built on them, each forming a category. The identity laws of the system category are still `sorry`. |
| [`Cats.lean`](Sketches/Cats.lean) | Small categories and functors from scratch; preorders as categories. |
| [`Groupoids.lean`](Sketches/Groupoids.lean) | Small groupoids, functors and natural transformations, with a two-object example. |
| [`ConcreteLinks.lean`](Sketches/ConcreteLinks.lean) | Typed, reversible links between items, composed as paths. |

[`wip/`](wip/) holds modules that do not compile yet:

| Module | Content | Missing |
|---|---|---|
| [`DDD.lean`](wip/DDD.lean) | Domains and entities as free products, and the category of systems. | The `map_inclusion` lemma statement does not type-check. |
| [`GraphCats.lean`](wip/GraphCats.lean) | A system's component relation as a category (reflexive closure). | The `GraphCat` instance lacks composition and its laws. |

[`deprecated/`](deprecated/) keeps earlier attempts (superseded models and approaches that did not work out) for reference. It is not built.

## Building

The Lean toolchain (v4.26.0) and Mathlib are pinned in `lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build           # Showcase, Sketches, Production, DDD
```

CI builds these libraries on each push, runs the Julia side of `DDD` and checks its certificate, and generates the API documentation. The Julia side needs Julia 1.10; [`julia/README.md`](julia/README.md) gives the commands.

## License

GPL-3.0, see [LICENSE](LICENSE).
