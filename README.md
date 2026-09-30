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
lake build           # Showcase and Sketches
```

CI builds both libraries on each push and generates the API documentation.

## License

GPL-3.0, see [LICENSE](LICENSE).
