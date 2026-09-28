import Init.Core
import Batteries.Data.Array
import Showcase.Optics
import Mathlib.Data.Finset.Basic

namespace Agents

open Optics

universe u v

-- Agents
structure SimpleAgent I O where
  stateSignature : Type
  state : stateSignature
  agentLens : Lens stateSignature stateSignature O I


def get {I O} (a : SimpleAgent I O) : O := a.agentLens.view a.state

def process {I O} (a : SimpleAgent I O) (val : I) : SimpleAgent I O :=
    {
      stateSignature := a.stateSignature
      state := a.agentLens.update a.state val
      agentLens := a.agentLens
    }


def fuse {I₁ O₁ I₂ O₂} (a₁ : SimpleAgent I₁ O₁) (a₂ : SimpleAgent I₂ O₂) :
 SimpleAgent (I₁ × I₂) (O₁ × O₂) :=
  {
    stateSignature := a₁.stateSignature × a₂.stateSignature
    state := (a₁.state, a₂.state)
    agentLens := Lens.prod a₁.agentLens a₂.agentLens
  }

-- Helper function

def _root_.List.il {α : Type} : List α → List α → List α
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => a :: b :: il as bs

def _root_.Array.interleave {α : Type} (as bs : Array α) : Array α :=
  (as.toList.il bs.toList).toArray

-- Channels

structure Channel T where
  state : Array T
  lens : Lens (Array T) (Array T) T T

namespace Channel

def read {T} (c : Channel T) : Option T :=
  c.lens.view c.state

def put {T} (c : Channel T) : T -> Channel T :=
  fun t => {
    state := c.lens.update c.state t
    lens := c.lens
  }

def copy {T} (c : Channel T) : Channel T × Channel T :=
  (c, c)

def merge {T} (c c' : Channel T) : Channel T :=
  {
    state := c.state.interleave c'.state
    lens := {
      -- Should we check somehow that both lenses are coherent rather
      -- than arbitrarily choosing the left one ?
      view := c.lens.view
      update := c.lens.update
    }
  }

def barrier {T U} (c : Channel T) (d : Channel U) : Channel (T × U) :=
  {
    state :=  c.state.zip d.state
    lens := {
      view := fun s => let (l, r) := s.unzip
      (c.lens.view l, d.lens.view r)
      update := fun s p => s.append #[p]
    }
  }

-- We impose a condition on the maps to ensure that the mapping is faithful
def channelMap {T U} (f : T -> U) (f' : U -> T) (_ : f ∘ f' = id) (c : Channel T) : Channel U :=
  {
    state := c.state.map f
    lens := {
      view := fun s => f (c.lens.view (s.map f'))
      update := fun s p => (c.lens.update (s.map f') (f' p)).map f
    }
  }

def channelFilter {T} (p : T -> Bool) (c : Channel T) : Channel T :=
  {
    state := c.state.filter p
    lens := c.lens
  }

end Channel

inductive ChannelWrapper where
| ofType {T} : T -> Channel T -> ChannelWrapper

--structure HeterogeneousAgent where
--  stateSignature : Type
--  state : stateSignature
--
--  -- Index types for inputs and outputs
--  InIdx  : Type
--  OutIdx : Type
--
--  -- Type profiles mapping each index to its respective Data Type
--  InType  : InIdx → Type
--  OutType : OutIdx → Type
--
--  -- Lenses mapping to the respective channel types
--  inputLenses  : (i : InIdx) → Lens stateSignature stateSignature (InType i) (InType i)
--  outputLenses : (o : OutIdx) → Lens stateSignature stateSignature (OutType o) (OutType o)

end Agents
