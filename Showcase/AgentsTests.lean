import Init.Core
import Batteries.Data.Array
import Showcase.Optics
import Showcase.Agents

namespace AgentsTests

open Optics Agents

universe u v

def a1 : SimpleAgent Nat Bool :=
  {
    stateSignature := Array Nat
    state := #[1]
    agentLens := {
      view := fun s => let n := s.back?
        match n with
        | some n' => (n' % 2 = 0) = true
        | none => false
      update := fun s i => s.append #[i]
    }
  }

def inputStream := #[1, 2, 3, 2, 5, 8, 2]

#eval get (process a1 1)

#eval (List.scanl (fun a i => process a i) a1 inputStream.toList).map (fun x => get x)


def a2 : SimpleAgent String (Option String) :=
  {
    stateSignature := Array String
    state := #["init"]
    agentLens := {
      view := fun s => s.back?
      update := fun s i => s.append #[i]
    }
  }

def inputStream2 := #["incoming data 1", "incoming data 2", "incoming data 3"]

#eval (List.scanl (fun a i => process a i) a2 inputStream2.toList).map (fun x => get x)

def a12 := fuse a1 a2

def fusedInputStream :=
  let l := inputStream.size
  let r := inputStream2.size
  if l == r then
    Array.zip inputStream inputStream2
    else (
      if r < l then
        Array.zip inputStream (inputStream2.rightpad l "")
        else Array.zip (inputStream.rightpad r 0) inputStream2
    )

def result := (List.scanl (fun a i => process a i) a12 fusedInputStream.toList).map (fun x => get x)
#eval result

-- Channel tests

def c1 : Channel String := {
  state := #["T", "F", "Y", "N"]
  lens := {
    view := fun s => s.back!
    update := fun s b => s.append #[b]
  }
}

def f1 : String -> Bool :=
  fun s => match s with
  | "T" | "Y" => true
  | _ => false

def f1' : Bool -> String := fun b => match b with | true => "T" | false => "F"

theorem finv : f1 ∘ f1' = id := by
  ext b
  cases b <;> rfl

def mapped_c1 := Channel.channelMap f1 f1' finv c1

#eval c1.read
#eval mapped_c1.read
def c1' := c1.put "Y"
def mapped_c1' := Channel.channelMap f1 f1' finv c1'
#eval c1'.read
#eval mapped_c1'.read

end AgentsTests
