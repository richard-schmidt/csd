import Mathlib.Data.Finset.Basic

namespace ConcreteLinks

structure User where
  name : String
deriving DecidableEq, Repr

structure Item where
  label : String
  author : User
deriving DecidableEq, Repr

structure ItemLinkType where
  sourceLabel : String
  targetLabel : String
deriving DecidableEq, Repr

def ItemLinkType.rev (t : ItemLinkType) : ItemLinkType :=
{sourceLabel := t.targetLabel, targetLabel := t.sourceLabel}

def LinkLabel := Σ (_ : Item × Item), String deriving DecidableEq, Repr

inductive ItemLink : (s : Item) -> (t : Item) -> Type where
| mk {s t : Item} : ItemLinkType -> ItemLink s t
| append {s t u : Item} : ItemLink s u -> ItemLink u t -> ItemLink s t

def rev {s t : Item} : ItemLink s t -> ItemLink t s
  | ItemLink.mk x => ItemLink.mk x.rev
  | ItemLink.append j k => ItemLink.append (rev k) (rev j)

def ItemLink.reduceLabels {s t : Item} : ItemLink s t → List LinkLabel
  | ItemLink.mk iLinkType => [⟨(s, t), iLinkType.sourceLabel⟩]
  | ItemLink.append j k =>
    let j_reduced := ItemLink.reduceLabels j
    let k_reduced := ItemLink.reduceLabels k
    List.append j_reduced k_reduced

def print (l : LinkLabel) : String :=
l.1.1.label ++ " " ++ l.2 ++ " " ++ l.1.2.label.toLower

def u : User := {name := "Me"}
def item1 : Item := {label := "My earliest item", author := u}
def item2 : Item := {label := "My middle item", author := u}
def item3 : Item := {label := "My last item", author := u}
def referLT : ItemLinkType := {sourceLabel := "references", targetLabel := "is referenced by"}
def followLT : ItemLinkType := {sourceLabel := "follows", targetLabel := "is followed by"}

def l1 : ItemLink item1 item2 := ItemLink.mk referLT
def l2 : ItemLink item2 item3 := ItemLink.mk followLT

#eval (ItemLink.reduceLabels l1).map print
#eval (ItemLink.reduceLabels l2).map print
#eval (ItemLink.reduceLabels (ItemLink.append l1 l2)).map print
#eval (ItemLink.reduceLabels (rev (ItemLink.append l1 l2))).map print

end ConcreteLinks
