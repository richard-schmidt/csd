import Init.Core
import Showcase.HeytAlg

inductive ValueType where
| Numerical
| Textual
| Temporal
| Categorical
deriving DecidableEq, Repr

inductive Component where
| withName : String -> Component
deriving DecidableEq, Repr

inductive Entity (c : Component) where
| withName : String -> Entity c
| join : Entity c -> Entity c -> Entity c
deriving DecidableEq, Repr

def defineEntity (c : Component) :
 String -> Entity c :=
  fun s => Entity.withName s

notation s " ⊏ " c => defineEntity c s

inductive Field {c : Component} (e : Entity c)  where
| valueSingle : ValueType -> String -> Field e
| valueCollection : ValueType -> String -> Field e
| relationSingle {d : Component} : (e' : Entity d) -> String -> Field e
| relationCollection {d : Component} : (e' : Entity d) -> String -> Field e
deriving DecidableEq, Repr

def defineSimpleValueField {c : Component} (e : Entity c) :
ValueType -> String -> Field e :=
  fun v s => Field.valueSingle v s

def defineCollectionValueField {c : Component} (e : Entity c) :
ValueType -> String -> Field e :=
  fun v s => Field.valueCollection v s

def defineSingleRelationField {c d : Component} (e : Entity c) :
Entity d -> String -> Field e :=
  fun e s => Field.relationSingle e s

def defineCollectionRelationField {c d : Component} (e : Entity c) :
 Entity d -> String -> Field e :=
  fun e s => Field.relationCollection e s

notation s " :: " v " ⊸ " e => defineSimpleValueField e v s
notation s " :: " "[" v "]" " ⊸ " e => defineCollectionValueField e v s
notation s " :: " f " ⊸ " e => defineSingleRelationField e f s
notation s " :: " "[" f "]" " ⊸ " e => defineCollectionRelationField e f s

def mapField {c : Component} {e e' : Entity c} : Field e -> Field e' :=
  fun f =>
  match f with
  | Field.valueSingle v s => s :: v ⊸ e'
  | Field.valueCollection v s => s :: [v] ⊸ e'
  | Field.relationSingle e'' s => s :: e'' ⊸ e'
  | Field.relationCollection e'' s => s :: [e''] ⊸ e'

def AbstractEntity := Σ (c : Component), Entity c deriving Repr

def EntityFields (c : Component) := Σ (e : Entity c), List (Field e) deriving Repr

def fieldToEntityFields {c : Component} (e : Entity c) (f : Field e) : EntityFields c :=
  ⟨ e, [f] ⟩

def efJoin {c : Component} : EntityFields c -> EntityFields c -> EntityFields c :=
  fun ef ef' =>
  match ef, ef' with
  | ⟨ e, f ⟩, ⟨ e', f' ⟩ => if _ : e = e' then ⟨ e, f ++ (f'.map mapField) ⟩ else
   let e'' := Entity.join e e'; ⟨ e'', (f.map mapField) ++ (f'.map mapField) ⟩

def ComponentBundle := Σ (c : Component), EntityFields c deriving Repr

instance {c : Component} : CoeOut (Entity c) AbstractEntity where
  coe e := ⟨ c, e ⟩

instance {c : Component} : CoeOut (EntityFields c)  ComponentBundle where
  coe e := ⟨ c, e ⟩

instance {c : Component} {e : Entity c} : CoeOut (Field e) ComponentBundle where
  coe f := ⟨ c, fieldToEntityFields e f ⟩

def fieldMatchBuild (l : List (List (ComponentBundle))) :
 (c : Component) -> List (EntityFields c) :=
  fun c =>
    l.flatten.filterMap (fun ⟨ found, compEnt ⟩ =>
                          if h : c = found then
                          some (h ▸ compEnt)
                          else
                          none)

structure System where
  components : List Component
  entities : ∀ (c : Component), List (Entity c)
  fields : ∀ (c : Component), List (EntityFields c)

section SystemModelExample

def lendingComponent := Component.withName "Lending"
def identityComponent := Component.withName "Identity"

def loanEntity := "Loan" ⊏ lendingComponent
def bookEntity := "Book" ⊏ lendingComponent
def userEntity := "User" ⊏ identityComponent

def allEntities : List AbstractEntity := [ loanEntity,
  bookEntity,
  userEntity]


def allFields : List ComponentBundle := [
  "id" :: ValueType.Numerical ⊸ loanEntity,
  "borrower" :: userEntity ⊸ loanEntity,
  "book" :: bookEntity ⊸ loanEntity,
  "id" :: ValueType.Numerical ⊸ bookEntity,
  "authors" :: [userEntity] ⊸ bookEntity,
  "tags" :: [ValueType.Categorical] ⊸ bookEntity
]

def ex (inputComponents : List Component)
 (inputEntities : List AbstractEntity)
 (inputFields : List ComponentBundle) : System :=
  {
  components := inputComponents
  entities := fun c => if _ : c ∈ inputComponents then inputEntities.filterMap (fun ⟨ fc, fe ⟩  =>
                                                              if h : fc = c then
                                                              some (h ▸ fe)
                                                              else
                                                              none)
                                          else []
  fields := fun c => if _ : c ∈ inputComponents then inputFields.filterMap (fun ⟨ fc , ff ⟩ =>
                                                                            if h : fc = c then
                                                                            some (h ▸ ff)
                                                                            else
                                                                            none)
                                                else []
  }

def toySystem := ex [lendingComponent, identityComponent] allEntities allFields

#eval (toySystem.components).map
  (
    fun c =>
      (toySystem.entities c).map
        (fun e =>
          (⟨c, e⟩ : AbstractEntity)
        )
  )

#eval (toySystem.components).map
(
  fun c =>
    (toySystem.fields c).map
    (
      fun ⟨ e, f ⟩  =>
        (⟨ c, e, f ⟩ : Σ (α : Component), EntityFields α)
    )
)

def compA : Component := Component.withName "A"
def compB : Component := Component.withName "B"
def entAa := "Aa" ⊏ compA
def entAb := "Ab" ⊏ compA
def entBa := "Ba" ⊏ compB
def entBb := "Bb" ⊏ compB
def f1 := "f1" :: ValueType.Categorical ⊸ entAa
def f2 := "f2" :: entBa ⊸ entAa
def f3 := "f3" :: ValueType.Numerical ⊸ entAb
def f4 := "f4" :: [entBb] ⊸ entAb

#eval efJoin ⟨ entAa, [f1, f2]⟩  ⟨ entAb, [f3, f4] ⟩

end SystemModelExample
