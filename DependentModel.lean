import Mathlib.Data.Finset.Basic

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
deriving DecidableEq, Repr

def defineEntity (c : Component) :
 String -> Entity c :=
  fun s => Entity.withName s

notation s " ⊏ " c => defineEntity c s

inductive Field {c : Component} (e : Entity c)  where
| valueSingle : ValueType -> String -> Field e
| valueCollection : ValueType -> String -> Field e
| relationSingle : (e' : Entity d) -> String -> Field e
| relationCollection : (e' : Entity d) -> String -> Field e
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

def ComponentEntities := Σ (c : Component), Entity c deriving Repr


def ComponentEntitiesStructure := Σ (c : Component), (e : Entity c) -> Finset (Field e)

instance {c : Component} : CoeOut (Entity c)  ComponentEntities where
  coe := fun e => ⟨ c, e ⟩

--
structure System where
  components : Finset Component
  entities : List ComponentEntities
  --fields : ∀ {c: Component}, (e : Entity c) -> Finset (Field e)

def meetingComponent := Component.withName "Meeting"
def identityComponent := Component.withName "Identity"

def meetingEntity := "Meeting" ⊏ meetingComponent
def agendaEntity := "Agenda" ⊏ meetingComponent
def userEntity := "User" ⊏ identityComponent

def allEntities : List ComponentEntities := [ meetingEntity,
  agendaEntity,
  userEntity]


def meetingEntityFields : Finset (Field meetingEntity) := {
  "id" :: ValueType.Numerical ⊸ meetingEntity,
  "author" :: userEntity ⊸ meetingEntity,
  "agenda" :: agendaEntity ⊸ meetingEntity
}

def agendaEntityFields : Finset (Field agendaEntity) := {
  "id" :: ValueType.Numerical ⊸ agendaEntity,
  "participants" :: [userEntity] ⊸ agendaEntity,
  "tags" :: [ValueType.Categorical] ⊸ agendaEntity
}

def ex : System := {
  components := {meetingComponent, identityComponent},
  entities := allEntities
}
