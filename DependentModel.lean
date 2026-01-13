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

def getComponent {c : Component} (_ : Entity c) : Component := c

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


def AbstractEntity := Σ (c : Component), Entity c deriving DecidableEq, Repr

def EntityFields (c : Component) := Σ (e : Entity c), List (Field e) deriving DecidableEq, Repr

def fieldToEntityFields {c : Component} (e : Entity c) (f : Field e) : EntityFields c :=
  ⟨ e, [f] ⟩

def ComponentBundle := Σ (c : Component), EntityFields c deriving DecidableEq, Repr

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

def meetingComponent := Component.withName "Meeting"
def identityComponent := Component.withName "Identity"

def meetingEntity := "Meeting" ⊏ meetingComponent
def agendaEntity := "Agenda" ⊏ meetingComponent
def userEntity := "User" ⊏ identityComponent

def allEntities : List AbstractEntity := [ meetingEntity,
  agendaEntity,
  userEntity]


def allFields : List ComponentBundle := [
  "id" :: ValueType.Numerical ⊸ meetingEntity,
  "author" :: userEntity ⊸ meetingEntity,
  "agenda" :: agendaEntity ⊸ meetingEntity,
  "id" :: ValueType.Numerical ⊸ agendaEntity,
  "participants" :: [userEntity] ⊸ agendaEntity,
  "tags" :: [ValueType.Categorical] ⊸ agendaEntity
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

def toySystem := ex [meetingComponent, identityComponent] allEntities allFields

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
        (⟨ c, e, f ⟩ : Σ (α : Component), (Σ (ε : Entity α ), (List (Field ε))))
    )
)
