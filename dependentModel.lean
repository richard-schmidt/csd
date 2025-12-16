-- a Component represents a functional domain, a software module, a DDD bounded context
@[ext]
structure Component where
  name : String
deriving DecidableEq, Repr

-- Entities are elements of Components
@[ext]
structure Entity (α : Component) where
  name : String
deriving DecidableEq, Repr

-- Value types
inductive Value where
  | Int
  | String
  | Uuid
  | Datetime
  | Timestamp
  | Bool

-- Utility to derivate Components from names
def stringToComponent : String -> Component :=
  fun s => {name := s}

instance : Coe String Component where coe := stringToComponent

-- Utility to retrieve a Component from an Entity
def parentComponent : (Entity α) -> Component :=
  fun _ => α

-- Syntactic sugar
def defineEntity (α : Component) : String -> Entity α :=
  fun s => {name := s}

notation s "⊏" α => defineEntity α s

inductive EntityField {α :Component}  (e : Entity α) where
  | fieldName : String -> EntityField e
deriving DecidableEq, Repr

def entityFieldName (ef : EntityField e) : String :=
  match ef with
  | EntityField.fieldName s => s

-- Defines an inclusion relation between entities with no specific arity
inductive EntityRelationField (e₁ : Entity α) (e₂ : Entity β) where
  | simpleField : EntityField e₁ -> EntityRelationField e₁ e₂
  | collection : EntityField e₁ -> EntityRelationField e₁ e₂
deriving DecidableEq, Repr

@[coe]
def retrieveEntityFieldFromRelation(erf : EntityRelationField e₁ e₂) : EntityField e₁ :=
  match erf with
  | EntityRelationField.simpleField ef => ef
  | EntityRelationField.collection ef =>  ef

instance : CoeOut (EntityRelationField e₁ e₂) (EntityField e₁) where coe := retrieveEntityFieldFromRelation

inductive EntityValueField (e₁ : Entity α) (v: Value) where
  | value : EntityField e₁ -> EntityValueField e₁ v
deriving DecidableEq, Repr

def entityRelationName (erf : EntityRelationField e₁ e₂) : String :=
  entityFieldName (retrieveEntityFieldFromRelation erf)


-- Syntatic sugar
def defineSimpleEntityRelationField (e₁ : Entity α)  (e₂ : Entity β) : String -> EntityRelationField e₁ e₂ :=
  fun s => EntityRelationField.simpleField (EntityField.fieldName s)

def defineCollectionEntityRelationField (e₁ : Entity α) (e₂ : Entity β) : String -> EntityRelationField e₁ e₂ :=
  fun s => EntityRelationField.collection (EntityField.fieldName s)

notation f " :: " e₂ " ⊸ " e₁ => defineSimpleEntityRelationField e₁ e₂ f
notation f " :: " "["e₂"]" " ⊸ " e₁ => defineCollectionEntityRelationField e₁ e₂ f

/-
------          ------
        Example
------          ------
-/


def ex := "f1" :: ("E1" ⊏ "C1") ⊸ ("E2" ⊏ "C2")
#eval entityRelationName ex

-- Utility to mass declare Entities
def defineEntities : (α : Component) -> (names : List String) -> Component × (List (Entity α)) :=
  fun α names => Prod.mk α (names.map (fun n => n ⊏ α))

instance meetingsComponent : Component := {name := "Meetings"}
def itemEntity := "Item" ⊏ "Meetings"

#eval meetingsComponent
#eval parentComponent itemEntity
#eval parentComponent itemEntity = meetingsComponent

def userEntity := "User" ⊏ "Identity"

def y := "author" :: userEntity ⊸ itemEntity
def x := "author" :: ("User" ⊏ "Identity") ⊸ ("Item" ⊏ "Meetings")
#check x
#check y
#eval x = y

def m := defineEntities "Meetings"
  [
    "Meeting",
    "MeetingType",
    "PlenaryMeeting",
    "CommissionMeeting",
    "Participant",
    "Agenda",
    "Entry",
    "Section",
    "Item"
  ]

def meetingComponent := m.1

def TestType := Entity meetingComponent

/-
!Fails

def meetingFields e : List (e: Entity meetingComponent) × EntityField e :=
  [
    "agenda" :: "Agenda" ⊏ meetingComponent ⊸ "Meeting" ⊏ meetingComponent,
    "entries" :: "Entry" ⊏ "meetingComponent" ⊸ "Agenda" ⊏ meetingComponent
  ]

-/

def o := defineEntities "Organization"
  [
    "Organization",
    "Unit",
    "OrganizationUnitMembership"
  ]

def organizationsComponent := o.1

def entitiesFields :=
  [
      "units" :: ["Unit" ⊏ "Organization"] ⊸ "Organization" ⊏ "Organization"
  ]
