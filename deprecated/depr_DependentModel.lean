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
def parentComponent {α : Component} : (Entity α) -> Component :=
  fun _ => α

-- Syntactic sugar
def defineEntity (α : Component) : String -> Entity α :=
  fun s => {name := s}

notation s "⊏" α => defineEntity α s

inductive EntityField {α :Component}  (e : Entity α) where
  | fieldName : String -> EntityField e
deriving DecidableEq, Repr

def entityFieldName {α : Component} {e : Entity α} (ef : EntityField e) : String :=
  match ef with
  | EntityField.fieldName s => s

-- Defines an inclusion relation between entities with no specific arity
inductive EntityRelationField {α β : Component} (e₁ : Entity α) (e₂ : Entity β) where
  | simpleField : EntityField e₁ -> EntityRelationField e₁ e₂
  | collection : EntityField e₁ -> EntityRelationField e₁ e₂
deriving DecidableEq, Repr

@[coe]
def retrieveEntityFieldFromRelation {α β : Component} {e₁ : Entity α} {e₂ : Entity β} (erf : EntityRelationField e₁ e₂) : EntityField e₁ :=
  match erf with
  | EntityRelationField.simpleField ef => ef
  | EntityRelationField.collection ef =>  ef

instance {α β : Component} {e₁ : Entity α} {e₂ : Entity β} : CoeOut (EntityRelationField e₁ e₂) (EntityField e₁) where coe :=
 retrieveEntityFieldFromRelation

inductive EntityValueField {α : Component} (e₁ : Entity α) (v: Value) where
  | value : EntityField e₁ -> EntityValueField e₁ v
deriving DecidableEq, Repr

def entityRelationName {α β : Component} {e₁ : Entity α} {e₂ : Entity β} (erf : EntityRelationField e₁ e₂) : String :=
  entityFieldName (retrieveEntityFieldFromRelation erf)


-- Syntatic sugar
def defineSimpleEntityRelationField {α β : Component} (e₁ : Entity α)  (e₂ : Entity β) : String -> EntityRelationField e₁ e₂ :=
  fun s => EntityRelationField.simpleField (EntityField.fieldName s)

def defineCollectionEntityRelationField {α β : Component} (e₁ : Entity α) (e₂ : Entity β) : String -> EntityRelationField e₁ e₂ :=
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

instance lendingComponent : Component := {name := "Lending"}
def itemEntity := "Item" ⊏ "Lending"

#eval lendingComponent
#eval parentComponent itemEntity
#eval parentComponent itemEntity = lendingComponent

def userEntity := "User" ⊏ "Identity"

def y := "author" :: userEntity ⊸ itemEntity
def x := "author" :: ("User" ⊏ "Identity") ⊸ ("Item" ⊏ "Lending")
#check x
#check y
#eval x = y

def m := defineEntities "Lending"
  [
    "Loan",
    "LoanType",
    "ShortLoan",
    "InterLibraryLoan",
    "Borrower",
    "Book",
    "Chapter",
    "Section",
    "Item"
  ]

def loanComponent := m.1

def TestType := Entity loanComponent

/-
!Fails

def loanFields e : List (e: Entity loanComponent) × EntityField e :=
  [
    "book" :: "Book" ⊏ loanComponent ⊸ "Loan" ⊏ loanComponent,
    "chapters" :: "Chapter" ⊏ "loanComponent" ⊸ "Book" ⊏ loanComponent
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
