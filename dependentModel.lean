@[ext]
structure Component where
  name : String
deriving DecidableEq, Repr

@[ext]
structure Entity (α : Component) where
  name : String
deriving DecidableEq, Repr

inductive EntityField (e : Entity α) (f : Entity β) where
  | field : String -> EntityField e f
deriving DecidableEq, Repr

def defineEntityField (e₁ : Entity α) (e₂ : Entity β) : String -> EntityField e₁ e₂ :=
  fun s => EntityField.field s

notation e₁ " o-- " e₂ " ::= " f => defineEntityField e₁ e₂ f 

def fieldName (ef : (EntityField e f) ) : String :=
  match ef with
  | EntityField.field s => s

def defineEntities : (α : Component) -> (names : List String) -> List (Entity α) :=
  fun α names => names.map (fun n => {name := n: Entity α})

instance meetingsComponent : Component := {name := "Meetings"}
instance identityComponent : Component := {name := "Identity"}
instance itemEntity : Entity meetingsComponent := {name := "Item"}
instance userEntity : Entity identityComponent := {name := "User"}

#eval itemEntity o-- userEntity ::= "author"

instance tl : List (Entity meetingsComponent) := defineEntities meetingsComponent ["MeetingType", "PlenaryMeeting", "CommissionMeeting", "MeetingPrefix", "Participant", "Agenda", "Entry", "Section", "Item"]
