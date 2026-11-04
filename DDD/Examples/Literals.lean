import DDD.Literals

/-!
# Example: literals in normal form

`types` is a list of value types with an enumeration and a named type over
`decimal`. The `#guard` tests give, for each value type, literals written in
other forms and their normal forms, and literals that are not values of the
type. Two literals that denote the same value have the same normal form.
-/

set_option linter.hashCommand false

namespace DDD.Examples.Literals

open DDD

/-- An enumeration and a named type over `decimal`. -/
def types : TypeList where
  decls := [("DeliveryStatus", .enum ["scheduled", "dispatched", "delivered"]),
    ("Money", .over .decimal)]

/-- The normal form of a literal of `v`, or the sentence of the failure. -/
def nf (v : ValueType) (l : Lit) : Except String Lit := types.normalize v l

/-- The normal form of a text literal of `v`. -/
def text (v : ValueType) (s : String) : Option String :=
  match nf v (.text s) with
  | .ok (.text t) => some t
  | _ => none

/-- `s` is not a value of `v`. -/
def refused (v : ValueType) (l : Lit) : Bool :=
  match nf v l with
  | .ok _ => false
  | .error _ => true

/-! ## Sound lists and admitted types -/

#guard types.checkSound
#guard types.problems == []
#guard ({ decls := [("Money", .over .decimal), ("Money", .enum []), ("int", .over .int),
    ("Tag", .enum ["a", "a"]), ("Ref", .over (.named "Money"))] } : TypeList).problems ==
  [.duplicateType "Money", .emptyEnum "Money", .builtinName "int", .duplicateValue "Tag" "a",
    .baseNotBuiltin "Ref" (.named "Money")]

#guard types.admits (.optional (.named "Money"))
#guard !types.admits (.named "Currency")
#guard types.undeclared? (.optional (.named "Currency")) == some "Currency"
#guard !types.admits (.optional (.optional .int))

/-! ## Built-ins -/

#guard text .decimal "1.50" == some "1.5"
#guard text .decimal "+0012.000" == some "12"
#guard text .decimal "-0.0" == some "0"
#guard text .decimal ".5" == some "0.5"
#guard (nf .decimal (.int 3)).toOption == some (.text "3")
#guard refused .decimal (.text "1,5") && refused .decimal (.text "1e3") &&
  refused .decimal (.text ".")

#guard text .date "2024-02-29" == some "2024-02-29"
#guard refused .date (.text "2026-02-29") && refused .date (.text "2026-13-01") &&
  refused .date (.text "26-11-04")

#guard text .time "09:30" == some "09:30:00"
#guard text .time "09:30:00.500" == some "09:30:00.5"
#guard text .time "09:30:00,000" == some "09:30:00"
#guard refused .time (.text "24:00:00") && refused .time (.text "9:30")

#guard text .datetime "2026-11-04 09:30" == some "2026-11-04T09:30:00"
#guard text .datetime "2026-11-04t09:30:15.250" == some "2026-11-04T09:30:15.25"
#guard refused .datetime (.text "2026-11-04T09:30:00Z")

#guard text .timestamp "2026-11-04T09:30:00+01:00" == some "2026-11-04T08:30:00Z"
#guard text .timestamp "2026-11-04T08:30:00z" == some "2026-11-04T08:30:00Z"
#guard text .timestamp "2026-01-01T00:30:00+0100" == some "2025-12-31T23:30:00Z"
#guard text .timestamp "2024-02-28T23:00:00-02" == some "2024-02-29T01:00:00Z"
#guard text .timestamp "2026-12-31T23:59:59.9-01:00" == some "2027-01-01T00:59:59.9Z"
#guard refused .timestamp (.text "2026-11-04T09:30:00")
#guard refused .timestamp (.text "0000-01-01T00:30:00+01:00")

#guard text .duration "PT90M" == some "PT1H30M"
#guard text .duration "P1W" == some "P7D"
#guard text .duration "PT36H" == some "P1DT12H"
#guard text .duration "pt1.50s" == some "PT1.5S"
#guard text .duration "PT0S" == some "PT0S"
#guard text .duration "P0D" == some "PT0S"
#guard refused .duration (.text "P1M") && refused .duration (.text "P1Y") &&
  refused .duration (.text "PT") && refused .duration (.text "PT1.5M") &&
  refused .duration (.text "PT1S2M")

#guard text .uuid "7C9E6679-7425-40DE-944B-E07FC1F90AE7" ==
  some "7c9e6679-7425-40de-944b-e07fc1f90ae7"
#guard text .uuid "7c9e6679742540de944be07fc1f90ae7" ==
  some "7c9e6679-7425-40de-944b-e07fc1f90ae7"
#guard refused .uuid (.text "7c9e6679-7425-40de-944b")

#guard (nf .int (.int 4)).toOption == some (.int 4)
#guard refused .int (.text "4") && refused .string (.int 4) && refused .bool (.text "true")

/-! ## Named and optional types -/

#guard text (.named "DeliveryStatus") "dispatched" == some "dispatched"
#guard refused (.named "DeliveryStatus") (.text "Dispatched")
#guard text (.named "Money") "12.50" == some "12.5"
#guard refused (.named "Currency") (.text "CHF")

#guard (nf (.optional .string) .null).toOption == some .null
#guard text (.optional .timestamp) "2026-11-04T09:30:00+01:00" == some "2026-11-04T08:30:00Z"
#guard refused .string .null
#guard refused (.optional (.optional .int)) .null

/-! ## Records and tables -/

/-- A record, two enumerations and a table between them. -/
def withRecords : TypeList where
  decls := [("Status", .enum ["placed", "paid"]), ("Phase", .enum ["open", "closed"]),
    ("Address", .record [("street", .string), ("city", .string), ("zip", .optional .string)])]
  tables := [⟨"phase", .named "Status", .named "Phase", [("placed", "open"), ("paid", "closed")]⟩,
    ⟨"isPaid", .named "Status", .bool, [("placed", "false"), ("paid", "true")]⟩]

#guard withRecords.checkSound
#guard withRecords.values? .bool == some ["false", "true"]
#guard withRecords.values? (.named "Address") == none

-- A record literal: fields sorted by name, each in normal form, an absent optional
-- field written as null.
#guard (withRecords.normalize (.named "Address") (.record [("street", .text "Main 1"),
    ("zip", .null), ("city", .text "Bern")])).toOption ==
  some (.record [("city", .text "Bern"), ("street", .text "Main 1"), ("zip", .null)])
#guard (withRecords.normalize (.named "Address") (.record [("street", .text "Main 1")])).toOption ==
  none
#guard (withRecords.normalize (.named "Address") (.record [("street", .text "x"),
    ("city", .text "y"), ("zip", .null), ("country", .text "CH")])).toOption == none
#guard (withRecords.normalize (.optional (.named "Address")) .null).toOption == some .null

/-- A list whose records and tables break each condition once. -/
def brokenRecords : TypeList where
  decls := [("R", .record []), ("S", .record [("a", .int), ("a", .int), ("some", .int)]),
    ("T", .record [("r", .named "S"), ("u", .named "Undeclared")])]
  tables := [⟨"int", .int, .bool, []⟩, ⟨"t", .bool, .bool, [("true", "false"), ("true", "maybe")]⟩]

#guard brokenRecords.problems ==
  [.emptyRecord "R", .duplicateField "S" "a", .reservedField "S" "some",
    .fieldType "T" "r" (.named "S"), .fieldType "T" "u" (.named "Undeclared"),
    .tableName "int", .tableSource "int" .int,
    .rowTwice "t" "true", .rowTarget "t" "maybe", .rowMissing "t" "false"]

end DDD.Examples.Literals
