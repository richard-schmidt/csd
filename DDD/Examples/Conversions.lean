import DDD.Report
import DDD.VData

/-!
# Example: conversions

`types` is the list of value types of the example map with conversions and a
record: the enumeration `Phase`, the named type `Instant` over `timestamp`, the
record `PostalAddress`, and the tables `phase`, `isOpen`, `active` and `settled`
between finite types. The schema `billing` has attributes of these types.

Each kind of conversion occurs in a path below: the built-ins out of
`timestamp` and `int`, coercions both ways, `string`, tables, `some` and lifts,
and the fields of a record. `pathEqualities` lists paths of `billing.vcat types`
that are equal by the equations of `TypeList.Basic`, which `Schema.pathEqV`
confirms; `conversions` lists paths of conversions with a literal in normal form
and the literal `TypeList.applyLit` gives. Both are claims of the certificate
`certificate`, which passes its check, and `Exchange.workspace` hands them to the
Julia side, which evaluates the conversions on its own.
-/

set_option linter.hashCommand false

namespace DDD.Examples.Conversions

open DDD

/-- The value types of the example map: enumerations, named types, a record, and
tables. -/
def types : TypeList where
  decls := [("OrderStatus", .enum ["placed", "paid", "shipped", "cancelled"]),
    ("PaymentMethod", .enum ["card", "invoice", "transfer"]),
    ("DeliveryStatus", .enum ["scheduled", "dispatched", "delivered"]),
    ("Money", .over .decimal), ("Phase", .enum ["open", "closed"]),
    ("Instant", .over .timestamp),
    ("PostalAddress", .record [("street", .string), ("city", .string),
      ("zip", .optional .string)])]
  tables := [
    ⟨"phase", .named "OrderStatus", .named "Phase",
      [("placed", "open"), ("paid", "open"), ("shipped", "closed"), ("cancelled", "closed")]⟩,
    ⟨"isOpen", .named "Phase", .bool, [("open", "true"), ("closed", "false")]⟩,
    ⟨"active", .named "OrderStatus", .bool,
      [("placed", "true"), ("paid", "true"), ("shipped", "false"), ("cancelled", "false")]⟩,
    ⟨"settled", .named "OrderStatus", .bool,
      [("placed", "false"), ("paid", "true"), ("shipped", "true"), ("cancelled", "false")]⟩]

#guard types.checkSound

/-- Invoices of customers, with attributes of the types of `types`. -/
def billing : Schema where
  entities := ["Invoice", "Customer"]
  refs := [⟨"customer", "Invoice", "Customer"⟩]
  attrs := [⟨"total", "Invoice", .named "Money"⟩, ⟨"lines", "Invoice", .int⟩,
    ⟨"issuedAt", "Invoice", .named "Instant"⟩, ⟨"status", "Invoice", .named "OrderStatus"⟩,
    ⟨"dueIn", "Invoice", .optional .duration⟩, ⟨"name", "Customer", .string⟩,
    ⟨"address", "Customer", .named "PostalAddress"⟩]

theorem billing_wellFormed : billing.WellFormed := by decide

/-! ## Path equality -/

/-- Paths out of `Invoice` that are equal in `billing.vcat types`. -/
def pathEqualities : List (List String × List String) := [
  -- The date of a timestamp, directly or through its date and time.
  (["issuedAt", "timestamp", "datetime", "date"], ["issuedAt", "timestamp", "date"]),
  -- A coercion followed by its inverse.
  (["total", "decimal", "Money"], ["total"]),
  -- Two paths of tables that compute the same function.
  (["status", "phase", "isOpen"], ["status", "active"]),
  -- A coercion followed by `string`.
  (["total", "decimal", "string"], ["total", "string"]),
  -- `some` and the lift of a field of a record.
  (["customer", "address", "city", "some"], ["customer", "address", "some", "city"]),
  -- `some`, and the lifts of a coercion and a built-in.
  (["issuedAt", "some", "timestamp", "date"], ["issuedAt", "timestamp", "date", "some"]),
  -- A lifted coercion followed by its inverse.
  (["total", "some", "decimal", "Money"], ["total", "some"]),
  -- The decimal of an integer, through a named type and back.
  (["lines", "decimal", "Money", "decimal"], ["lines", "decimal"])]

#guard pathEqualities.all fun (l, r) => billing.pathEqV types (.entity "Invoice") l r

-- Two tables that compute different functions are not identified.
#guard !billing.pathEqV types (.entity "Invoice") ["status", "active"] ["status", "settled"]
-- A path of the schema and a path of conversions out of different value types.
#guard !billing.pathEqV types (.entity "Invoice") ["total", "string"] ["lines", "string"]

/-- The date of the instant of an invoice is the date of its date and time. -/
theorem issuedAt_date : billing.VPathEq types ⟨.entity "Invoice", by decide⟩
    ["issuedAt", "timestamp", "datetime", "date"] ["issuedAt", "timestamp", "date"] :=
  Schema.pathEqV_sound billing_wellFormed _ (by decide)

/-- A path of two tables is the table it computes. -/
theorem status_active : billing.VPathEq types ⟨.entity "Invoice", by decide⟩
    ["status", "phase", "isOpen"] ["status", "active"] :=
  Schema.pathEqV_sound billing_wellFormed _ (by decide)

/-! ## Conversions of literals -/

/-- A postal address in normal form: its fields sorted by name. -/
def bern : Lit :=
  .record [("city", .text "Bern"), ("street", .text "Bahnhofstrasse 1"), ("zip", .null)]

/-- Paths of conversions out of a value type, a literal in normal form, and the
literal they give. -/
def conversions : List (ValueType × List String × Lit × Lit) := [
  (.named "Instant", ["timestamp", "date"], .text "2026-11-04T08:30:00Z", .text "2026-11-04"),
  (.named "Instant", ["timestamp", "time"], .text "2026-11-04T08:30:00Z", .text "08:30:00"),
  (.named "Instant", ["timestamp", "datetime"], .text "2026-11-04T08:30:00Z",
    .text "2026-11-04T08:30:00"),
  (.int, ["decimal", "Money", "string"], .int 3, .text "3"),
  (.named "OrderStatus", ["phase", "isOpen"], .text "shipped", .bool false),
  (.named "OrderStatus", ["active", "string"], .text "paid", .text "true"),
  (.named "PostalAddress", ["city"], bern, .text "Bern"),
  (.named "PostalAddress", ["zip"], bern, .null),
  (.named "PostalAddress", ["string"], bern,
    .text "{city: Bern, street: Bahnhofstrasse 1, zip: null}"),
  (.optional (.named "Money"), ["decimal", "string"], .text "12.5", .text "12.5"),
  (.optional (.named "Money"), ["decimal", "string"], .null, .null),
  (.named "Money", ["some", "decimal"], .text "12.5", .text "12.5"),
  (.optional .duration, ["string"], .text "PT1H30M", .text "PT1H30M")]

#guard conversions.all fun (v, l, x, y) =>
  match types.applyLit v l x with
  | .ok z => z == y
  | .error _ => false

-- No conversion `date` out of `Instant`: it goes through the coercion to its base.
#guard (types.convTgt? (.named "Instant") ["date"]).isNone
-- A table has a row for every value of its source.
#guard match types.applyLit (.named "Phase") ["isOpen"] (.text "closed") with
  | .ok y => y == .bool false
  | .error _ => false

/-! ## A state and the certificate -/

/-- Two invoices of one customer. -/
def state : FinState LitK where
  sizes := [("Invoice", 2), ("Customer", 1)]
  refs := [(("Invoice", "customer"), [0, 0])]
  attrs := [
    (("Invoice", "total"), [⟨.named "Money", .text "33.00"⟩, ⟨.named "Money", .int 8⟩]),
    (("Invoice", "lines"), [⟨.int, .int 2⟩, ⟨.int, .int 1⟩]),
    (("Invoice", "issuedAt"), [⟨.named "Instant", .text "2026-11-04T09:30:00+01:00"⟩,
      ⟨.named "Instant", .text "2026-11-05T10:00:00Z"⟩]),
    (("Invoice", "status"), [⟨.named "OrderStatus", .text "paid"⟩,
      ⟨.named "OrderStatus", .text "placed"⟩]),
    (("Invoice", "dueIn"), [⟨.optional .duration, .text "P30D"⟩, ⟨.optional .duration, .null⟩]),
    (("Customer", "name"), [⟨.string, .text "Ada"⟩]),
    (("Customer", "address"), [⟨.named "PostalAddress",
      .record [("street", .text "Bahnhofstrasse 1"), ("city", .text "Bern"), ("zip", .null)]⟩])]

/-- The schema, the state and the claims about them. -/
def certificate : Certificate where
  valueTypes := types
  schemas := [("Billing", billing)]
  states := [("XBilling", "Billing", state.normalize types)]
  claims := [.valueTypes, .wellFormed "Billing", .declared "Billing", .state "XBilling"] ++
    pathEqualities.map (fun (l, r) => .pathEquality "Billing" (.entity "Invoice") l r) ++
    conversions.map fun (v, l, x, y) => .conversion v l x y

#guard certificate.check

-- A path equality that does not hold, and a conversion with a wrong result, fail
-- their claims, and the report names the reason.
#guard !certificate.checkClaim
  (.pathEquality "Billing" (.entity "Invoice") ["status", "active"] ["status", "settled"])
#guard ((certificate.explain (.pathEquality "Billing" (.entity "Invoice") ["status", "active"]
    ["status", "settled"])).map (·.getObjValD "kind")) == [.str "pathsDiffer"]
#guard ((certificate.explain (.conversion (.named "OrderStatus") ["active"] (.text "paid")
    (.bool false))).map (·.getObjValD "kind")) == [.str "conversionResult"]
#guard ((certificate.explain (.conversion (.named "Money") ["decimal"] (.text "12.50")
    (.text "12.50"))).map (·.getObjValD "kind")) == [.str "notNormal"]

end DDD.Examples.Conversions
