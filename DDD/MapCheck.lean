import DDD.Report
import DDD.ContextMap

/-!
# Context map documents as context maps

A context map document (`MapDoc`, `Json.lean`) lists contexts and arrows by name.
`MapDoc.certificate` (`Report.lean`) holds its claims about each context and each
arrow. This module adds the conditions on the map as a whole, and proves that a
document that passes all of them is a context map (`ContextMap`).

The conditions, each a check on the document:

- `checkNames`: the names of the contexts are distinct, and so are those of the
  arrows;
- `checkKernels`: every arrow out of a context marked as a kernel is the empty
  translation;
- `checkPublished`: every arrow marked as publishing keeps the entity types of its
  source apart and sends them to roots of its target (`ContextMap.Publishes`);
- `checkAcyclic`: the ranks computed for the contexts (`rank`, the length of the
  longest route into each) increase along every arrow, so the map has no cycle;
- `checkRoutes`: each declared equation names two routes between the same
  contexts whose composite translations induce the same functor
  (`checkRouteEqn`).

`MapDoc.check` is the conjunction of these with the check of the certificate.

- `MapDoc.Ctx` is the type of the contexts of a document, a quiver with the
  arrows of the document.
- `MapDoc.contextMap`: a document that passes `check` is a context map on
  `Ctx`, with its declared route equations and its kernels.
- `MapDoc.nonInterference`: each of its contexts embeds into the lax integration
  fully faithfully and injectively on objects.
- `MapDoc.publishes`: each arrow marked as publishing presents its source as a
  published language of its target.

`MapDoc.report` is the report of a document for `csd-check --json`: the list of
value types, each context with the problems of its schema and of the event types
it publishes, each arrow with the problems of its claims and of its kernel and
publishing conditions, and the map with the problems of its names, cycles and route
equations. An event type whose context the document does not have is a problem of
the map.
-/

namespace DDD

open CategoryTheory Lean

namespace MapDoc

variable (M : MapDoc)

/-- An arrow of a document: its name, source, target and translation. -/
abbrev Arrow : Type := String × String × String × Translation

/-- The names of the contexts. -/
def names : List String := M.contexts.map (·.1)

/-- The context named `n` is marked as a kernel. -/
def isKernel (n : String) : Bool := ((M.contexts.lookup n).map (·.2)).getD false

/-! ## The conditions on the map -/

/-- The names of the contexts are distinct, and so are the names of the arrows. -/
def checkNames : Bool := decide M.names.Nodup && decide (M.arrows.map (·.1)).Nodup

/-- An arrow out of a kernel is the empty translation. -/
def kernelOk (a : Arrow) : Bool := !M.isKernel a.2.1 || decide (a.2.2.2 = {})

def checkKernels : Bool := M.arrows.all M.kernelOk

/-- An arrow marked as publishing keeps the entity types of its source apart and
sends them to roots of its target. -/
def publishOk (a : Arrow) : Bool :=
  !M.published.contains a.1 ||
    match M.certificate.schema? a.2.1, M.certificate.schema? a.2.2.1 with
    | some P, some S => decide ((P.entities.map a.2.2.2.ent).Nodup ∧ a.2.2.2.RootsOnly P S)
    | _, _ => false

def checkPublished : Bool := M.arrows.all M.publishOk

/-- One round of the ranks: each context one above the highest rank of the sources
of the arrows into it. -/
def rankStep (r : List (String × Nat)) : List (String × Nat) :=
  M.names.map fun n => (n, (M.arrows.filter fun a => a.2.2.1 == n).foldl
    (fun m a => max m ((r.lookup a.2.1).getD 0 + 1)) 0)

/-- The ranks after as many rounds as there are contexts. In a map without cycles,
the rank of a context is the length of the longest route into it. -/
def ranks : List (String × Nat) :=
  Nat.iterate M.rankStep M.contexts.length (M.names.map fun n => (n, 0))

/-- The rank of the context named `n`. -/
def rank (n : String) : Nat := (M.ranks.lookup n).getD 0

/-- The rank increases along an arrow between two contexts of the document. -/
def rankOk (a : Arrow) : Bool :=
  !(M.names.contains a.2.1 && M.names.contains a.2.2.1) || decide (M.rank a.2.1 < M.rank a.2.2.1)

/-- The ranks increase along every arrow, so the map has no cycle. -/
def checkAcyclic : Bool := M.arrows.all M.rankOk

/-! ## The quiver of contexts -/

/-- The contexts of a document. -/
def Ctx : Type := { n : String // n ∈ M.names }

instance : DecidableEq M.Ctx := inferInstanceAs (DecidableEq { n : String // n ∈ M.names })

/-- The arrows of the document from `u` to `d`. -/
instance : Quiver.{1} M.Ctx where
  Hom u d := { a : Arrow // a ∈ M.arrows ∧ a.2.1 = u.1 ∧ a.2.2.1 = d.1 }

/-- The schema of a context. -/
def schemaOf (c : M.Ctx) : Schema := (M.certificate.schema? c.1).getD emptySchema

/-- The translation of an arrow. -/
def translationOf {u d : M.Ctx} (f : u ⟶ d) : Translation := f.1.2.2.2

/-! ## Route equations -/

/-- The arrow named `n` out of the context `u`, when its target is a context. -/
def arrow? (u : M.Ctx) (n : String) : Option (Σ d : M.Ctx, u ⟶ d) :=
  M.arrows.attach.findSome? fun a =>
    if h : a.1.1 = n ∧ a.1.2.1 = u.1 ∧ a.1.2.2.1 ∈ M.names then
      some ⟨⟨a.1.2.2.1, h.2.2⟩, ⟨a.1, a.2, h.2.1, rfl⟩⟩
    else none

/-- The route out of `u` that continues `cur` along the arrows named in the list. -/
def path? (u : M.Ctx) :
    (Σ d : M.Ctx, Quiver.Path u d) → List String → Option (Σ d : M.Ctx, Quiver.Path u d)
  | cur, [] => some cur
  | cur, n :: ns => (M.arrow? cur.1 n).bind fun f => path? u ⟨f.1, cur.2.cons f.2⟩ ns

/-- The context a declared equation starts at: the source of its first arrow. -/
def source? (e : List String × List String) : Option M.Ctx :=
  (e.1 ++ e.2).head?.bind fun n => (M.arrows.find? fun a => a.1 == n).bind fun a =>
    if h : a.2.1 ∈ M.names then some ⟨a.2.1, h⟩ else none

/-- A declared equation as an equation between two routes with the same endpoints,
when its two lists of arrow names are such routes. -/
def routeEqn? (e : List String × List String) : Option (RouteEqn M.Ctx) :=
  (M.source? e).bind fun u =>
    (M.path? u ⟨u, .nil⟩ e.1).bind fun p => (M.path? u ⟨u, .nil⟩ e.2).bind fun q =>
      if h : q.1 = p.1 then some ⟨u, p.1, p.2, h ▸ q.2⟩ else none

/-- A declared equation names two routes whose composite translations induce the
same functor. -/
def routeOk (e : List String × List String) : Bool :=
  match M.routeEqn? e with
  | some r => checkRouteEqn M.valueTypes M.schemaOf (@translationOf M) r
  | none => false

def checkRoutes : Bool := M.routeEqns.all M.routeOk

/-- The check of a context map document: the claims of its certificate and the
conditions on the map. -/
def check : Bool :=
  M.certificate.check && M.checkNames && M.checkKernels && M.checkPublished &&
    M.checkAcyclic && M.checkRoutes

/-! ## A document that passes is a context map -/

section Sound

variable {M}

theorem check_certificate (h : M.check = true) : M.certificate.check = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

theorem sound (h : M.check = true) : M.valueTypes.Sound :=
  M.certificate.check_sound (check_certificate h) .valueTypes
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_singleton_self _))))

theorem wellFormedOf (h : M.check = true) (c : M.Ctx) : (M.schemaOf c).WellFormed := by
  obtain ⟨ctx, hctx, hn⟩ := List.mem_map.mp c.2
  obtain ⟨S, hS, hw⟩ := M.certificate.check_sound (check_certificate h) (.wellFormed ctx.1)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨ctx, hctx, List.mem_cons_self⟩))))
  rw [hn] at hS
  simp only [schemaOf, hS, Option.getD_some]
  exact hw

theorem validOf (h : M.check = true) {u d : M.Ctx} (f : u ⟶ d) :
    (M.translationOf f).VValid M.valueTypes (M.schemaOf u) (M.schemaOf d) := by
  obtain ⟨a, ha, hu, hd⟩ := f
  obtain ⟨S, S', hS, hS', hv⟩ := M.certificate.check_sound (check_certificate h)
    (.translation a.2.1 a.2.2.1 a.2.2.2)
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩)))
  simp only [schemaOf, translationOf, ← hu, ← hd, hS, hS', Option.getD_some]
  exact hv

/-- The equations between routes that a document declares. -/
def routeEqnList (M : MapDoc) : List (RouteEqn M.Ctx) := M.routeEqns.filterMap M.routeEqn?

theorem routeEqnList_check (h : M.check = true) :
    ∀ e ∈ M.routeEqnList, checkRouteEqn M.valueTypes M.schemaOf (@translationOf M) e = true := by
  intro e he
  obtain ⟨e₀, he₀, hr⟩ := List.mem_filterMap.mp he
  simp only [check, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 e₀ he₀
  simpa [routeOk, hr] using this

/-- A document that passes its check, as a context map on its contexts: its
schemas and translations, its declared route equations and its kernels. -/
def contextMap (h : M.check = true) : ContextMap M.Ctx where
  valueTypes := M.valueTypes
  sound := sound h
  schema := M.schemaOf
  translation := @translationOf M
  wellFormed := wellFormedOf h
  valid := fun f => validOf h f
  routeEqns := RouteEqn.rel M.routeEqnList
  coherent := coherent_of_check (wellFormedOf h) (fun f => validOf h f) M.routeEqnList
    (routeEqnList_check h)
  kernel := fun c => M.isKernel c.1
  inclusion := by
    rintro u d ⟨a, ha, hu, hd⟩ hk
    simp only [check, Bool.and_eq_true] at h
    have := List.all_eq_true.mp h.1.1.1.2 a ha
    simp only [kernelOk, hu, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    rcases this with hn | he
    · rw [hn] at hk
      cases hk
    · exact he

/-- The ranks increase along the arrows of a document that passes its check. -/
theorem rank_lt (h : M.check = true) {u d : M.Ctx} (f : u ⟶ d) : M.rank u.1 < M.rank d.1 := by
  obtain ⟨a, ha, hu, hd⟩ := f
  simp only [check, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.1.2 a ha
  simp only [rankOk, hu, hd, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq] at this
  rcases this with (hn | hn) | hlt
  · exact absurd (List.elem_eq_true_of_mem u.2) (by simpa using hn)
  · exact absurd (List.elem_eq_true_of_mem d.2) (by simpa using hn)
  · exact hlt

/-- Lax non-interference for a document that passes its check: each context embeds
into the lax integration fully faithfully and injectively on objects. -/
theorem nonInterference (h : M.check = true) (c : M.Ctx) :
    ((contextMap h).embed c).Full ∧ ((contextMap h).embed c).Faithful ∧
      Function.Injective ((contextMap h).embed c).obj :=
  (contextMap h).nonInterference
    ((contextMap h).endo_eq_id (endo_eq_id_of_rank (fun c : M.Ctx => M.rank c.1) (rank_lt h))) c

/-- An arrow marked as publishing presents its source as a published language of
its target. -/
theorem publishes (h : M.check = true) {u d : M.Ctx} (f : u ⟶ d)
    (hp : f.1.1 ∈ M.published) : (contextMap h).Publishes f := by
  obtain ⟨a, ha, hu, hd⟩ := f
  simp only [check, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.1.1.2 a ha
  have hc : M.published.contains a.1 = true := List.elem_eq_true_of_mem hp
  simp only [publishOk, hc, Bool.not_true, Bool.false_or] at this
  change ((M.schemaOf u).entities.map a.2.2.2.ent).Nodup ∧
    a.2.2.2.RootsOnly (M.schemaOf u) (M.schemaOf d)
  simp only [schemaOf, ← hu, ← hd]
  split at this
  · rename_i P S hP hS
    simpa [hP, hS] using this
  · exact absurd this (by simp)

end Sound

/-! ## The report -/

/-- The problem of an arrow out of a kernel whose translation is not empty. -/
def kernelProblems (a : Arrow) : List Json :=
  if M.kernelOk a then [] else
    [problemJson "kernelTranslation" [("arrow", .str a.1), ("kernel", .str a.2.1)]
      s!"{a.2.1} is a shared kernel, so the arrow {a.1} out of it must keep every name: its \
        translation lists images"]

/-- The problems of a publishing arrow: entity types of its source that go to the
same entity type, and entity types that go to a member of an aggregate. -/
def publishProblems (a : Arrow) : List Json :=
  if M.publishOk a then [] else
    match M.certificate.schema? a.2.1, M.certificate.schema? a.2.2.1 with
    | some P, some S =>
      let T := a.2.2.2
      (P.entities.filter fun e => (P.entities.filter fun e' => T.ent e' == T.ent e).length > 1).map
        (fun e => problemJson "entitiesMerged" [("arrow", .str a.1), ("entity", .str e),
          ("image", .str (T.ent e))]
          s!"{a.2.1} is published by {a.2.2.1}, but {e} and another of its entity types both go \
            to {T.ent e}") ++
      (P.entities.filterMap fun e =>
        (S.aggregates.find? fun A => (A.members.map (·.entity)).contains (T.ent e)).map fun A =>
          problemJson "publishedMember" [("arrow", .str a.1), ("entity", .str e),
            ("image", .str (T.ent e)), ("root", .str A.root)]
            s!"{a.2.1} is published by {a.2.2.1}, but {e} goes to {T.ent e}, a member of the \
              aggregate {A.root}: a published language contains roots only")
    | _, _ => []

/-- The names of contexts and of arrows that are declared more than once. -/
def nameProblems : List Json :=
  (M.names.filter fun n => M.names.count n > 1).eraseDups.map (fun n =>
    problemJson "duplicateContext" [("context", .str n)]
      s!"the context {n} is declared more than once") ++
  ((M.arrows.map (·.1)).filter fun n => (M.arrows.map (·.1)).count n > 1).eraseDups.map fun n =>
    problemJson "duplicateArrow" [("arrow", .str n)] s!"the arrow {n} is declared more than once"

/-- The arrows along which the rank does not increase: they lie on a cycle or lead
out of one. -/
def cycleProblems : List Json :=
  match (M.arrows.filter fun a => !M.rankOk a).map (·.1) with
  | [] => []
  | as => [problemJson "cycle" [("arrows", Lean.toJson as)]
    s!"the map has a cycle: the arrows {", ".intercalate as} lie on one or lead out of one"]

/-- The event types whose context the document does not have. -/
def eventProblems : List Json :=
  (M.events.filter fun e => !M.names.contains e.1).map fun e =>
    problemJson "unknownSchema" [("schema", .str e.1), ("event", .str e.2.name)]
      s!"the event type {e.2.name} is published by {e.1}, which is not a context"

/-- The declared route equations that do not hold. -/
def routeProblems : List Json :=
  (M.routeEqns.filter fun e => !M.routeOk e).map fun e =>
    problemJson "routeEquation" [("lhs", Lean.toJson e.1), ("rhs", Lean.toJson e.2)]
      (if (M.routeEqn? e).isNone then
        s!"{pathText e.1} and {pathText e.2} are not two routes between the same contexts"
      else s!"the routes {pathText e.1} and {pathText e.2} have different composite translations")

/-- The conditions on the map, each with a sentence, its check and its problems. -/
def conditions : List (String × Bool × List Json) :=
  [("the names of the contexts and of the arrows are distinct", M.checkNames, M.nameProblems),
   ("every arrow out of a shared kernel keeps names", M.checkKernels,
     M.arrows.flatMap M.kernelProblems),
   ("every published language keeps its entity types apart and goes to roots", M.checkPublished,
     M.arrows.flatMap M.publishProblems),
   ("the map has no cycle", M.checkAcyclic, M.cycleProblems),
   ("the declared route equations hold", M.checkRoutes, M.routeProblems)]

/-- The conditions on the map as a whole hold. -/
def mapOk : Bool :=
  M.checkNames && M.checkAcyclic && M.checkRoutes && M.eventProblems.isEmpty

/-- The report of a context map document: the list of value types, each context
with the problems of its well-formedness and of its value types, each arrow with
the problems of its claims and of its kernel and publishing conditions, and the
map with the problems of its names, cycles and route equations. -/
def report : Json :=
  let c := M.certificate
  let (typesOk, typeProblems) := c.result .valueTypes
  let valueTypes := Json.mkObj [("ok", .bool typesOk),
    ("problems", Json.arr typeProblems.toArray)]
  let contexts := M.contexts.map fun ctx =>
    let (ok₁, ps₁) := c.result (.wellFormed ctx.1)
    let (ok₂, ps₂) := c.result (.declared ctx.1)
    let evs := (M.events.filter fun e => e.1 == ctx.1).map fun e => c.result (.eventType e.1 e.2)
    Json.mkObj [("name", .str ctx.1), ("ok", .bool (ok₁ && ok₂ && evs.all (·.1))),
      ("problems", Json.arr (ps₁ ++ ps₂ ++
        (evs.flatMap (·.2)).filter fun p => !ps₁.contains p).toArray)]
  let arrows := M.arrows.map fun a =>
    let (ok₁, ps₁) := c.result (.translation a.2.1 a.2.2.1 a.2.2.2)
    let (ok₂, ps₂) := c.result (.keysKept a.2.1 a.2.2.1 a.2.2.2)
    Json.mkObj [("name", .str a.1), ("source", .str a.2.1), ("target", .str a.2.2.1),
      ("ok", .bool (ok₁ && ok₂ && M.kernelOk a && M.publishOk a)),
      ("problems", Json.arr (ps₁ ++ (ps₂.filter fun p => !ps₁.contains p) ++
        M.kernelProblems a ++ M.publishProblems a).toArray)]
  let map := Json.mkObj [("ok", .bool M.mapOk),
    ("problems", Json.arr (M.nameProblems ++ M.cycleProblems ++ M.routeProblems ++
      M.eventProblems).toArray)]
  let failed := (valueTypes :: map :: contexts ++ arrows).filter fun j =>
    j.getObjValD "ok" != .bool true
  Json.mkObj [("format", .str formatVersion), ("kind", .str "mapReport"),
    ("valueTypes", valueTypes), ("contexts", Json.arr contexts.toArray),
    ("arrows", Json.arr arrows.toArray), ("map", map),
    ("failed", (failed.length : Nat))]

end MapDoc

end DDD
