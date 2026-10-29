import DDD.Open

/-!
# Qualified names

Open schemas compose only when they share no name outside the shared interface.
Qualification renames the entity types and generators of a schema that an
interface does not have, by prefixing a name, usually that of the context: in a
second ordering context, `Order` becomes `Store.Order` and its generator
`customer` becomes `Store.customer`. The Julia side qualifies clashing generators
the same way.

- `Schema.qualify keep p S`: `S` with the names that `keep` does not have
  qualified by `p`. `qualifyTranslation` and `unqualifyTranslation` translate
  between `S` and its qualification.
- `Translation.catIso`: translations both ways whose functors compose to the
  identity both ways give an isomorphism of schema categories.
  `functor_comp_eq_id` derives such a composite from `checkSameFunctor`, and
  `functor_empty_comp_eq` the commutation with an inclusion.
- `OpenSchema.Iso`: translations both ways between the schemas of two open
  schemas with the same interfaces, inverse to each other and commuting with
  the legs; `Iso.catIso` is the isomorphism of schema categories.
- `OpenSchema.qualify`: an open schema with the names outside its interfaces
  qualified, when `checkQualify` passes, and `qualifyIso`, its isomorphism with
  the original.
-/

namespace DDD

open CategoryTheory Schema

namespace Schema

variable (keep : Schema) (p : String)

/-- The entity type `e`, qualified by `p` unless `keep` has it. -/
def qualifyEnt (e : String) : String := if e ∈ keep.entities then e else p ++ "." ++ e

/-- The generator `n` out of `e`, qualified by `p` unless `keep` has it. -/
def qualifyGen (e n : String) : String := if (e, n) ∈ keep.gens then n else p ++ "." ++ n

/-- The translation from `S` to its qualification. -/
def qualifyTranslation (S : Schema) : Translation where
  entities := S.entities.map fun e => (e, qualifyEnt keep p e)
  gens := S.gens.map fun g => ⟨g.1, g.2, [qualifyGen keep p g.1 g.2]⟩

/-- The translation from the qualification of `S` back to `S`. -/
def unqualifyTranslation (S : Schema) : Translation where
  entities := S.entities.map fun e => (qualifyEnt keep p e, e)
  gens := S.gens.map fun g => ⟨qualifyEnt keep p g.1, qualifyGen keep p g.1 g.2, [g.2]⟩

/-- `S` with the names that `keep` does not have qualified by `p`. -/
def qualify (S : Schema) : Schema where
  entities := S.entities.map (qualifyEnt keep p)
  refs := S.refs.map fun r =>
    ⟨qualifyGen keep p r.src r.name, qualifyEnt keep p r.src, qualifyEnt keep p r.tgt⟩
  attrs := S.attrs.map fun a => ⟨qualifyGen keep p a.src a.name, qualifyEnt keep p a.src, a.tgt⟩
  eqns := S.eqns.map fun q =>
    ⟨qualifyEnt keep p q.src, (qualifyTranslation keep p S).mapPath S (.entity q.src) q.lhs,
      (qualifyTranslation keep p S).mapPath S (.entity q.src) q.rhs⟩
  aggregates := S.aggregates.map fun A =>
    ⟨qualifyEnt keep p A.root,
      A.members.map fun m => ⟨qualifyEnt keep p m.entity, qualifyGen keep p m.entity m.owner⟩⟩
  valueObjects := S.valueObjects.map (qualifyEnt keep p)

end Schema

namespace Translation

variable {I S S' : Schema} {T U : Translation}

/-- Translations both ways whose functors compose to the identity both ways give an
isomorphism of schema categories. -/
def catIso (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S') (hU : U.Valid S' S)
    (h₁ : functor hS' hT ⋙ functor hS hU = 𝟭 _) (h₂ : functor hS hU ⋙ functor hS' hT = 𝟭 _) :
    S.cat ≅ S'.cat where
  hom := functor hS' hT
  inv := functor hS hU
  hom_inv_id := h₁
  inv_hom_id := h₂

/-- `T` followed by `U` induces the identity functor when the composite translation
and the empty translation pass `checkSameFunctor`. -/
theorem functor_comp_eq_id (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    (hU : U.Valid S' S) {peq : Ob → List String → List String → Bool}
    (hpeq : ∀ (a : S.Obj) (l l' : List String), peq a.1 l l' = true → S.PathEq a l l')
    (h : (T.comp S S' U).checkSameFunctor {} S peq = true) :
    functor hS' hT ⋙ functor hS hU = 𝟭 _ := by
  rw [← functor_comp hS hS' hS hT hU,
    checkSameFunctor_sound hS (comp_valid hS hS hT hU) (empty_valid_self hS) hpeq h,
    functor_empty_self]

/-- An inclusion followed by `T` is an inclusion when the composite translation and
the empty translation pass `checkSameFunctor`. -/
theorem functor_empty_comp_eq (hI : I.WellFormed) (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hi : ({} : Translation).Valid I S) (hT : T.Valid S S') (hi' : ({} : Translation).Valid I S')
    {peq : Ob → List String → List String → Bool}
    (hpeq : ∀ (a : S'.Obj) (l l' : List String), peq a.1 l l' = true → S'.PathEq a l l')
    (h : (({} : Translation).comp I S T).checkSameFunctor {} I peq = true) :
    functor hS hi ⋙ functor hS' hT = functor hS' hi' := by
  rw [← functor_comp hI hS hS' hi hT]
  exact checkSameFunctor_sound hS' (comp_valid hI hS' hi hT) hi' hpeq h

end Translation

namespace OpenSchema

variable {I O : Schema}

/-- An isomorphism of open schemas with the same interfaces: translations both ways
between their schemas, whose functors are inverse to each other and commute
with the legs. -/
structure Iso (X Y : OpenSchema I O) where
  T : Translation
  U : Translation
  validT : T.Valid X.S Y.S
  validU : U.Valid Y.S X.S
  hom_inv : Translation.functor Y.wf validT ⋙ Translation.functor X.wf validU = 𝟭 _
  inv_hom : Translation.functor X.wf validU ⋙ Translation.functor Y.wf validT = 𝟭 _
  legI : X.legI ⋙ Translation.functor Y.wf validT = Y.legI
  legO : X.legO ⋙ Translation.functor Y.wf validT = Y.legO

/-- The isomorphism of schema categories of an isomorphism of open schemas. -/
def Iso.catIso {X Y : OpenSchema I O} (e : X.Iso Y) : X.S.cat ≅ Y.S.cat :=
  Translation.catIso X.wf Y.wf e.validT e.validU e.hom_inv e.inv_hom

variable (X : OpenSchema I O) (p : String)

/-- The schema of `X` with the names outside both interfaces qualified by `p`. -/
abbrev qualifiedSchema : Schema := Schema.qualify (glue I O) p X.S

/-- The checks for qualifying `X` by `p`: the qualified schema is well-formed and
includes both interfaces, which contain roots only in it; the translations both
ways are valid, compose to the identity both ways, and fix the interfaces. -/
def checkQualify : Bool :=
  (X.qualifiedSchema p).checkWellFormed &&
  ({} : Translation).checkValid I (X.qualifiedSchema p) (X.qualifiedSchema p).pathEq &&
  ({} : Translation).checkValid O (X.qualifiedSchema p) (X.qualifiedSchema p).pathEq &&
  I.checkRootsOnly (X.qualifiedSchema p) && O.checkRootsOnly (X.qualifiedSchema p) &&
  (qualifyTranslation (glue I O) p X.S).checkValid X.S (X.qualifiedSchema p)
    (X.qualifiedSchema p).pathEq &&
  (unqualifyTranslation (glue I O) p X.S).checkValid (X.qualifiedSchema p) X.S X.S.pathEq &&
  ((qualifyTranslation (glue I O) p X.S).comp X.S (X.qualifiedSchema p)
    (unqualifyTranslation (glue I O) p X.S)).checkSameFunctor {} X.S X.S.pathEq &&
  ((unqualifyTranslation (glue I O) p X.S).comp (X.qualifiedSchema p) X.S
    (qualifyTranslation (glue I O) p X.S)).checkSameFunctor {} (X.qualifiedSchema p)
      (X.qualifiedSchema p).pathEq &&
  (({} : Translation).comp I X.S (qualifyTranslation (glue I O) p X.S)).checkSameFunctor {} I
    (X.qualifiedSchema p).pathEq &&
  (({} : Translation).comp O X.S (qualifyTranslation (glue I O) p X.S)).checkSameFunctor {} O
    (X.qualifiedSchema p).pathEq

variable {X p} (h : X.checkQualify p = true)

include h in
theorem checkQualify_spec :
    (X.qualifiedSchema p).WellFormed ∧
    ({} : Translation).Valid I (X.qualifiedSchema p) ∧
    ({} : Translation).Valid O (X.qualifiedSchema p) ∧
    I.RootsOnly (X.qualifiedSchema p) ∧ O.RootsOnly (X.qualifiedSchema p) ∧
    (qualifyTranslation (glue I O) p X.S).Valid X.S (X.qualifiedSchema p) ∧
    (unqualifyTranslation (glue I O) p X.S).Valid (X.qualifiedSchema p) X.S := by
  simp only [checkQualify, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwf, hI⟩, hO⟩, hrI⟩, hrO⟩, hT⟩, hU⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hwf' := (checkWellFormed_iff _).mp hwf
  exact ⟨hwf', Translation.checkValid_sound (fun a _ _ h => pathEq_sound hwf' a h) hI,
    Translation.checkValid_sound (fun a _ _ h => pathEq_sound hwf' a h) hO,
    (checkRootsOnly_iff _ _).mp hrI, (checkRootsOnly_iff _ _).mp hrO,
    Translation.checkValid_sound (fun a _ _ h => pathEq_sound hwf' a h) hT,
    Translation.checkValid_sound (fun a _ _ h => pathEq_sound X.wf a h) hU⟩

/-- `X` with the names outside its interfaces qualified by `p`. -/
def qualify : OpenSchema I O where
  S := X.qualifiedSchema p
  wfI := X.wfI
  wfO := X.wfO
  wf := (checkQualify_spec h).1
  inI := (checkQualify_spec h).2.1
  inO := (checkQualify_spec h).2.2.1
  rootsI := (checkQualify_spec h).2.2.2.1
  rootsO := (checkQualify_spec h).2.2.2.2.1

/-- `X` and its qualification are isomorphic open schemas. -/
def qualifyIso : X.Iso (X.qualify h) := by
  have hc := h
  simp only [checkQualify, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h₁⟩, h₂⟩, hlI⟩, hlO⟩ := hc
  have hwf' := (checkQualify_spec h).1
  exact
    { T := qualifyTranslation (glue I O) p X.S
      U := unqualifyTranslation (glue I O) p X.S
      validT := (checkQualify_spec h).2.2.2.2.2.1
      validU := (checkQualify_spec h).2.2.2.2.2.2
      hom_inv := Translation.functor_comp_eq_id X.wf hwf' _ _
        (fun a _ _ h => pathEq_sound X.wf a h) h₁
      inv_hom := Translation.functor_comp_eq_id hwf' X.wf _ _
        (fun a _ _ h => pathEq_sound hwf' a h) h₂
      legI := Translation.functor_empty_comp_eq X.wfI X.wf hwf' _ _ _
        (fun a _ _ h => pathEq_sound hwf' a h) hlI
      legO := Translation.functor_empty_comp_eq X.wfO X.wf hwf' _ _ _
        (fun a _ _ h => pathEq_sound hwf' a h) hlO }

end OpenSchema

end DDD
