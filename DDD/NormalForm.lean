import DDD.Rename

/-!
# The normal form of a translation

A translation `T` from `S` to `S'` that keeps the entity types of `S` apart factors
as an inclusion into a definitional extension of `S'` (`Translation.ext T S S'`):
`S'` with the image `T e` of each entity type of `S` renamed `e`, and, for each
generator `g` of `S` whose image is not the generator of the same name, a derived
generator `g` with the equation `g = T g`. `S` includes into the extension by the
empty translation, so gluing, open schemas and the roots-only check, which take
inclusions, apply to it.

- `Translation.toTarget`: the translation from the extension to `S'`, each derived
  generator to its image and each entity type back to its name in `S'`;
  `fromTarget`: the translation from `S'` to the extension, renaming.
- `checkNormalForm`: `T` keeps entity types apart, the extension is well formed,
  the inclusion and both translations are valid, the two translations compose to
  the identity both ways, and the inclusion followed by `toTarget` is `T`, each by
  `Translation.checkSameFunctor`.
- `normalForm`: when the check passes, the extension presents a category
  isomorphic to that of `S'` (`NormalForm.iso`), and the functor of `T` is the
  inclusion followed by the isomorphism (`NormalForm.factor`).

The isomorphism is proved for each translation that passes the check. A
translation that sends two entity types to one fails it, and a translation that
converts has no normal form: its derived equations would end in conversions.
-/

namespace DDD

open CategoryTheory Schema

namespace Translation

variable (T : Translation) (S S' : Schema)

/-- The name in the extension of the entity type `x` of `S'`: the entity type of
`S` that goes to `x`, or `x`. -/
def extEnt (x : String) : String :=
  (S.entities.find? fun e => T.ent e == x).getD x

/-- The generator `n` out of `e` is derived: its image is not the generator of the
same name. -/
def derived (e n : String) : Bool := T.gen (.entity e) n != [n]

/-- The derived generators of `S`, by source and name. -/
def derivedGens : List (String × String) := S.gens.filter fun g => T.derived g.1 g.2

/-- The definitional extension of `S'` along `T`: `S'` with the images of the entity
types of `S` renamed after them, a derived generator for each generator of `S`
whose image is not the generator of the same name, and its defining equation. -/
def ext : Schema where
  entities := S'.entities.map (T.extEnt S)
  refs := S'.refs.map (fun r => ⟨r.name, T.extEnt S r.src, T.extEnt S r.tgt⟩) ++
    S.refs.filter fun r => T.derived r.src r.name
  attrs := S'.attrs.map (fun a => ⟨a.name, T.extEnt S a.src, a.tgt⟩) ++
    S.attrs.filter fun a => T.derived a.src a.name
  eqns := S'.eqns.map (fun q => ⟨T.extEnt S q.src, q.lhs, q.rhs⟩) ++
    (T.derivedGens S).map fun g => ⟨g.1, [g.2], T.gen (.entity g.1) g.2⟩
  aggregates := S'.aggregates.map fun A =>
    ⟨T.extEnt S A.root, A.members.map fun m => ⟨T.extEnt S m.entity, m.owner⟩⟩
  valueObjects := S'.valueObjects.map (T.extEnt S)
  keys := S'.keys.map fun k => ⟨T.extEnt S k.entity, k.fields⟩
  subtypes := S'.subtypes.map fun s => ⟨T.extEnt S s.entity, s.ref⟩

/-- The translation from the extension to `S'`: each entity type back to its name
in `S'`, each derived generator to its image. -/
def toTarget : Translation where
  entities := S'.entities.map fun x => (T.extEnt S x, x)
  gens := (T.derivedGens S).map fun g => ⟨g.1, g.2, T.gen (.entity g.1) g.2⟩

/-- The translation from `S'` to the extension: each entity type to its name in the
extension. -/
def fromTarget : Translation where
  entities := S'.entities.map fun x => (x, T.extEnt S x)

/-- The check that `T` factors through its definitional extension. -/
def checkNormalForm : Bool :=
  decide (S.entities.map T.ent).Nodup && (T.ext S S').checkWellFormed &&
  ({} : Translation).checkValid S (T.ext S S') (T.ext S S').pathEq &&
  (T.toTarget S S').checkValid (T.ext S S') S' S'.pathEq &&
  (T.fromTarget S S').checkValid S' (T.ext S S') (T.ext S S').pathEq &&
  ((T.toTarget S S').comp (T.ext S S') S' (T.fromTarget S S')).checkSameFunctor {}
    (T.ext S S') (T.ext S S').pathEq &&
  ((T.fromTarget S S').comp S' (T.ext S S') (T.toTarget S S')).checkSameFunctor {} S'
    S'.pathEq &&
  (({} : Translation).comp S (T.ext S S') (T.toTarget S S')).checkSameFunctor T S S'.pathEq

variable {S S'}

/-- The normal form of a translation: the inclusion of `S` into the definitional
extension, the isomorphism of the extension with `S'`, and the factorization of
the functor of `T`. -/
structure NormalForm (hS' : S'.WellFormed) (hT : T.Valid S S') where
  wf : (T.ext S S').WellFormed
  incl : ({} : Translation).Valid S (T.ext S S')
  iso : (T.ext S S').cat ≅ S'.cat
  factor : functor wf incl ⋙ iso.hom = functor hS' hT

variable {T}

/-- When the check passes, `T` has a normal form. -/
def normalForm (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    (h : T.checkNormalForm S S' = true) : T.NormalForm hS' hT :=
  have hc := h
  have hwf : (T.ext S S').WellFormed := by
    simp only [checkNormalForm, Bool.and_eq_true] at hc
    exact (checkWellFormed_iff _).mp hc.1.1.1.1.1.1.2
  have hpE : ∀ (a : (T.ext S S').Obj) (l l' : List String),
      (T.ext S S').pathEq a.1 l l' = true → (T.ext S S').PathEq a l l' :=
    fun a _ _ hp => pathEq_sound hwf a hp
  have hpS' : ∀ (a : S'.Obj) (l l' : List String),
      S'.pathEq a.1 l l' = true → S'.PathEq a l l' :=
    fun a _ _ hp => pathEq_sound hS' a hp
  have parts := hc
  by
    simp only [checkNormalForm, Bool.and_eq_true] at parts
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hi⟩, hto⟩, hfrom⟩, h₁⟩, h₂⟩, h₃⟩ := parts
    have hincl := checkValid_sound hpE hi
    have hTo := checkValid_sound hpS' hto
    have hFrom := checkValid_sound hpE hfrom
    exact
      { wf := hwf
        incl := hincl
        iso := catIso hwf hS' hTo hFrom (functor_comp_eq_id hwf hS' hTo hFrom hpE h₁)
          (functor_comp_eq_id hS' hwf hFrom hTo hpS' h₂)
        factor := by
          change functor hwf hincl ⋙ functor hS' hTo = functor hS' hT
          rw [← functor_comp hS hwf hS' hincl hTo]
          exact checkSameFunctor_sound hS' (comp_valid hS hS' hincl hTo) hT hpS' h₃ }

end Translation

end DDD
