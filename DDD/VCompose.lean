import DDD.Compose
import DDD.ConvComplete

/-!
# Composite translations with conversions

The composite of translations valid with conversions, and the equality of their
functors between the categories with conversions.

- `Translation.vcomp T S S' L U`: as `Translation.comp`, with the image under `U`
  of each image path taken through the conversions (`Translation.vmapPath`). It is
  valid with conversions (`vcomp_vvalid`), and its functor is the composite of the
  functors (`vfunctor_vcomp`).
- The functor of the empty translation from a schema to itself is the identity
  (`vfunctor_empty_self`).
- `Translation.checkSameFunctor` with a procedure for path equality in `S'.vcat L`
  decides the equality of the functors with conversions (`checkSameFunctor_vsound`,
  `checkSameFunctor_viff`).
-/

namespace DDD

open CategoryTheory

namespace Schema

variable {S : Schema} {L : TypeList}

/-- The object map of `Schema.vobj` is injective. -/
theorem vobj_injective {a b : S.VObj L} (h : S.vobj L a = S.vobj L b) : a = b :=
  congrArg (fun x : CategoryTheory.Quotient (S.vrel L) => x.as) h

/-- Paths with the same names present the same morphism, up to the equalities of
their endpoints. -/
theorem vmor_eq_of_vnames {a a' b b' : S.VObj L} (ha : a = a') (hb : b = b')
    (p : Quiver.Path a b) (p' : Quiver.Path a' b') (h : vnames p = vnames p') :
    vmor p = eqToHom (congrArg (S.vobj L) ha) ≫ vmor p' ≫
      eqToHom (congrArg (S.vobj L) hb).symm := by
  subst ha hb
  obtain rfl := vnames_injective p p' h
  simp

/-- Paths whose names satisfy `VPathEq` present the same morphism, up to equalities
of their endpoints. -/
theorem vmor_eq_of_vPathEq {a a' b b' : S.VObj L} (ha : a = a') (hb : b = b')
    (p : Quiver.Path a b) (p' : Quiver.Path a' b') (h : S.VPathEq L a (vnames p) (vnames p')) :
    vmor p = eqToHom (congrArg (S.vobj L) ha) ≫ vmor p' ≫
      eqToHom (congrArg (S.vobj L) hb).symm := by
  subst ha hb
  simpa using VPathEq.vmor_eq h

/-- Paths that present the same morphism, up to equalities of their endpoints,
satisfy `VPathEq`. -/
theorem vPathEq_of_vmor_eq {a a' b b' : S.VObj L} (ha : a = a') (hb : b = b')
    (p : Quiver.Path a b) (p' : Quiver.Path a' b')
    (h : vmor p = eqToHom (congrArg (S.vobj L) ha) ≫ vmor p' ≫
      eqToHom (congrArg (S.vobj L) hb).symm) :
    S.VPathEq L a (vnames p) (vnames p') := by
  subst ha hb
  exact ⟨b, p, p', rfl, rfl, by simpa using h⟩

end Schema

namespace Translation

open Schema

variable {S S' S'' : Schema} {L : TypeList}

/-! ## Images of paths -/

/-- A path of generators and conversions goes to a path between the images of its
endpoints. -/
theorem VValid.vtgt?_vmapPath {T : Translation} (hT : T.VValid L S S') :
    ∀ {o x : Ob} {l : List String}, S.vtgt? L o l = some x →
      S'.vtgt? L (T.ob o) (T.vmapPath S L o l) = some (T.ob x)
  | _, _, [], h => by cases h; rfl
  | o, x, n :: ns, h => by
    cases hs : S.vstep? L o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [vtgt?_cons, hs, Option.bind_some] at h
      simp only [vmapPath, hs]
      rw [vtgt?_append, hT.vtgt?_gen hs, Option.bind_some]
      exact VValid.vtgt?_vmapPath hT h

/-- A generator between entity types goes to a path of `S'`. -/
theorem VValid.tgt?_gen_entity {T : Translation} (hT : T.VValid L S S') {o : Ob} {e n : String}
    (h : S.step? o n = some (.entity e)) :
    S'.tgt? (T.ob o) (T.gen o n) = some (T.ob (.entity e)) := by
  cases o with
  | value => simp [Schema.step?] at h
  | entity e₀ =>
    simp only [Schema.step?] at h
    split at h
    · rename_i r hr
      cases h
      unfold Schema.ref? at hr
      have hp := List.find?_some hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hT.ref r (List.mem_of_find?_eq_some hr)
    · obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp h
      cases ha

/-- A path of `S` between entity types goes to a path of `S'`. -/
theorem VValid.tgt?_mapPath_entity {T : Translation} (hT : T.VValid L S S') :
    ∀ {o : Ob} {e : String} {l : List String}, S.tgt? o l = some (.entity e) →
      S'.tgt? (T.ob o) (T.mapPath S o l) = some (T.ob (.entity e))
  | _, _, [], h => by cases h; rfl
  | o, e, n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      cases o' with
      | value v => cases ns <;> simp [Schema.step?] at h
      | entity e₁ =>
        simp only [mapPath, hs]
        rw [Schema.tgt?_append, hT.tgt?_gen_entity hs, Option.bind_some]
        exact VValid.tgt?_mapPath_entity hT h

/-! ## The composite -/

/-- The composite of `T` from `S` to `S'` and `U` out of `S'`, with conversions: the
images of the entity types and generators of `S`, listed. -/
def vcomp (T : Translation) (S S' : Schema) (L : TypeList) (U : Translation) : Translation where
  entities := S.entities.map fun e => (e, U.ent (T.ent e))
  gens := (S.refs.map fun r => ⟨r.src, r.name,
      U.vmapPath S' L (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name)⟩) ++
    S.attrs.map fun a => ⟨a.src, a.name,
      U.vmapPath S' L (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name)⟩

variable (T U : Translation)

theorem vcomp_ent {e : String} (he : e ∈ S.entities) :
    (T.vcomp S S' L U).ent e = U.ent (T.ent e) :=
  comp_ent (S' := S') T U he

theorem vcomp_ob {o : Ob} (ho : S.IsOb o) : (T.vcomp S S' L U).ob o = U.ob (T.ob o) :=
  comp_ob (S' := S') T U ho

theorem vcomp_gen {o o' : Ob} {n : String} (h : S.step? o n = some o') :
    (T.vcomp S S' L U).gen o n = U.vmapPath S' L (T.ob o) (T.gen o n) := by
  obtain ⟨e, rfl, hg⟩ := Schema.exists_gen_of_step? h
  let F : String → String → List String := fun s m =>
    U.vmapPath S' L (T.ob (.entity s)) (T.gen (.entity s) m)
  have hall : ∀ g ∈ (T.vcomp S S' L U).gens, g.path = F g.src g.name := by
    intro g hg
    simp only [vcomp, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨r, -, rfl⟩ | ⟨a, -, rfl⟩ <;> rfl
  have hsome : ((T.vcomp S S' L U).gens.find? fun g => g.src == e && g.name == n).isSome := by
    rw [List.find?_isSome]
    rcases hg with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩), by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩), by simp⟩
  obtain ⟨g, hgf⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hgf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hc : (T.vcomp S S' L U).gen (.entity e) n = g.path := by
    simp only [gen, hgf, Option.map_some, Option.getD_some]
  rw [hc, hall g (List.mem_of_find?_eq_some hgf), hp.1, hp.2]

/-- A generator or a conversion goes to the image under `U` of its image under `T`. -/
theorem vcomp_vgen {o o' : Ob} {n : String} (h : S.vstep? L o n = some o') :
    (T.vcomp S S' L U).gen o n = U.vmapPath S' L (T.ob o) (T.gen o n) := by
  cases o with
  | entity e => exact vcomp_gen T U h
  | value v =>
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [gen, ob, vmapPath, vstep?, hw]

/-- The image of a path of `S` under the composite is the image under `U` of its
image under `T`. -/
theorem vcomp_mapPath {T : Translation} (U : Translation) (hT : T.VValid L S S') :
    ∀ {o x : Ob} {l : List String}, S.tgt? o l = some x →
      (T.vcomp S S' L U).mapPath S o l = U.vmapPath S' L (T.ob o) (T.mapPath S o l)
  | _, _, [], _ => rfl
  | o, x, n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      simp only [mapPath, hs]
      rw [vcomp_gen T U hs, vcomp_mapPath U hT h,
        vmapPath_append U (hT.vtgt?_gen (vstep?_of_step? hs))]

variable {T U}

/-- The composite of translations valid with conversions is valid with
conversions. -/
theorem vcomp_vvalid (hS : S.WellFormed) (hS' : S'.WellFormed) (hS'' : S''.WellFormed)
    (hT : T.VValid L S S') (hU : U.VValid L S' S'') : (T.vcomp S S' L U).VValid L S S'' where
  entity e he := by
    rw [vcomp_ent T U he]
    exact hU.entity _ (hT.entity e he)
  ref r hr := by
    have hs := Schema.step?_of_mem_refs hS hr
    rw [vcomp_ob T U (o := .entity r.src) (hS.ref_src r hr),
      vcomp_ob T U (o := .entity r.tgt) (hS.ref_tgt r hr), vcomp_gen T U hs,
      vmapPath_of_tgt? U (hT.ref r hr)]
    exact hU.tgt?_mapPath_entity (hT.ref r hr)
  attr a ha := by
    have hs := Schema.step?_of_mem_attrs hS ha
    rw [vcomp_ob T U (o := .entity a.src) (hS.attr_src a ha), vcomp_gen T U hs]
    exact hU.vtgt?_vmapPath (hT.attr a ha)
  eqn q hq := by
    have hsrc := hS.eqn_src q hq
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
    obtain ⟨hm, hpe⟩ := hT.eqn q hq
    have hpe' := hU.map_vPathEq hS' hS'' hpe
    have hent : (T.vcomp S S' L U).ent q.src = U.ent (T.ent q.src) := vcomp_ent T U hsrc
    refine ⟨hent ▸ hU.entity _ hm, ?_⟩
    rw [vcomp_mapPath U hT hl, vcomp_mapPath U hT hr]
    have hobj :
        (⟨.entity ((T.vcomp S S' L U).ent q.src), hent ▸ hU.entity _ hm⟩ : S''.VObj L) =
          U.vobj hU ⟨.entity (T.ent q.src), hm⟩ := Subtype.ext (by simp [vobj, ob, hent])
    rw [hobj]
    exact hpe'

/-- The functor of the composite is the composite of the functors. -/
theorem vfunctor_vcomp (hS : S.WellFormed) (hS' : S'.WellFormed) (hS'' : S''.WellFormed)
    (hT : T.VValid L S S') (hU : U.VValid L S' S'') :
    (T.vcomp S S' L U).vfunctor hS hS'' (vcomp_vvalid hS hS' hS'' hT hU) =
      T.vfunctor hS hS' hT ⋙ U.vfunctor hS' hS'' hU := by
  have hobj : ∀ a : S.VObj L,
      (T.vcomp S S' L U).vobj (vcomp_vvalid hS hS' hS'' hT hU) a = U.vobj hU (T.vobj hT a) :=
    fun a => Subtype.ext (vcomp_ob T U a.2)
  refine Schema.vext_functor (fun a => congrArg (S''.vobj L) (hobj a)) fun a b e => ?_
  rw [Functor.comp_map, vfunctor_map_vmor, vfunctor_map_vmor, vfunctor_map_vmor]
  apply Schema.vmor_eq_of_vnames (hobj a) (hobj b)
  rw [vnames_vfunctorPath, vnames_vfunctorPath, vnames_vfunctorPath, vnames_toPath,
    vmapPath_singleton, vmapPath_singleton, vcomp_vgen T U e.2]
  rfl

/-! ## The identity -/

/-- The functor of the empty translation from a schema to itself is the identity. -/
theorem vfunctor_empty_self (hS : S.WellFormed) (h : ({} : Translation).VValid L S S) :
    Translation.vfunctor {} hS hS h = 𝟭 _ := by
  have hobj : ∀ a : S.VObj L, Translation.vobj {} h a = a := fun a => Subtype.ext (ob_empty a.1)
  refine Schema.vext_functor (fun a => congrArg (S.vobj L) (hobj a)) fun a b e => ?_
  rw [vfunctor_map_vmor, Functor.id_map]
  apply Schema.vmor_eq_of_vnames (hobj a) (hobj b)
  rw [vnames_vfunctorPath, vnames_toPath, vmapPath_singleton, gen_empty]

/-- Equal translations induce equal functors with conversions. -/
theorem vfunctor_congr {T' : Translation} (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.VValid L S S') (hT' : T'.VValid L S S') (h : T = T') :
    T.vfunctor hS hS' hT = T'.vfunctor hS hS' hT' := by
  subst h
  rfl

/-! ## Equality of functors -/

variable {T T' : Translation} {peq : Ob → List String → List String → Bool}

/-- `checkSameFunctor` with path equality in `S'.vcat L` is sound for the functors
with conversions. -/
theorem checkSameFunctor_vsound (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.VValid L S S') (hT' : T'.VValid L S S')
    (hpeq : ∀ (a : S'.VObj L) (l l' : List String), peq a.1 l l' = true → S'.VPathEq L a l l')
    (h : T.checkSameFunctor T' S peq = true) :
    T.vfunctor hS hS' hT = T'.vfunctor hS hS' hT' := by
  simp only [checkSameFunctor, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨he, hr⟩, ha⟩ := h
  have hobj : ∀ a : S.VObj L, T.vobj hT a = T'.vobj hT' a := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    cases o with
    | value => rfl
    | entity e => simp only [vobj, ob, he e ho]
  refine Schema.vext_functor (fun a => congrArg (S'.vobj L) (hobj a)) fun a b e => ?_
  rw [vfunctor_map_vmor, vfunctor_map_vmor]
  apply Schema.vmor_eq_of_vPathEq (hobj a) (hobj b)
  rw [vnames_vfunctorPath, vnames_vfunctorPath, vnames_toPath, vmapPath_singleton,
    vmapPath_singleton]
  obtain ⟨⟨o⟩ | ⟨v⟩, hao⟩ := a
  · obtain ⟨x, hx, hg⟩ := Schema.exists_gen_of_step? (show S.step? (.entity o) e.1 = some b.1
      from e.2)
    generalize (e.1 : String) = n at hg ⊢
    obtain rfl : x = o := (Ob.entity.inj hx).symm
    rcases hg with ⟨r, hrm, hrs, hrn⟩ | ⟨t, htm, hts, htn⟩
    · exact hpeq (T.vobj hT ⟨.entity x, hao⟩) _ _ (by simpa [vobj, hrs, hrn] using hr r hrm)
    · exact hpeq (T.vobj hT ⟨.entity x, hao⟩) _ _ (by simpa [vobj, hts, htn] using ha t htm)
  · obtain ⟨w, hw, hb⟩ := Option.map_eq_some_iff.mp e.2
    simp only [gen]
    exact VPathEq.refl hS' (o := .value w) (by simp [vtgt?, vstep?, vobj, ob, hw])

/-- With a procedure that decides path equality in `S'.vcat L`, `checkSameFunctor`
decides the equality of the functors with conversions. -/
theorem checkSameFunctor_viff (hS : S.WellFormed) (hS' : S'.WellFormed)
    (hT : T.VValid L S S') (hT' : T'.VValid L S S')
    (hpeq : ∀ (a : S'.VObj L) (l l' : List String), peq a.1 l l' = true ↔ S'.VPathEq L a l l') :
    T.checkSameFunctor T' S peq = true ↔ T.vfunctor hS hS' hT = T'.vfunctor hS hS' hT' := by
  constructor
  · exact checkSameFunctor_vsound hS hS' hT hT' fun a l l' => (hpeq a l l').mp
  · intro hF
    simp only [checkSameFunctor, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    have hobj : ∀ a : S.VObj L, T.vobj hT a = T'.vobj hT' a := fun a =>
      Schema.vobj_injective (Functor.congr_obj hF (S.vobj L a))
    have hgen : ∀ (a b : S.VObj L) (n : String) (h : S.vstep? L a.1 n = some b.1),
        S'.VPathEq L (T.vobj hT a) (T.gen a.1 n) (T'.gen a.1 n) := by
      intro a b n h
      have hm := Functor.congr_hom hF (vmor (Quiver.Hom.toPath
        (show a ⟶ b from ⟨n, h⟩)))
      rw [vfunctor_map_vmor, vfunctor_map_vmor] at hm
      have := Schema.vPathEq_of_vmor_eq (hobj a) (hobj b) _ _ hm
      rwa [vnames_vfunctorPath, vnames_vfunctorPath, vnames_toPath, vmapPath_singleton,
        vmapPath_singleton] at this
    refine ⟨⟨fun e he => ?_, fun r hr => ?_⟩, fun a ha => ?_⟩
    · have := congrArg Subtype.val (hobj ⟨.entity e, he⟩)
      simpa [vobj, ob] using this
    · exact (hpeq (T.vobj hT ⟨.entity r.src, hS.ref_src r hr⟩) _ _).mpr
        (hgen ⟨.entity r.src, hS.ref_src r hr⟩ ⟨.entity r.tgt, hS.ref_tgt r hr⟩ r.name
          (Schema.step?_of_mem_refs hS hr))
    · exact (hpeq (T.vobj hT ⟨.entity a.src, hS.attr_src a ha⟩) _ _).mpr
        (hgen ⟨.entity a.src, hS.attr_src a ha⟩ ⟨.value a.tgt, trivial⟩ a.name
          (Schema.step?_of_mem_attrs hS ha))

end Translation

end DDD
