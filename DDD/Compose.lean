import DDD.Translation

/-!
# Composite translations and equality of functors

- `Translation.comp T S S' U`: the composite of a translation `T` from `S` to `S'`
  and a translation `U` out of `S'`, as finite data. Each entity type of `S`
  goes to the image under `U` of its image under `T`, and each generator to the
  image under `U` of its image path (`comp_ent`, `comp_gen`, `comp_mapPath`).
  It is valid (`comp_valid`), and its functor is the composite of the functors
  (`functor_comp`).
- The empty translation from a well-formed schema to itself is valid
  (`empty_valid_self`), and its functor is the identity (`functor_empty_self`).
- `Translation.checkSameFunctor T T' S peq`: `T` and `T'` agree on the entity
  types of `S`, and send each generator to paths that `peq` finds equal. It is
  sound: the two functors are equal (`checkSameFunctor_sound`); and complete
  when `peq` is (`checkSameFunctor_iff`).
-/

namespace DDD

open CategoryTheory

namespace Schema

variable {S : Schema}

/-- A generator out of `o` is a reference or an attribute of `S` out of an entity
type. -/
theorem exists_gen_of_step? {o o' : Ob} {n : String} (h : S.step? o n = some o') :
    ∃ e, o = .entity e ∧
      ((∃ r ∈ S.refs, r.src = e ∧ r.name = n) ∨ (∃ a ∈ S.attrs, a.src = e ∧ a.name = n)) := by
  cases o with
  | value => simp [step?] at h
  | entity e =>
    refine ⟨e, rfl, ?_⟩
    simp only [step?] at h
    split at h
    · rename_i r hr
      unfold ref? at hr
      have hp := List.find?_some hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact Or.inl ⟨r, List.mem_of_find?_eq_some hr, hp⟩
    · obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.mp h
      unfold attr? at ha
      have hp := List.find?_some ha
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact Or.inr ⟨a, List.mem_of_find?_eq_some ha, hp⟩

/-- The object map of `Schema.obj` is injective. -/
theorem obj_injective {a b : S.Obj} (h : S.obj a = S.obj b) : a = b := by
  have h' : (CategoryTheory.Quotient.functor S.rel).obj a =
      (CategoryTheory.Quotient.functor S.rel).obj b := h
  exact congrArg (fun x : CategoryTheory.Quotient S.rel => x.as) h'

/-- Paths that present the same morphism, up to equalities of their endpoints,
satisfy `PathEq`. -/
theorem pathEq_of_mor_eq {a a' b b' : S.Obj} (ha : a = a') (hb : b = b') (p : Quiver.Path a b)
    (p' : Quiver.Path a' b')
    (h : mor p = eqToHom (congrArg S.obj ha) ≫ mor p' ≫ eqToHom (congrArg S.obj hb).symm) :
    S.PathEq a (names p) (names p') := by
  subst ha hb
  exact ⟨b, p, p', rfl, rfl, by simpa using h⟩

/-- Paths whose names satisfy `PathEq` present the same morphism, up to equalities
of their endpoints. -/
theorem mor_eq_of_pathEq {a a' b b' : S.Obj} (ha : a = a') (hb : b = b') (p : Quiver.Path a b)
    (p' : Quiver.Path a' b') (h : S.PathEq a (names p) (names p')) :
    mor p = eqToHom (congrArg S.obj ha) ≫ mor p' ≫ eqToHom (congrArg S.obj hb).symm := by
  subst ha hb
  simpa using PathEq.mor_eq h

end Schema

namespace Translation

variable {S S' S'' : Schema}

/-! ## Images of paths under valid translations -/

/-- A path of `S` goes to a path of `S'` between the images of its endpoints. -/
theorem tgt?_mapPath {T : Translation} (hT : T.Valid S S') :
    ∀ {o x : Ob} {l : List String}, S.tgt? o l = some x →
      S'.tgt? (T.ob o) (T.mapPath S o l) = some (T.ob x)
  | _, _, [], h => by cases h; rfl
  | o, x, n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      simp only [mapPath, hs]
      rw [Schema.tgt?_append, tgt?_gen hT hs, Option.bind_some]
      exact tgt?_mapPath hT h

/-- A valid translation sends paths that present the same morphism to paths that
present the same morphism. -/
theorem PathEq.map {T : Translation} (hS' : S'.WellFormed) (hT : T.Valid S S') {a : S.Obj}
    {l l' : List String} (h : S.PathEq a l l') :
    S'.PathEq (obj hT a) (T.mapPath S a.1 l) (T.mapPath S a.1 l') := by
  obtain ⟨b, p, q, rfl, rfl, hm⟩ := h
  refine ⟨obj hT b, functorPath hS' hT p, functorPath hS' hT q, names_functorPath hS' hT p,
    names_functorPath hS' hT q, ?_⟩
  rw [← functor_map_mor, ← functor_map_mor, hm]

/-! ## The composite -/

/-- The composite of `T` from `S` to `S'` and `U` out of `S'`: the images of the
entity types and generators of `S`, listed. -/
def comp (T : Translation) (S S' : Schema) (U : Translation) : Translation where
  entities := S.entities.map fun e => (e, U.ent (T.ent e))
  gens := (S.refs.map fun r => ⟨r.src, r.name,
      U.mapPath S' (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name)⟩) ++
    S.attrs.map fun a => ⟨a.src, a.name,
      U.mapPath S' (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name)⟩

variable (T U : Translation)

theorem comp_ent {e : String} (he : e ∈ S.entities) : (T.comp S S' U).ent e = U.ent (T.ent e) := by
  have hsome : ((S.entities.map fun e => (e, U.ent (T.ent e))).find? (·.1 == e)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(e, U.ent (T.ent e)), List.mem_map.mpr ⟨e, he, rfl⟩, by simp⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hx
  obtain ⟨e', -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hx)
  simp only [beq_iff_eq] at hp
  subst hp
  change (((S.entities.map fun e => (e, U.ent (T.ent e))).find? (·.1 == e')).map (·.2)).getD e' = _
  rw [hx]
  rfl

theorem comp_ob {o : Ob} (ho : S.IsOb o) : (T.comp S S' U).ob o = U.ob (T.ob o) := by
  cases o with
  | value => rfl
  | entity e => simp only [ob, comp_ent T U ho]

theorem comp_gen {o o' : Ob} {n : String} (h : S.step? o n = some o') :
    (T.comp S S' U).gen o n = U.mapPath S' (T.ob o) (T.gen o n) := by
  obtain ⟨e, rfl, hg⟩ := Schema.exists_gen_of_step? h
  let F : String → String → List String := fun s m =>
    U.mapPath S' (T.ob (.entity s)) (T.gen (.entity s) m)
  have hall : ∀ g ∈ (T.comp S S' U).gens, g.path = F g.src g.name := by
    intro g hg
    simp only [comp, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨r, -, rfl⟩ | ⟨a, -, rfl⟩ <;> rfl
  have hsome : ((T.comp S S' U).gens.find? fun g => g.src == e && g.name == n).isSome := by
    rw [List.find?_isSome]
    rcases hg with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩), by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩), by simp⟩
  obtain ⟨g, hgf⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hgf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hc : (T.comp S S' U).gen (.entity e) n = g.path := by
    simp only [gen, hgf, Option.map_some, Option.getD_some]
  rw [hc, hall g (List.mem_of_find?_eq_some hgf), hp.1, hp.2]

/-- The image of a path under the composite is the image under `U` of its image
under `T`. -/
theorem comp_mapPath {T : Translation} (U : Translation) (hT : T.Valid S S') :
    ∀ {o x : Ob} {l : List String}, S.tgt? o l = some x →
      (T.comp S S' U).mapPath S o l = U.mapPath S' (T.ob o) (T.mapPath S o l)
  | _, _, [], _ => rfl
  | o, x, n :: ns, h => by
    cases hs : S.step? o n with
    | none => simp [hs] at h
    | some o' =>
      simp only [Schema.tgt?_cons, hs, Option.bind_some] at h
      simp only [mapPath, hs]
      rw [comp_gen T U hs, comp_mapPath U hT h, mapPath_append (tgt?_gen hT hs)]

variable {T U}

/-- The composite of valid translations is valid. -/
theorem comp_valid (hS : S.WellFormed) (hS'' : S''.WellFormed) (hT : T.Valid S S')
    (hU : U.Valid S' S'') : (T.comp S S' U).Valid S S'' where
  entity e he := by
    rw [comp_ent T U he]
    exact hU.entity _ (hT.entity e he)
  ref r hr := by
    have hs := Schema.step?_of_mem_refs hS hr
    rw [comp_ob T U (o := .entity r.src) (hS.ref_src r hr),
      comp_ob T U (o := .entity r.tgt) (hS.ref_tgt r hr), comp_gen T U hs]
    exact tgt?_mapPath hU (hT.ref r hr)
  attr a ha := by
    have hs := Schema.step?_of_mem_attrs hS ha
    rw [comp_ob T U (o := .entity a.src) (hS.attr_src a ha), comp_gen T U hs]
    exact tgt?_mapPath hU (hT.attr a ha)
  eqn q hq := by
    have hsrc := hS.eqn_src q hq
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
    obtain ⟨hm, hpe⟩ := hT.eqn q hq
    have hpe' := PathEq.map hS'' hU hpe
    have hent : (T.comp S S' U).ent q.src = U.ent (T.ent q.src) := comp_ent T U hsrc
    refine ⟨hent ▸ hU.entity _ hm, ?_⟩
    rw [comp_mapPath U hT hl, comp_mapPath U hT hr]
    have hobj : (⟨.entity ((T.comp S S' U).ent q.src), hent ▸ hU.entity _ hm⟩ : S''.Obj) =
        obj hU ⟨.entity (T.ent q.src), hm⟩ := Subtype.ext (by simp [obj, ob, hent])
    rw [hobj]
    exact hpe'

/-- The functor of the composite is the composite of the functors. -/
theorem functor_comp (hS : S.WellFormed) (hS' : S'.WellFormed) (hS'' : S''.WellFormed)
    (hT : T.Valid S S') (hU : U.Valid S' S'') :
    functor hS'' (comp_valid hS hS'' hT hU) = functor hS' hT ⋙ functor hS'' hU := by
  have hobj : ∀ a : S.Obj, obj (comp_valid hS hS'' hT hU) a = obj hU (obj hT a) :=
    fun a => Subtype.ext (comp_ob T U a.2)
  refine Schema.ext_functor (fun a => congrArg S''.obj (hobj a)) fun a b e => ?_
  rw [Functor.comp_map, functor_map_mor, functor_map_mor, functor_map_mor]
  apply Schema.mor_eq_of_names (hobj a) (hobj b)
  rw [names_functorPath, names_functorPath, names_functorPath, Schema.names_toPath,
    mapPath_singleton, mapPath_singleton, comp_gen T U e.2]
  rfl

/-! ## The identity -/

/-- The empty translation from a well-formed schema to itself is valid. -/
theorem empty_valid_self (hS : S.WellFormed) : ({} : Translation).Valid S S where
  entity e he := he
  ref r hr := by
    simp only [ob_empty, gen_empty, Schema.tgt?_singleton]
    exact Schema.step?_of_mem_refs hS hr
  attr a ha := by
    simp only [ob_empty, gen_empty, Schema.tgt?_singleton]
    exact Schema.step?_of_mem_attrs hS ha
  eqn q hq := by
    obtain ⟨o, hl, hr⟩ := hS.eqn_parallel q hq
    rw [mapPath_empty hl, mapPath_empty hr]
    exact ⟨hS.eqn_src q hq, Schema.pathEq_of_mem_eqns hS hq⟩

/-- The functor of the empty translation from a schema to itself is the
identity. -/
theorem functor_empty_self (hS : S.WellFormed) (h : ({} : Translation).Valid S S) :
    functor hS h = 𝟭 _ := by
  have hobj : ∀ a : S.Obj, obj h a = a := fun a => Subtype.ext (ob_empty a.1)
  refine Schema.ext_functor (fun a => congrArg S.obj (hobj a)) fun a b e => ?_
  rw [functor_map_mor, Functor.id_map]
  exact Schema.mor_eq_of_names (hobj a) (hobj b) _ _ (names_functorPath_empty hS h _)

/-- Inclusions compose: the composite of the functors of two valid empty
translations is the functor of the empty translation. -/
theorem functor_empty_comp_empty (hS' : S'.WellFormed) (hS'' : S''.WellFormed)
    (h₁ : ({} : Translation).Valid S S') (h₂ : ({} : Translation).Valid S' S'')
    (h₃ : ({} : Translation).Valid S S'') :
    functor hS' h₁ ⋙ functor hS'' h₂ = functor hS'' h₃ := by
  have hobj : ∀ a : S.Obj, obj h₂ (obj h₁ a) = obj h₃ a :=
    fun a => Subtype.ext (by simp [obj])
  refine Schema.ext_functor (fun a => congrArg S''.obj (hobj a)) fun a b e => ?_
  rw [Functor.comp_map, functor_map_mor, functor_map_mor, functor_map_mor]
  apply Schema.mor_eq_of_names (hobj a) (hobj b)
  rw [names_functorPath_empty, names_functorPath_empty, names_functorPath_empty]

/-! ## Equality of functors -/

/-- `T` and `T'` agree on the entity types of `S` and send each generator of `S` to
paths that `peq` finds equal. -/
def checkSameFunctor (T T' : Translation) (S : Schema)
    (peq : Ob → List String → List String → Bool) : Bool :=
  S.entities.all (fun e => T.ent e == T'.ent e) &&
  S.refs.all (fun r =>
    peq (T.ob (.entity r.src)) (T.gen (.entity r.src) r.name) (T'.gen (.entity r.src) r.name)) &&
  S.attrs.all (fun a =>
    peq (T.ob (.entity a.src)) (T.gen (.entity a.src) a.name) (T'.gen (.entity a.src) a.name))

variable {T T' : Translation} {peq : Ob → List String → List String → Bool}

theorem checkSameFunctor_sound (hS' : S'.WellFormed) (hT : T.Valid S S') (hT' : T'.Valid S S')
    (hpeq : ∀ (a : S'.Obj) (l l' : List String), peq a.1 l l' = true → S'.PathEq a l l')
    (h : T.checkSameFunctor T' S peq = true) : functor hS' hT = functor hS' hT' := by
  simp only [checkSameFunctor, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨he, hr⟩, ha⟩ := h
  have hobj : ∀ a : S.Obj, obj hT a = obj hT' a := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    cases o with
    | value => rfl
    | entity e => simp only [obj, ob, he e ho]
  refine Schema.ext_functor (fun a => congrArg S'.obj (hobj a)) fun a b e => ?_
  rw [functor_map_mor, functor_map_mor]
  apply Schema.mor_eq_of_pathEq (hobj a) (hobj b)
  rw [names_functorPath, names_functorPath, Schema.names_toPath, mapPath_singleton,
    mapPath_singleton]
  obtain ⟨x, hx, hg⟩ := Schema.exists_gen_of_step? e.2
  generalize (e.1 : String) = n at hg ⊢
  rw [hx]
  rcases hg with ⟨r, hrm, hrs, hrn⟩ | ⟨t, htm, hts, htn⟩
  · exact hpeq (obj hT a) _ _ (by simpa [obj, hx, hrs, hrn] using hr r hrm)
  · exact hpeq (obj hT a) _ _ (by simpa [obj, hx, hts, htn] using ha t htm)

theorem checkSameFunctor_iff (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    (hT' : T'.Valid S S')
    (hpeq : ∀ (a : S'.Obj) (l l' : List String), peq a.1 l l' = true ↔ S'.PathEq a l l') :
    T.checkSameFunctor T' S peq = true ↔ functor hS' hT = functor hS' hT' := by
  constructor
  · exact checkSameFunctor_sound hS' hT hT' fun a l l' => (hpeq a l l').mp
  · intro hF
    simp only [checkSameFunctor, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    have hobj : ∀ a : S.Obj, obj hT a = obj hT' a := fun a =>
      Schema.obj_injective (Functor.congr_obj hF (S.obj a))
    have hgen : ∀ (a b : S.Obj) (n : String) (h : S.step? a.1 n = some b.1),
        S'.PathEq (obj hT a) (T.gen a.1 n) (T'.gen a.1 n) := by
      intro a b n h
      have hm := Functor.congr_hom hF (S.genMor n h)
      rw [functor_map_mor, functor_map_mor] at hm
      have := Schema.pathEq_of_mor_eq (hobj a) (hobj b) _ _ hm
      rwa [names_functorPath, names_functorPath, Schema.names_toPath, mapPath_singleton,
        mapPath_singleton] at this
    refine ⟨⟨fun e he => ?_, fun r hr => ?_⟩, fun a ha => ?_⟩
    · have := congrArg Subtype.val (hobj ⟨.entity e, he⟩)
      simpa [obj, ob] using this
    · exact (hpeq (obj hT ⟨.entity r.src, hS.ref_src r hr⟩) _ _).mpr
        (hgen ⟨.entity r.src, hS.ref_src r hr⟩ ⟨.entity r.tgt, hS.ref_tgt r hr⟩ r.name
          (Schema.step?_of_mem_refs hS hr))
    · exact (hpeq (obj hT ⟨.entity a.src, hS.attr_src a ha⟩) _ _).mpr
        (hgen ⟨.entity a.src, hS.attr_src a ha⟩ ⟨.value a.tgt, trivial⟩ a.name
          (Schema.step?_of_mem_attrs hS ha))

end Translation

end DDD
