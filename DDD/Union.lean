import DDD.Compose
import DDD.Glue

/-!
# Unions of schemas

A schema `G` is covered by schemas `B i` (`Schema.Cover`) when each `B i` is
included in `G` by the empty translation and every object, generator and
equation of `G` is one of some `B i`. Functors out of `G.cat` are then glued from
functors out of the parts.

- `Schema.Agree B F`: the functors `F i` out of the parts agree where the parts
  overlap, on shared objects and on shared generators (as arrows of the target
  category).
- `Cover.desc`: for agreeing functors, the functor out of `G.cat` that is `F i`
  on the objects and generators of `B i`. It restricts to each `F i`
  (`Cover.leg_desc`) and is the only such functor (`Cover.desc_unique`).
- `Schema.glueAll`: the union of a list of schemas, each glued onto the union of
  the ones after it. A generator of the union is the generator of the first part
  that has it. When the parts give each shared generator the same target, the
  parts cover their union (`Cover.glueAll`).
- `checkSpanning`: a check on a list, used to derive agreement of all pairs from
  agreement of neighbours (`pairwise_of_checkSpanning`).

The bridge theorem of `DDD.Glue` is the case of two parts.
-/

namespace DDD

open CategoryTheory

namespace Schema

variable {S G : Schema}

/-- A path of a schema included in `G` by the empty translation is a path of `G`
with the same target. -/
theorem tgt?_of_sub (h : ({} : Translation).Valid S G) {o x : Ob} {l : List String}
    (hl : S.tgt? o l = some x) : G.tgt? o l = some x := by
  have := Translation.tgt?_mapPath h hl
  rwa [Translation.mapPath_empty hl, Translation.ob_empty, Translation.ob_empty] at this

theorem step?_of_sub (h : ({} : Translation).Valid S G) {o x : Ob} {n : String}
    (hn : S.step? o n = some x) : G.step? o n = some x := by
  have := tgt?_of_sub h (l := [n]) (by rwa [tgt?_singleton])
  rwa [tgt?_singleton] at this

/-! ## Covers and agreeing functors -/

/-- `G` is covered by the schemas `B i`: each is included in `G` by the empty
translation, and every object, generator and equation of `G` is one of some
`B i`. -/
structure Cover (G : Schema) {ι : Type*} (B : ι → Schema) : Prop where
  wf : G.WellFormed
  wf_part : ∀ i, (B i).WellFormed
  sub : ∀ i, ({} : Translation).Valid (B i) G
  ob : ∀ o, G.IsOb o → ∃ i, (B i).IsOb o
  gen : ∀ {o x : Ob} {n : String}, G.step? o n = some x → ∃ i, (B i).step? o n = some x
  eqn : ∀ q ∈ G.eqns, ∃ i, q ∈ (B i).eqns

/-- Functors out of the schemas `B i` agree where the schemas overlap: on each
shared object, and on each shared generator, as arrows of `X`. -/
structure Agree {ι : Type*} (B : ι → Schema) {X : Type*} [Category X]
    (F : ∀ i, (B i).cat ⥤ X) : Prop where
  ob : ∀ i j (o : Ob) (hi : (B i).IsOb o) (hj : (B j).IsOb o),
    (F i).obj ((B i).obj ⟨o, hi⟩) = (F j).obj ((B j).obj ⟨o, hj⟩)
  gen : ∀ i j (a b : Ob) (n : String) (hai : (B i).IsOb a) (hbi : (B i).IsOb b)
    (haj : (B j).IsOb a) (hbj : (B j).IsOb b) (hi : (B i).step? a n = some b)
    (hj : (B j).step? a n = some b),
    Arrow.mk ((F i).map ((B i).genMor (a := ⟨a, hai⟩) (b := ⟨b, hbi⟩) n hi)) =
      Arrow.mk ((F j).map ((B j).genMor (a := ⟨a, haj⟩) (b := ⟨b, hbj⟩) n hj))

namespace Cover

variable {ι : Type*} {B : ι → Schema} (hC : Cover G B)

/-- The inclusion of the part `B i` in `G`. -/
def leg (i : ι) : (B i).cat ⥤ G.cat := Translation.functor hC.wf (hC.sub i)

/-- A part with the object `a`. -/
noncomputable def partOb (a : G.Obj) : ι := Classical.choose (hC.ob a.1 a.2)

theorem partOb_spec (a : G.Obj) : (B (hC.partOb a)).IsOb a.1 :=
  Classical.choose_spec (hC.ob a.1 a.2)

/-- A part with the generator `e`. -/
noncomputable def partGen {a b : G.Obj} (e : a ⟶ b) : ι := Classical.choose (hC.gen e.2)

theorem partGen_spec {a b : G.Obj} (e : a ⟶ b) : (B (hC.partGen e)).step? a.1 e.1 = some b.1 :=
  Classical.choose_spec (hC.gen e.2)

section Desc

variable {X : Type*} [Category X] {F : ∀ i, (B i).cat ⥤ X}

variable (F) in
/-- The object map of the glued functor: `F i` for a part `B i` with the
object. -/
noncomputable def descObj (a : G.Obj) : X :=
  (F (hC.partOb a)).obj ((B (hC.partOb a)).obj ⟨a.1, hC.partOb_spec a⟩)

variable (hF : Agree B F)

include hF in
theorem descObj_eq (a : G.Obj) (i : ι) (h : (B i).IsOb a.1) :
    hC.descObj F a = (F i).obj ((B i).obj ⟨a.1, h⟩) :=
  hF.ob _ _ _ _ _

/-- The map of the glued functor on a generator: `F i` for a part `B i` with the
generator. -/
noncomputable def descMap {a b : G.Obj} (e : a ⟶ b) : hC.descObj F a ⟶ hC.descObj F b :=
  have h := hC.partGen_spec e
  have ha := isOb_src_of_step? (hC.wf_part _) h
  have hb := isOb_of_step? (hC.wf_part _) h
  eqToHom (hC.descObj_eq hF a _ ha) ≫
    (F (hC.partGen e)).map ((B (hC.partGen e)).genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 h) ≫
    eqToHom (hC.descObj_eq hF b _ hb).symm

/-- On a generator, the glued functor is `F j` for every part `B j` with the
generator. -/
theorem descMap_eq {a b : G.Obj} (e : a ⟶ b) (j : ι) (ha : (B j).IsOb a.1) (hb : (B j).IsOb b.1)
    (h : (B j).step? a.1 e.1 = some b.1) :
    hC.descMap hF e = eqToHom (hC.descObj_eq hF a j ha) ≫
      (F j).map ((B j).genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 h) ≫
      eqToHom (hC.descObj_eq hF b j hb).symm := by
  obtain ⟨h₁, h₂, hm⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (hF.gen (hC.partGen e) j a.1 b.1 e.1 _ _ ha hb (hC.partGen_spec e) h)
  simp only [descMap]
  rw [hm]
  simp

/-- The prefunctor of the glued functor. -/
noncomputable def descPrefunctor : G.Obj ⥤q X where
  obj := hC.descObj F
  map := hC.descMap hF

/-- On a path of `G` whose names are a path of the part `B i`, the glued functor is
`F i`. -/
theorem lift_map_part (i : ι) {a : G.Obj} (ha : (B i).IsOb a.1) :
    ∀ {b : G.Obj} (p : Quiver.Path a b) (hb : (B i).IsOb b.1)
      (h : (B i).tgt? a.1 (names p) = some b.1),
      (Paths.lift (hC.descPrefunctor hF)).map p = eqToHom (hC.descObj_eq hF a i ha) ≫
        (F i).map ((B i).mor ((B i).pathOf (hC.wf_part i) ⟨a.1, ha⟩ ⟨b.1, hb⟩ (names p) h)) ≫
        eqToHom (hC.descObj_eq hF b i hb).symm
  | _, .nil, hb, h => by
    have : (B i).pathOf (hC.wf_part i) ⟨a.1, ha⟩ ⟨a.1, hb⟩ (names Quiver.Path.nil) h =
        Quiver.Path.nil := names_injective _ _ (by simp)
    rw [this]
    simp [Paths.lift_nil]
    rfl
  | b, .cons (b := c) p e, hb, h => by
    have h' := h
    rw [names_cons, tgt?_append] at h'
    obtain ⟨c', hc', he⟩ := Option.bind_eq_some_iff.mp h'
    obtain rfl : c' = c.1 :=
      Option.some.inj ((tgt?_of_sub (hC.sub i) hc').symm.trans (tgt?_names p))
    rw [tgt?_singleton] at he
    have hc : (B i).IsOb c.1 := isOb_src_of_step? (hC.wf_part i) he
    rw [Paths.lift_cons, lift_map_part i ha p hc hc']
    change _ ≫ hC.descMap hF e = _
    rw [hC.descMap_eq hF e i hc hb he]
    have hp : (B i).pathOf (hC.wf_part i) ⟨a.1, ha⟩ ⟨b.1, hb⟩ (names (p.cons e)) h =
        ((B i).pathOf (hC.wf_part i) ⟨a.1, ha⟩ ⟨c.1, hc⟩ (names p) hc').comp
          ((B i).genPath ⟨c.1, hc⟩ ⟨b.1, hb⟩ e.1 he) :=
      names_injective _ _ (by simp)
    rw [hp, mor_comp, Functor.map_comp]
    simp

/-- The functor glued from agreeing functors out of the parts. It respects the
equations of `G`, each of which is an equation of a part. -/
noncomputable def desc : G.cat ⥤ X :=
  CategoryTheory.Quotient.lift G.rel (Paths.lift (hC.descPrefunctor hF)) (by
    rintro a b f g ⟨q, hq, ha, h₁, h₂⟩
    obtain ⟨i, hqi⟩ := hC.eqn q hq
    have hwf := hC.wf_part i
    obtain ⟨o, hl, hr⟩ := hwf.eqn_parallel q hqi
    have hqa : (B i).IsOb a.1 := ha ▸ hwf.eqn_src q hqi
    rw [← ha, ← h₁] at hl
    rw [← ha, ← h₂] at hr
    obtain rfl : o = b.1 :=
      Option.some.inj ((tgt?_of_sub (hC.sub i) hl).symm.trans (tgt?_names f))
    have hb : (B i).IsOb b.1 := isOb_of_tgt? hwf hqa hl
    change (Paths.lift (hC.descPrefunctor hF)).map f = (Paths.lift (hC.descPrefunctor hF)).map g
    rw [hC.lift_map_part hF i hqa f hb hl, hC.lift_map_part hF i hqa g hb hr]
    have hm : (B i).mor ((B i).pathOf hwf ⟨a.1, hqa⟩ ⟨b.1, hb⟩ (names f) hl) =
        (B i).mor ((B i).pathOf hwf ⟨a.1, hqa⟩ ⟨b.1, hb⟩ (names g) hr) := by
      apply PathEq.mor_eq
      rw [names_pathOf, names_pathOf, h₁, h₂]
      have hpe := pathEq_of_mem_eqns hwf hqi
      have hobj : (⟨a.1, hqa⟩ : (B i).Obj) = ⟨.entity q.src, hwf.eqn_src q hqi⟩ :=
        Subtype.ext ha
      rw [hobj]
      exact hpe
    rw [hm])

theorem desc_obj (a : G.Obj) : (hC.desc hF).obj (G.obj a) = hC.descObj F a := rfl

theorem desc_map_genPath {a b : G.Obj} (e : a ⟶ b) :
    (hC.desc hF).map (G.mor e.toPath) = hC.descMap hF e :=
  Paths.lift_toPath _ _

/-- The glued functor restricts to `F i` on the part `B i`. -/
theorem leg_desc (i : ι) : hC.leg i ⋙ hC.desc hF = F i := by
  have hobj : ∀ a : (B i).Obj,
      (hC.leg i ⋙ hC.desc hF).obj ((B i).obj a) = (F i).obj ((B i).obj a) := fun a => by
    change hC.descObj F (Translation.obj (hC.sub i) a) = _
    rw [Translation.obj_empty]
    exact hC.descObj_eq hF _ i a.2
  refine ext_functor hobj fun a b e => ?_
  have ha : (B i).IsOb (Translation.ob {} a.1) := (Translation.ob_empty a.1).symm ▸ a.2
  have hb : (B i).IsOb (Translation.ob {} b.1) := (Translation.ob_empty b.1).symm ▸ b.2
  have hp : (B i).tgt? (Translation.ob {} a.1)
      (names (Translation.functorPath hC.wf (hC.sub i) e.toPath)) =
        some (Translation.ob {} b.1) := by
    rw [Translation.names_functorPath_empty, Translation.ob_empty, Translation.ob_empty]
    simpa [tgt?_singleton] using e.2
  change (Paths.lift (hC.descPrefunctor hF)).map
      (Translation.functorPath hC.wf (hC.sub i) e.toPath) = _
  rw [hC.lift_map_part hF i ha _ hb hp,
    map_mor_eq_of_names (F i) (Subtype.ext (Translation.ob_empty a.1))
      (Subtype.ext (Translation.ob_empty b.1)) _ e.toPath
        (by simp [Translation.names_functorPath_empty])]
  simp

/-- The glued functor is the only functor that restricts to every `F i`. -/
theorem desc_unique (F' : G.cat ⥤ X) (h : ∀ i, hC.leg i ⋙ F' = F i) : F' = hC.desc hF := by
  have hobj : ∀ a : G.Obj, F'.obj (G.obj a) = (hC.desc hF).obj (G.obj a) := by
    intro a
    rw [desc_obj]
    obtain ⟨i, hi⟩ := hC.ob a.1 a.2
    have e : (hC.leg i).obj ((B i).obj ⟨a.1, hi⟩) = G.obj a :=
      congrArg G.obj (Subtype.ext (Translation.ob_empty a.1))
    rw [← e, hC.descObj_eq hF a i hi]
    exact Functor.congr_obj (h i) _
  refine ext_functor hobj fun a b e => ?_
  rw [desc_map_genPath]
  obtain ⟨i, hs⟩ := hC.gen e.2
  have ha : (B i).IsOb a.1 := isOb_src_of_step? (hC.wf_part i) hs
  have hb : (B i).IsOb b.1 := isOb_of_step? (hC.wf_part i) hs
  rw [hC.descMap_eq hF e i ha hb hs]
  have g := Translation.functor_empty_genMor hC.wf (hC.sub i)
    (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs a.2 b.2 e.2
  have k : G.mor e.toPath =
      eqToHom (congrArg G.obj (Subtype.ext (Translation.ob_empty a.1) :
        Translation.obj (hC.sub i) ⟨a.1, ha⟩ = ⟨a.1, a.2⟩)).symm ≫
      (hC.leg i).map ((B i).genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs) ≫
      eqToHom (congrArg G.obj (Subtype.ext (Translation.ob_empty b.1) :
        Translation.obj (hC.sub i) ⟨b.1, hb⟩ = ⟨b.1, b.2⟩)) := by
    simp only [leg]
    rw [g]
    simp
    rfl
  have hc := Functor.congr_hom (h i) ((B i).genMor (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩) e.1 hs)
  simp only [Functor.comp_map] at hc
  rw [k, Functor.map_comp, Functor.map_comp, hc]
  simp [eqToHom_map]

end Desc

end Cover

/-! ## The union of a list of schemas -/

/-- The union of a list of schemas: each glued onto the union of the ones after
it. -/
def glueAll : List Schema → Schema
  | [] => { entities := [] }
  | B :: Bs => glue B (glueAll Bs)

theorem mem_entities_glueAll {e : String} :
    ∀ {Bs : List Schema}, e ∈ (glueAll Bs).entities ↔ ∃ B ∈ Bs, e ∈ B.entities
  | [] => by simp [glueAll]
  | B :: Bs => by
    simp only [glueAll, glue, List.mem_append, List.mem_filter, decide_eq_true_eq,
      mem_entities_glueAll, List.mem_cons, exists_eq_or_imp]
    tauto

theorem eqns_glueAll : ∀ (Bs : List Schema), (glueAll Bs).eqns = Bs.flatMap (·.eqns)
  | [] => rfl
  | B :: Bs => by simp [glueAll, glue, eqns_glueAll Bs]

theorem step?_glueAll (o : Ob) (n : String) (B : Schema) (Bs : List Schema) :
    (glueAll (B :: Bs)).step? o n = (B.step? o n).or ((glueAll Bs).step? o n) :=
  glue_step? o n

/-- A generator of the union is a generator of a part. -/
theorem exists_of_step?_glueAll {o x : Ob} {n : String} :
    ∀ {Bs : List Schema}, (glueAll Bs).step? o n = some x → ∃ B ∈ Bs, B.step? o n = some x
  | [], h => by
    cases o with
    | value => simp [step?] at h
    | entity e => simp [glueAll, step?, ref?, attr?] at h
  | B :: Bs, h => by
    rw [step?_glueAll] at h
    cases hB : B.step? o n with
    | some y =>
      rw [hB, Option.some_or] at h
      exact ⟨B, List.mem_cons_self, hB.trans h⟩
    | none =>
      rw [hB, Option.none_or] at h
      obtain ⟨B', hB', h'⟩ := exists_of_step?_glueAll h
      exact ⟨B', List.mem_cons_of_mem _ hB', h'⟩

/-- When the parts give each shared generator the same target, a generator of a
part is a generator of the union. -/
theorem step?_glueAll_of_mem {o x : Ob} {n : String} :
    ∀ {Bs : List Schema},
      (∀ B ∈ Bs, ∀ B' ∈ Bs, ∀ y y', B.step? o n = some y → B'.step? o n = some y' → y = y') →
      ∀ {B : Schema}, B ∈ Bs → B.step? o n = some x → (glueAll Bs).step? o n = some x
  | [], _, _, hB, _ => absurd hB List.not_mem_nil
  | B₀ :: Bs, hagree, B, hB, h => by
    rw [step?_glueAll]
    rcases List.mem_cons.mp hB with rfl | hB
    · rw [h, Option.some_or]
    · have ih := step?_glueAll_of_mem (Bs := Bs)
        (fun B hB B' hB' => hagree B (List.mem_cons_of_mem _ hB) B' (List.mem_cons_of_mem _ hB'))
        hB h
      cases h₀ : B₀.step? o n with
      | none => rw [Option.none_or, ih]
      | some y =>
        rw [Option.some_or, hagree B₀ List.mem_cons_self B (List.mem_cons_of_mem _ hB) y x h₀ h]

/-- Parts that give each shared generator the same target cover their union,
when the union is well formed. -/
theorem Cover.glueAll {ι : Type*} (l : List ι) (B : ι → Schema) (hne : l ≠ [])
    (hwf : (glueAll (l.map B)).WellFormed) (hB : ∀ i ∈ l, (B i).WellFormed)
    (hstep : ∀ i ∈ l, ∀ j ∈ l, ∀ (o : Ob) (n : String) (y y' : Ob),
      (B i).step? o n = some y → (B j).step? o n = some y' → y = y') :
    Cover (glueAll (l.map B)) (fun i : {i // i ∈ l} => B i.1) where
  wf := hwf
  wf_part i := hB i.1 i.2
  sub i := by
    have hagree : ∀ C ∈ l.map B, ∀ C' ∈ l.map B, ∀ (o : Ob) (n : String) (y y' : Ob),
        C.step? o n = some y → C'.step? o n = some y' → y = y' := by
      intro C hC C' hC' o n y y' h h'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hC
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hC'
      exact hstep j hj j' hj' o n y y' h h'
    have hmem : B i.1 ∈ l.map B := List.mem_map_of_mem i.2
    have hwfi := hB i.1 i.2
    have hs : ∀ {o x : Ob} {n : String}, (B i.1).step? o n = some x →
        (Schema.glueAll (l.map B)).step? o n = some x := fun h =>
      step?_glueAll_of_mem (fun C hC C' hC' y y' => hagree C hC C' hC' _ _ y y') hmem h
    exact {
      entity := fun e he => mem_entities_glueAll.mpr ⟨B i.1, hmem, he⟩
      ref := fun r hr => by
        simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
        exact hs (step?_of_mem_refs hwfi hr)
      attr := fun a ha => by
        simp only [Translation.ob_empty, Translation.gen_empty, tgt?_singleton]
        exact hs (step?_of_mem_attrs hwfi ha)
      eqn := fun q hq => by
        obtain ⟨o, hl, hr⟩ := hwfi.eqn_parallel q hq
        rw [Translation.mapPath_empty hl, Translation.mapPath_empty hr]
        refine ⟨mem_entities_glueAll.mpr ⟨B i.1, hmem, hwfi.eqn_src q hq⟩, ?_⟩
        exact pathEq_of_mem_eqns hwf (by
          rw [eqns_glueAll]
          exact List.mem_flatMap.mpr ⟨B i.1, hmem, hq⟩) }
  ob o ho := by
    cases o with
    | value =>
      obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil l hne
      exact ⟨⟨i, hi⟩, trivial⟩
    | entity e =>
      obtain ⟨C, hC, he⟩ := mem_entities_glueAll.mp ho
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
      exact ⟨⟨i, hi⟩, he⟩
  gen h := by
    obtain ⟨C, hC, h'⟩ := exists_of_step?_glueAll h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
    exact ⟨⟨i, hi⟩, h'⟩
  eqn q hq := by
    rw [eqns_glueAll] at hq
    obtain ⟨C, hC, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
    exact ⟨⟨i, hi⟩, hq⟩

end Schema

/-! ## Spanning lists -/

/-- `checkSpanning has adj seen rest`: each element `m` of `rest` that has the
property `has` is the first to have it (no element of `seen`, nor an earlier
element of `rest`, has it), or is `adj` to an earlier element that has it. -/
def checkSpanning {α : Type*} (has : α → Bool) (adj : α → α → Bool) : List α → List α → Bool
  | _, [] => true
  | seen, m :: rest =>
    (!has m || !seen.any has || seen.any fun c => has c && adj c m) &&
      checkSpanning has adj (m :: seen) rest

/-- A relation that is reflexive, symmetric and transitive on the elements of `U`
with the property `has`, and holds between `adj` elements, holds between all
elements with the property, when the list spans. -/
theorem pairwise_of_checkSpanning {α : Type*} {has : α → Bool} {adj : α → α → Bool}
    (R : α → α → Prop) (U : List α)
    (hrefl : ∀ c ∈ U, has c → R c c)
    (hsymm : ∀ c ∈ U, ∀ c' ∈ U, has c → has c' → R c c' → R c' c)
    (htrans : ∀ c ∈ U, ∀ c' ∈ U, ∀ c'' ∈ U, has c → has c' → has c'' →
      R c c' → R c' c'' → R c c'')
    (hadj : ∀ c ∈ U, ∀ c' ∈ U, has c → has c' → adj c c' = true → R c c') :
    ∀ (seen rest : List α), seen ⊆ U → rest ⊆ U →
      (∀ c ∈ seen, ∀ c' ∈ seen, has c → has c' → R c c') →
      checkSpanning has adj seen rest = true →
      ∀ c ∈ seen ++ rest, ∀ c' ∈ seen ++ rest, has c → has c' → R c c'
  | seen, [], _, _, h, _ => by simpa using h
  | seen, m :: rest, hseen, hrest, h, hc => by
    simp only [checkSpanning, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.any_eq_false, List.any_eq_true] at hc
    obtain ⟨hm, hc⟩ := hc
    have hmU : m ∈ U := hrest List.mem_cons_self
    -- `m` is related to every element of `seen` with the property.
    have hms : ∀ c ∈ seen, has c → has m → R c m := by
      intro c hcs hhc hhm
      rcases hm with (hm | hm) | ⟨c₀, hc₀, hh₀, ha₀⟩
      · simp [hhm] at hm
      · exact absurd hhc (by simpa using hm c hcs)
      · exact htrans c (hseen hcs) c₀ (hseen hc₀) m hmU hhc hh₀ hhm
          (h c hcs c₀ hc₀ hhc hh₀) (hadj c₀ (hseen hc₀) m hmU hh₀ hhm ha₀)
    have h' : ∀ c ∈ m :: seen, ∀ c' ∈ m :: seen, has c → has c' → R c c' := by
      intro c hcs c' hcs' hhc hhc'
      rcases List.mem_cons.mp hcs with e | hs <;> rcases List.mem_cons.mp hcs' with e' | hs'
      · subst e e'
        exact hrefl _ hmU hhc
      · subst e
        exact hsymm c' (hseen hs') _ hmU hhc' hhc (hms c' hs' hhc' hhc)
      · subst e'
        exact hms c hs hhc hhc'
      · exact h c hs c' hs' hhc hhc'
    have ih := pairwise_of_checkSpanning R U hrefl hsymm htrans hadj (m :: seen) rest
      (List.cons_subset.mpr ⟨hmU, hseen⟩) (fun x hx => hrest (List.mem_cons_of_mem _ hx)) h' hc
    intro c hcm c' hcm' hhc hhc'
    have hperm : ∀ x, x ∈ seen ++ m :: rest → x ∈ (m :: seen) ++ rest := by
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
    exact ih c (hperm c hcm) c' (hperm c' hcm') hhc hhc'

end DDD
