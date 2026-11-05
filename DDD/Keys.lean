import DDD.VData
import DDD.Aggregates

/-!
# Keys through restriction and gluing

A translation keeps the keys of its source (`Translation.KeysKept`) when, for each
key `(e, F)` of the source, a field of `F` goes to the empty path, or the target
has a key on `T e` each of whose fields is the image `T f` of a field `f` of `F`.

- `Translation.restrictState_keys`: under the condition, `Δ_T` of a state that
  satisfies the keys of the target satisfies the keys of the source;
  `FinState.restrict_checkKeys` states the same of the checks on data, and
  `FinState.vrestrict_checkKeys` of the restriction along a translation that
  converts.
- `Schema.State.KeysOf Y B`: `Y` satisfies the keys of `B`. Along an inclusion, the
  restriction of a state satisfies the keys of the included schema exactly when
  the state satisfies them (`Translation.keys_restrict_empty_iff`).
- Gluing: a state of the glued schema satisfies the keys of the two schemas
  exactly when its restrictions satisfy their keys (`Gluing.keysOf_iff`), and it
  then satisfies the keys of the glued schema, whose value objects have the fields
  of both (`Gluing.keys_of_keysOf`). `Gluing.keyedStateEquiv` restricts data
  gluing to these states, and `Schema.keyedFamilyEquiv` restricts the family
  equivalence of `Aggregates.lean`: a state of the internal schema satisfies the
  keys exactly when each of its aggregate parts does.
-/

namespace DDD

open CategoryTheory Schema

namespace Schema

variable {S : Schema}

/-- A name of a generator out of `e` is a generator of `S` out of `e`. -/
theorem mem_gens_of_mem_outNames {e n : String} (h : n ∈ S.outNames e) : (e, n) ∈ S.gens := by
  simp only [outNames, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at h
  simp only [gens, List.mem_append, List.mem_map, Prod.mk.injEq]
  rcases h with ⟨r, ⟨hr, rfl⟩, rfl⟩ | ⟨a, ⟨ha, rfl⟩, rfl⟩
  · exact Or.inl ⟨r, hr, rfl, rfl⟩
  · exact Or.inr ⟨a, ha, rfl, rfl⟩

/-- In a well-formed schema, every key is on a declared entity type, and its fields
are generators out of it. -/
theorem WellFormed.allKeys_spec (hS : S.WellFormed) {k : Key} (hk : k ∈ S.allKeys) :
    k.entity ∈ S.entities ∧ ∀ n ∈ k.fields, (k.entity, n) ∈ S.gens := by
  simp only [allKeys, List.mem_append, List.mem_map] at hk
  rcases hk with (hk | ⟨e, he, rfl⟩) | ⟨s, hs, rfl⟩
  · exact ⟨hS.key_entities k hk, fun n hn => mem_gens_of_mem_outNames (hS.key_fields k hk n hn)⟩
  · exact ⟨hS.vo_entities e he, fun n hn => mem_gens_of_mem_outNames hn⟩
  · refine ⟨hS.isa_entities s hs, fun n hn => ?_⟩
    obtain rfl := List.mem_singleton.mp hn
    obtain ⟨r, hr, hrs, hrn⟩ := hS.isa_ref s hs
    simp only [gens, List.mem_append, List.mem_map, Prod.mk.injEq]
    exact Or.inl ⟨r, hr, hrs, hrn⟩

/-- In a well-formed schema, each field of a key is a generator, with a target. -/
theorem WellFormed.step?_of_key (hS : S.WellFormed) {k : Key} (hk : k ∈ S.allKeys) {n : String}
    (hn : n ∈ k.fields) : ∃ b : S.Obj, S.step? (.entity k.entity) n = some b.1 := by
  have hs := step?_isSome_iff.mpr ((hS.allKeys_spec hk).2 n hn)
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨⟨o, isOb_of_step? hS ho⟩, ho⟩

end Schema

namespace Translation

variable {T : Translation} {S S' : Schema} {K : ValueType → Type}

/-- A state applied to a path with no names is injective: the path is empty. -/
theorem map_injective_of_names_nil (Y : S.State K) {a : S.Obj} :
    ∀ {c : S.Obj} (p : Quiver.Path a c), names p = [] → Function.Injective (Y.F.map (mor p))
  | _, .nil, _ => by
    rw [mor_nil, CategoryTheory.Functor.map_id]
    exact Function.injective_id
  | _, .cons p e, h => by simp [names_cons] at h

/-- `Δ_T` of a state that satisfies the keys of `S'` satisfies the keys of `S`, when
`T` keeps them. -/
theorem restrictState_keys (hS : S.WellFormed) (hS' : S'.WellFormed) (hT : T.Valid S S')
    (hK : T.KeysKept S S') {Y : S'.State K} (hY : Y.Keys) : (restrictState hS' hT Y).Keys := by
  intro k hk he x y hxy
  rcases hK k hk with ⟨f, hf, hf0⟩ | ⟨⟨e', fs'⟩, hk', hke, hk'f⟩
  · obtain ⟨b, hb⟩ := hS.step?_of_key hk hf
    have h := hxy f hf b hb
    change Y.F.map (S'.mor (functorPath hS' hT (S.genPath ⟨.entity k.entity, he⟩ b f hb))) x =
      Y.F.map (S'.mor (functorPath hS' hT (S.genPath ⟨.entity k.entity, he⟩ b f hb))) y at h
    refine map_injective_of_names_nil Y _ ?_ h
    rw [names_functorPath, names_toPath, mapPath_singleton]
    exact hf0
  · simp only at hke hk'f
    subst hke
    have he' : T.ent k.entity ∈ S'.entities := hT.entity _ he
    refine hY ⟨T.ent k.entity, fs'⟩ hk' he' x y fun n' hn' b' hb' => ?_
    obtain ⟨f, hf, hfn⟩ := hk'f n' hn'
    obtain ⟨b, hb⟩ := hS.step?_of_key hk hf
    have h := hxy f hf b hb
    change Y.F.map (S'.mor (functorPath hS' hT (S.genPath ⟨.entity k.entity, he⟩ b f hb))) x =
      Y.F.map (S'.mor (functorPath hS' hT (S.genPath ⟨.entity k.entity, he⟩ b f hb))) y at h
    have ht := tgt?_gen hT hb
    rw [hfn, tgt?_singleton] at ht
    obtain rfl : b' = obj hT b := Subtype.ext (Option.some.inj (hb'.symm.trans ht))
    have hp : functorPath hS' hT (S.genPath ⟨.entity k.entity, he⟩ b f hb) =
        S'.genPath (obj hT ⟨.entity k.entity, he⟩) (obj hT b) n' hb' :=
      names_injective _ _ (by rw [names_functorPath, names_toPath, mapPath_singleton, hfn]; rfl)
    rw [hp] at h
    exact h

end Translation

namespace FinState

variable {T : Translation} {S S' : Schema} {K : ValueType → Type} {X : FinState K}
  [∀ v, DecidableEq (K v)]

/-- The check of the keys of `S` passes on `Δ_T X` when it passes on `X` for the keys
of `S'` and `T` keeps them. -/
theorem restrict_checkKeys (hS : S.WellFormed) (hX : X.check S' = true) (hT : T.Valid S S')
    (hK : T.KeysKept S S') (hk : X.checkKeys S' = true) :
    (X.restrict T S S').checkKeys S = true := by
  simp only [checkKeys, List.all_eq_true] at hk ⊢
  intro k hkS
  have he := (hS.allKeys_spec hkS).1
  simp only [checkKey, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hk ⊢
  intro i hi j hj
  rw [size_restrict he] at hi hj
  by_cases hij : i = j
  · exact Or.inl hij
  refine Or.inr ?_
  by_contra hag
  simp only [Bool.not_eq_false, agree, List.all_eq_true, decide_eq_true_eq] at hag
  have hxi : (X.restrict T S S').Has (.ent k.entity i) (.entity k.entity) :=
    ⟨rfl, (size_restrict he).symm ▸ hi⟩
  have hxj : (X.restrict T S S').Has (.ent k.entity j) (.entity k.entity) :=
    ⟨rfl, (size_restrict he).symm ▸ hj⟩
  -- Each field of `k` steps to elements whose images are its image path in `X`.
  have hfield : ∀ f ∈ k.fields, ∃ yi yj,
      X.eval S' (.ent (T.ent k.entity) i) (T.gen (.entity k.entity) f) = some (rename T yi) ∧
      X.eval S' (.ent (T.ent k.entity) j) (T.gen (.entity k.entity) f) = some (rename T yj) ∧
      yi = yj := by
    intro f hf
    obtain ⟨b, hb⟩ := hS.step?_of_key hkS hf
    obtain ⟨yi, hyi, -, hei⟩ := restrict_step hS hX hT (show S.IsOb (.entity k.entity) from he)
      hxi hb
    obtain ⟨yj, hyj, -, hej⟩ := restrict_step hS hX hT (show S.IsOb (.entity k.entity) from he)
      hxj hb
    refine ⟨yi, yj, hei, hej, ?_⟩
    have := hag f hf
    rw [hyi, hyj] at this
    exact Option.some.inj this
  rcases hK k hkS with ⟨f, hf, hf0⟩ | ⟨⟨e', fs'⟩, hk', hke, hk'f⟩
  · obtain ⟨yi, yj, hei, hej, rfl⟩ := hfield f hf
    rw [hf0] at hei hej
    have := (Option.some.inj hei).trans (Option.some.inj hej).symm
    exact hij (by injection this)
  · simp only at hke hk'f
    subst hke
    have hk'' := hk ⟨T.ent k.entity, fs'⟩ hk' i hi j hj
    rcases hk'' with h | h
    · exact hij h
    · have hag' : X.agree S' (T.ent k.entity) fs' i j = true := by
        simp only [agree, List.all_eq_true, decide_eq_true_eq]
        intro n' hn'
        obtain ⟨f, hf, hfn⟩ := hk'f n' hn'
        obtain ⟨yi, yj, hei, hej, rfl⟩ := hfield f hf
        rw [hfn, eval_singleton] at hei hej
        rw [hei, hej]
      rw [hag'] at h
      exact absurd h (by simp)

variable {L : TypeList} {I : Interp L} {Z : FinState I.K} [∀ v, DecidableEq (I.K v)]

/-- The check of the keys of `S` passes on `Δ_T Z` along a translation that converts,
when it passes on `Z` for the keys of `S'` and `T` keeps them. -/
theorem vrestrict_checkKeys (hS : S.WellFormed) (hZ : Z.check S' = true)
    (hT : T.VValid L S S') (hK : T.KeysKept S S') (hk : Z.checkKeys S' = true) :
    (Z.vrestrict I T S S').checkKeys S = true := by
  simp only [checkKeys, List.all_eq_true] at hk ⊢
  intro k hkS
  have he := (hS.allKeys_spec hkS).1
  simp only [checkKey, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hk ⊢
  intro i hi j hj
  rw [size_vrestrict he] at hi hj
  by_cases hij : i = j
  · exact Or.inl hij
  refine Or.inr ?_
  by_contra hag
  simp only [Bool.not_eq_false, agree, List.all_eq_true, decide_eq_true_eq] at hag
  have hxi : (Z.vrestrict I T S S').Has (.ent k.entity i) (.entity k.entity) :=
    ⟨rfl, (size_vrestrict he).symm ▸ hi⟩
  have hxj : (Z.vrestrict I T S S').Has (.ent k.entity j) (.entity k.entity) :=
    ⟨rfl, (size_vrestrict he).symm ▸ hj⟩
  have hfield : ∀ f ∈ k.fields, ∃ yi yj,
      Z.evalV I S' (.ent (T.ent k.entity) i) (T.gen (.entity k.entity) f) = some (rename T yi) ∧
      Z.evalV I S' (.ent (T.ent k.entity) j) (T.gen (.entity k.entity) f) = some (rename T yj) ∧
      yi = yj := by
    intro f hf
    obtain ⟨b, hb⟩ := hS.step?_of_key hkS hf
    obtain ⟨yi, hyi, -, hei⟩ := vrestrict_step hS hZ hT (show S.IsOb (.entity k.entity) from he)
      hxi hb
    obtain ⟨yj, hyj, -, hej⟩ := vrestrict_step hS hZ hT (show S.IsOb (.entity k.entity) from he)
      hxj hb
    refine ⟨yi, yj, hei, hej, ?_⟩
    have := hag f hf
    rw [hyi, hyj] at this
    exact Option.some.inj this
  rcases hK k hkS with ⟨f, hf, hf0⟩ | ⟨⟨e', fs'⟩, hk', hke, hk'f⟩
  · obtain ⟨yi, yj, hei, hej, rfl⟩ := hfield f hf
    rw [hf0] at hei hej
    have := (Option.some.inj hei).trans (Option.some.inj hej).symm
    exact hij (by injection this)
  · simp only at hke hk'f
    subst hke
    have hk'' := hk ⟨T.ent k.entity, fs'⟩ hk' i hi j hj
    rcases hk'' with h | h
    · exact hij h
    · have hag' : Z.agree S' (T.ent k.entity) fs' i j = true := by
        simp only [agree, List.all_eq_true, decide_eq_true_eq]
        intro n' hn'
        obtain ⟨f, hf, hfn⟩ := hk'f n' hn'
        obtain ⟨yi, yj, hei, hej, rfl⟩ := hfield f hf
        rw [hfn, evalV_singleton] at hei hej
        have ei : Z.step S' (.ent (T.ent k.entity) i) n' = some (rename T yi) := hei
        have ej : Z.step S' (.ent (T.ent k.entity) j) n' = some (rename T yi) := hej
        rw [ei, ej]
      rw [hag'] at h
      exact absurd h (by simp)

end FinState

/-! ## Keys through inclusions -/

namespace Schema

variable {S : Schema}

theorem mem_outNames_iff {e n : String} : n ∈ S.outNames e ↔ (e, n) ∈ S.gens := by
  refine ⟨mem_gens_of_mem_outNames, fun h => ?_⟩
  simp only [gens, List.mem_append, List.mem_map, Prod.mk.injEq] at h
  simp only [outNames, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
  rcases h with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
  · exact Or.inl ⟨r, ⟨hr, rfl⟩, rfl⟩
  · exact Or.inr ⟨a, ⟨ha, rfl⟩, rfl⟩

variable {K : ValueType → Type}

/-- `Y` satisfies the keys of `B` on the entity types of `S`. -/
def State.KeysOf (Y : S.State K) (B : Schema) : Prop :=
  ∀ k ∈ B.allKeys, ∀ he : k.entity ∈ S.entities, Y.KeyHolds k.entity he k.fields

/-- A key with more fields imposes less. -/
theorem State.KeyHolds.mono {Y : S.State K} {e : String} {he : e ∈ S.entities}
    {fs fs' : List String} (hsub : ∀ n ∈ fs, n ∈ fs') (h : Y.KeyHolds e he fs) :
    Y.KeyHolds e he fs' :=
  fun x y hxy => h x y fun n hn b hb => hxy n (hsub n hn) b hb

end Schema

namespace Translation

variable {B G : Schema} {K : ValueType → Type}

/-- Along an inclusion, a key on generators of the included schema holds in the
restriction of a state exactly when it holds in the state. -/
theorem keyHolds_restrict_empty (hB : B.WellFormed) (hG : G.WellFormed)
    (hi : ({} : Translation).Valid B G)
    (Y : G.State K) {e : String} (he : e ∈ B.entities) {fs : List String}
    (hfs : ∀ n ∈ fs, (e, n) ∈ B.gens) :
    (restrictState hG hi Y).KeyHolds e he fs ↔ Y.KeyHolds e (hi.entity e he) fs := by
  have hstep : ∀ n ∈ fs, ∃ o, B.step? (.entity e) n = some o := fun n hn =>
    Option.isSome_iff_exists.mp (step?_isSome_iff.mpr (hfs n hn))
  -- The image of a generator of `B` is the generator of `G` of the same name.
  have himage : ∀ (n : String) (b : B.Obj) (hb : B.step? (.entity e) n = some b.1)
      (hb' : G.step? (.entity e) n = some (obj hi b).1),
      functorPath hG hi (B.genPath ⟨.entity e, he⟩ b n hb) =
        G.genPath (obj hi ⟨.entity e, he⟩) (obj hi b) n hb' := fun n b hb hb' =>
    names_injective _ _ (by rw [names_functorPath, names_toPath, mapPath_singleton]; rfl)
  constructor
  · intro h x y hxy
    refine h x y fun n hn b hb => ?_
    have hb' : G.step? (.entity e) n = some (obj hi b).1 := by
      rw [obj_empty]
      exact step?_of_sub hi hb
    change Y.F.map (G.mor (functorPath hG hi (B.genPath ⟨.entity e, he⟩ b n hb))) x =
      Y.F.map (G.mor (functorPath hG hi (B.genPath ⟨.entity e, he⟩ b n hb))) y
    rw [himage n b hb hb']
    exact hxy n hn (obj hi b) hb'
  · intro h x y hxy
    refine h x y fun n hn b' hb' => ?_
    obtain ⟨o, ho⟩ := hstep n hn
    let b : B.Obj := ⟨o, isOb_of_step? hB ho⟩
    have hb : B.step? (.entity e) n = some b.1 := ho
    obtain rfl : b' = obj hi b := Subtype.ext (by
      rw [obj_empty]
      exact Option.some.inj (hb'.symm.trans (step?_of_sub hi hb)))
    have h₁ := hxy n hn b hb
    change Y.F.map (G.mor (functorPath hG hi (B.genPath ⟨.entity e, he⟩ b n hb))) x =
      Y.F.map (G.mor (functorPath hG hi (B.genPath ⟨.entity e, he⟩ b n hb))) y at h₁
    rw [himage n b hb hb'] at h₁
    exact h₁

/-- Along an inclusion, the restriction of a state satisfies the keys of the
included schema exactly when the state satisfies them. -/
theorem keys_restrict_empty_iff (hB : B.WellFormed) (hG : G.WellFormed)
    (hi : ({} : Translation).Valid B G) (Y : G.State K) :
    (restrictState hG hi Y).Keys ↔ Y.KeysOf B := by
  constructor
  · intro h k hk _
    have hk' := hB.allKeys_spec hk
    exact (keyHolds_restrict_empty hB hG hi Y hk'.1 hk'.2).mp (h k hk hk'.1)
  · intro h k hk he
    exact (keyHolds_restrict_empty hB hG hi Y he (hB.allKeys_spec hk).2).mpr
      (h k hk (hi.entity _ he))

end Translation

/-! ## Keys through gluing -/

namespace Schema

variable {B₁ B₂ : Schema}

/-- The generators of a glued schema are those of the two schemas. -/
theorem mem_gens_glue {e n : String} :
    (e, n) ∈ (glue B₁ B₂).gens ↔ (e, n) ∈ B₁.gens ∨ (e, n) ∈ B₂.gens := by
  constructor
  · intro h
    simp only [gens, glue, List.map_append, List.mem_append, List.mem_map, List.mem_filter,
      Prod.mk.injEq] at h
    rcases h with ((⟨r, hr, rfl, rfl⟩ | ⟨r, ⟨hr, -⟩, rfl, rfl⟩) |
      (⟨a, ha, rfl, rfl⟩ | ⟨a, ⟨ha, -⟩, rfl, rfl⟩))
    · exact Or.inl (List.mem_append_left _ (List.mem_map_of_mem hr))
    · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem hr))
    · exact Or.inl (List.mem_append_right _ (List.mem_map_of_mem ha))
    · exact Or.inr (List.mem_append_right _ (List.mem_map_of_mem ha))
  · intro h
    by_cases h₁ : (e, n) ∈ B₁.gens
    · simp only [gens, List.mem_append, List.mem_map, Prod.mk.injEq] at h₁
      simp only [gens, glue, List.map_append, List.mem_append, List.mem_map, List.mem_filter,
        Prod.mk.injEq]
      rcases h₁ with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
      · exact Or.inl (Or.inl ⟨r, hr, rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨a, ha, rfl, rfl⟩)
    · have h₂ := h.resolve_left h₁
      simp only [gens, List.mem_append, List.mem_map, Prod.mk.injEq] at h₂
      simp only [gens, glue, List.map_append, List.mem_append, List.mem_map, List.mem_filter,
        Prod.mk.injEq, decide_eq_true_eq]
      rcases h₂ with ⟨r, hr, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
      · exact Or.inl (Or.inr ⟨r, ⟨hr, by
          simpa only [gens, List.mem_append, List.mem_map, Prod.mk.injEq] using h₁⟩, rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨a, ⟨ha, by
          simpa only [gens, List.mem_append, List.mem_map, Prod.mk.injEq] using h₁⟩, rfl, rfl⟩)

theorem outNames_subset_glue_left {e n : String} (h : n ∈ B₁.outNames e) :
    n ∈ (glue B₁ B₂).outNames e :=
  mem_outNames_iff.mpr (mem_gens_glue.mpr (Or.inl (mem_outNames_iff.mp h)))

theorem outNames_subset_glue_right {e n : String} (h : n ∈ B₂.outNames e) :
    n ∈ (glue B₁ B₂).outNames e :=
  mem_outNames_iff.mpr (mem_gens_glue.mpr (Or.inr (mem_outNames_iff.mp h)))

end Schema

namespace Gluing

variable (D : Gluing) {K : ValueType → Type}

/-- A state of the glued schema satisfies the keys of the two schemas exactly when
its two restrictions satisfy their keys. -/
theorem keysOf_iff (X : D.glued.State K) :
    (X.KeysOf D.left ∧ X.KeysOf D.right) ↔
      ((D.stateEquiv X).1.1.Keys ∧ (D.stateEquiv X).1.2.Keys) :=
  and_congr (Translation.keys_restrict_empty_iff D.wf_left D.wf_glued D.inl_valid X).symm
    (Translation.keys_restrict_empty_iff D.wf_right D.wf_glued D.inr_valid X).symm

/-- A state of the glued schema that satisfies the keys of the two schemas satisfies
the keys of the glued schema: its declared keys and subtypes are those of the two,
and a value object has at least the fields it has in either. -/
theorem keys_of_keysOf {X : D.glued.State K} (hl : X.KeysOf D.left) (hr : X.KeysOf D.right) :
    X.Keys := by
  intro k hk he
  simp only [glued, allKeys, glue, List.mem_append, List.mem_map, List.mem_filter] at hk
  rcases hk with ((hk | ⟨hk, -⟩) | ⟨e, he₁ | ⟨he₂, -⟩, rfl⟩) | ⟨s, hs | ⟨hs, -⟩, rfl⟩
  · exact hl k (List.mem_append_left _ (List.mem_append_left _ hk)) he
  · exact hr k (List.mem_append_left _ (List.mem_append_left _ hk)) he
  · exact (hl ⟨e, D.left.outNames e⟩
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he₁))) he).mono
      fun n hn => outNames_subset_glue_left (B₁ := D.left) (B₂ := D.right) hn
  · exact (hr ⟨e, D.right.outNames e⟩
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he₂))) he).mono
      fun n hn => outNames_subset_glue_right (B₁ := D.left) (B₂ := D.right) hn
  · exact hl _ (List.mem_append_right _ (List.mem_map_of_mem hs)) he
  · exact hr _ (List.mem_append_right _ (List.mem_map_of_mem hs)) he

/-- Data gluing for states that satisfy the keys: a state of the glued schema that
satisfies the keys of the two schemas is a pair of states that satisfy their keys
and have equal restrictions to the kernel. -/
def keyedStateEquiv :
    { X : D.glued.State K // X.KeysOf D.left ∧ X.KeysOf D.right } ≃
      { P : D.left.State K × D.right.State K //
        Translation.restrictState D.wf_left D.gluable.left P.1 =
          Translation.restrictState D.wf_right D.gluable.right P.2 ∧ P.1.Keys ∧ P.2.Keys } :=
  (D.stateEquiv.subtypeEquiv (q := fun P => P.1.1.Keys ∧ P.1.2.Keys) D.keysOf_iff).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _
      fun P : D.left.State K × D.right.State K => P.1.Keys ∧ P.2.Keys)

end Gluing

/-! ## Keys through the aggregates -/

namespace Schema

variable {S : Schema} {K : ValueType → Type}

/-- Out of an entity type of an aggregate, the aggregate schema has the generators
of `S`. -/
theorem outNames_aggregateSchema {A : Aggregate} {e : String} (he : e ∈ A.entities) :
    (S.aggregateSchema A).outNames e = S.outNames e := by
  simp only [outNames, aggregateSchema, aggregateBase, aggRefs, aggAttrs, List.filter_filter]
  congr 2
  · refine List.filter_congr fun r _ => ?_
    by_cases h : r.src = e
    · subst h
      simp [he]
    · simp [h]
  · refine List.filter_congr fun a _ => ?_
    by_cases h : a.src = e
    · subst h
      simp [he]
    · simp [h]

variable (hS : S.WellFormed) (hne : S.entities ≠ [])

/-- A state of the internal schema satisfies the keys of `S` exactly when it
satisfies the keys of every aggregate schema. -/
theorem keys_iff_keysOf_aggregates (Y : S.internalSchema.State K) :
    Y.Keys ↔ ∀ A : S.Aggs, Y.KeysOf (S.aggregateSchema A.1) := by
  constructor
  · intro h A k hk he
    simp only [allKeys, aggregateSchema, aggregateBase, List.mem_append, List.mem_map,
      List.mem_filter, decide_eq_true_eq] at hk
    rcases hk with (⟨hk, -⟩ | ⟨e, ⟨he₁, heA⟩, rfl⟩) | ⟨s, ⟨hs, -⟩, rfl⟩
    · exact h k (List.mem_append_left _ (List.mem_append_left _ hk)) he
    · have hk := h ⟨e, S.outNames e⟩
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he₁))) he
      change Y.KeyHolds e he ((S.aggregateSchema A.1).outNames e)
      rw [outNames_aggregateSchema heA]
      exact hk
    · exact h _ (List.mem_append_right _ (List.mem_map_of_mem hs)) he
  · intro h k hk he
    obtain ⟨A, hA, heA⟩ := exists_aggregate (S := S) (show k.entity ∈ S.entities from he)
    have hk' : k ∈ (S.aggregateSchema A).allKeys := by
      change k ∈ S.allKeys at hk
      simp only [allKeys, List.mem_append, List.mem_map] at hk
      rcases hk with (hk | ⟨e, he₁, rfl⟩) | ⟨s, hs, rfl⟩
      · exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_filter.mpr ⟨hk, decide_eq_true heA⟩))
      · refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
          ⟨e, List.mem_filter.mpr ⟨he₁, decide_eq_true heA⟩, ?_⟩))
        rw [outNames_aggregateSchema heA]
      · exact List.mem_append_right _ (List.mem_map.mpr
          ⟨s, List.mem_filter.mpr ⟨hs, decide_eq_true heA⟩, rfl⟩)
    exact h ⟨A, hA⟩ k hk' he

include hS in
/-- A state of the internal schema satisfies the keys exactly when each of its
aggregate parts satisfies the keys of its aggregate schema. -/
theorem keys_iff_parts (Y : S.internalSchema.State K) :
    Y.Keys ↔ ∀ A : S.Aggs, (parts hS Y A).Keys :=
  (keys_iff_keysOf_aggregates Y).trans (forall_congr' fun A =>
    (Translation.keys_restrict_empty_iff (aggregateSchema_wellFormed hS A.2)
      (internalSchema_wellFormed hS) (aggregate_valid hS A.2) Y).symm)

/-- Consistency inside the aggregates, with keys: a state of the internal schema
that satisfies the keys is a compatible family of states of the aggregate schemas,
each of which satisfies the keys of its aggregate schema. -/
noncomputable def keyedFamilyEquiv :
    { Y : S.internalSchema.State K // Y.Keys } ≃
      { X : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K // Compatible X ∧ ∀ A, (X A).Keys } :=
  ((familyEquiv hS hne).subtypeEquiv (q := fun X => ∀ A, (X.1 A).Keys) (keys_iff_parts hS)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _
      fun X : ∀ A : S.Aggs, (S.aggregateSchema A.1).State K => ∀ A, (X A).Keys)

end Schema

end DDD
