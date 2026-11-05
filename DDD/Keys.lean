import DDD.VData

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

end DDD
