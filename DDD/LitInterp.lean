import DDD.VStates
import DDD.ConvComplete

/-!
# The literal interpretation

The literals with `TypeList.convLit` form an interpretation of the value types of a sound
list (`TypeList.litInterp`). The values of `v` are the literals that fit `v`
(`TypeList.Fits`): an integer, a boolean or text as the type requires, the text of a
timestamp with more than ten characters, a value of an enumeration, a record with each of
its fields, `null` at an optional type. Every literal in normal form fits its type
(`fits_of_normalize`).

- Each conversion takes a literal that fits its source to one that fits its target
  (`convLit_fits`, `applyLit_fits`).
- The literals that fit a type satisfy the equations of `Basic` (`applyLit_basic`): a
  coercion keeps the literal, a path of tables computes the image of the value, `some`
  keeps the literal, the date and the time of a timestamp are those of its date and time,
  and `string` gives the text of the literal through a coercion as well.
- `applyLit` and `convLit` compute the interpretation on paths and on conversions
  (`applyLit_litInterp`, `convLit_litInterp`); the result of a claim `conversion` is the
  image of its literal (`applyLit_normal`).
- Paths of conversions that are equal in `S.vcat L` take a literal that fits their source
  to the same literal (`Schema.applyLit_eq_of_vPathEq`).
-/

namespace DDD

open CategoryTheory

namespace TypeList

variable (L : TypeList)

/-! ## Literals that fit a type -/

/-- A literal of the built-in type `b`: an integer, a boolean or text, as the type
requires; the text of a timestamp has more than ten characters. -/
def FitsBuiltin : ValueType → Lit → Prop
  | .int, x => ∃ i, x = .int i
  | .bool, x => ∃ b, x = .bool b
  | .timestamp, x => ∃ s, x = .text s ∧ 10 < s.length
  | .decimal, x | .string, x | .date, x | .uuid, x | .datetime, x | .time, x | .duration, x =>
    ∃ s, x = .text s
  | _, _ => False

/-- A literal of a type that is not a record: a value of an enumeration, a literal of the
base of a named type, `null` or a literal of the base of an optional type. -/
def FitsFlat : ValueType → Lit → Prop
  | .named n, x => match L.lookup n with
    | some (.enum vs) => ∃ s, x = .text s ∧ s ∈ vs
    | some (.over b) => FitsBuiltin b x
    | _ => False
  | .optional v, x => x = .null ∨ FitsFlat v x
  | v, x => FitsBuiltin v x

/-- A literal fits the value type `v`: it has the shape that the conversions out of `v`
need. A record has each of its fields, with a literal that fits the type of the field. -/
def Fits : ValueType → Lit → Prop
  | .named n, x => match L.lookup n with
    | some (.record fs) =>
      ∃ ys, x = .record ys ∧ ∀ f ∈ fs, ∃ y, ys.lookup f.1 = some y ∧ L.FitsFlat f.2 y
    | _ => L.FitsFlat (.named n) x
  | .optional v, x => x = .null ∨ Fits v x
  | v, x => FitsBuiltin v x

variable {L}

theorem fits_builtin {b : ValueType} (hb : b.isBuiltin = true) (x : Lit) :
    L.Fits b x ↔ FitsBuiltin b x := by
  cases b <;> first | exact Iff.rfl | exact absurd hb (by simp [ValueType.isBuiltin])

theorem fits_over {m : String} {b : ValueType} (hb : L.base? m = some b) (x : Lit) :
    L.Fits (.named m) x ↔ FitsBuiltin b x := by
  have := base?_some hb
  simp [Fits, FitsFlat, this]

theorem fits_optional {v : ValueType} (x : Lit) : L.Fits (.optional v) x ↔ x = .null ∨ L.Fits v x :=
  Iff.rfl

theorem not_fitsBuiltin_null (b : ValueType) : ¬ FitsBuiltin b .null := by
  cases b <;> simp [FitsBuiltin]

theorem not_fits_null {v : ValueType} (hv : v.isPlain = true) : ¬ L.Fits v .null := by
  cases v with
  | named n =>
    simp only [Fits, FitsFlat]
    split
    · simp
    · split <;> simp [not_fitsBuiltin_null]
  | optional _ => simp [ValueType.isPlain] at hv
  | _ => exact not_fitsBuiltin_null _

/-- On a type of a field, fitting is fitting as a type that is not a record. -/
theorem fits_of_flat : ∀ {t : ValueType}, L.flat t = true → ∀ {x : Lit}, L.FitsFlat t x → L.Fits t x
  | .named n, hf, x, hx => by
    simp only [flat] at hf
    simp only [Fits]
    split
    · rename_i fs hfs
      simp [hfs] at hf
    · exact hx
  | .optional (.optional _), hf, _, _ => by simp [flat] at hf
  | .optional (.named n), hf, x, hx => by
    rcases hx with hx | hx
    · exact .inl hx
    · exact .inr (fits_of_flat (t := .named n) hf hx)
  | .optional .int, _, _, hx | .optional .decimal, _, _, hx | .optional .string, _, _, hx
  | .optional .date, _, _, hx | .optional .uuid, _, _, hx | .optional .bool, _, _, hx
  | .optional .datetime, _, _, hx | .optional .timestamp, _, _, hx | .optional .time, _, _, hx
  | .optional .duration, _, _, hx => hx
  | .int, _, _, hx | .decimal, _, _, hx | .string, _, _, hx | .date, _, _, hx | .uuid, _, _, hx
  | .bool, _, _, hx | .datetime, _, _, hx | .timestamp, _, _, hx | .time, _, _, hx
  | .duration, _, _, hx => hx

/-! ## Conversions of literals -/

theorem convLit_plain {v : ValueType} (hv : v.isPlain = true) (n : String) (x : Lit) :
    L.convLit v n x = L.plainConvLit v n x := by
  cases v <;> first | rfl | exact absurd hv (by simp [ValueType.isPlain])

theorem convLit_null (u : ValueType) (n : String) : L.convLit (.optional u) n .null = .ok .null :=
  rfl

theorem convLit_lift {u : ValueType} {x : Lit} (hx : x ≠ .null) (n : String) :
    L.convLit (.optional u) n x = L.plainConvLit u n x := by
  cases x <;> first | rfl | exact absurd rfl hx

theorem plainConvLit_some (v : ValueType) (x : Lit) : L.plainConvLit v "some" x = .ok x := by
  simp [plainConvLit]; rfl

theorem plainConvLit_string (v : ValueType) (x : Lit) :
    L.plainConvLit v "string" x = .ok (.text x.str) := by
  simp [plainConvLit]; rfl

/-- A coercion keeps the literal. -/
theorem plainConvLit_coerce {v w : ValueType} {n : String} (hn : n ≠ "some") (hs : n ≠ "string")
    (hb : builtinConv? v n = none) (hc : L.coerce? v n = some w) (x : Lit) :
    L.plainConvLit v n x = .ok x := by
  unfold plainConvLit
  rw [if_neg hn, if_neg hs]
  split <;> first | (simp [builtinConv?] at hb; done) | (rw [if_pos (by simp [hc])]; rfl)

theorem plainConvLit_table {v : ValueType} {n : String} {t : Table} (hn : n ≠ "some")
    (hs : n ≠ "string") (hb : builtinConv? v n = none) (hc : L.coerce? v n = none)
    (ht : L.table? v n = some t) {x : Lit} {y : String}
    (hy : ((finKey x).bind fun k => t.rows.lookup k) = some y) :
    L.plainConvLit v n x = .ok (finLit t.target y) := by
  unfold plainConvLit
  rw [if_neg hn, if_neg hs]
  split <;> first
    | (simp [builtinConv?] at hb; done)
    | (rw [if_neg (by simp [hc]), ht]; simp [hy]; rfl)

theorem plainConvLit_field {v : ValueType} {n : String} (hn : n ≠ "some") (hs : n ≠ "string")
    (hb : builtinConv? v n = none) (hc : L.coerce? v n = none) (ht : L.table? v n = none)
    {ys : List (String × Lit)} {y : Lit} (hy : ys.lookup n = some y) :
    L.plainConvLit v n (.record ys) = .ok y := by
  unfold plainConvLit
  rw [if_neg hn, if_neg hs]
  split <;> first
    | (simp [builtinConv?] at hb; done)
    | (rw [if_neg (by simp [hc]), ht]; simp [hy]; rfl)

theorem lookup_of_mem_keys {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α}, k ∈ l.map Prod.fst → ∃ y, l.lookup k = some y
  | [], _, h => by simp at h
  | (k', y) :: l, k, h => by
    rw [List.lookup_cons]
    by_cases e : k = k'
    · subst e
      exact ⟨y, by simp⟩
    · have : (k == k') = false := by simpa using e
      rw [this]
      simp only [List.map_cons, List.mem_cons, e, false_or] at h
      exact lookup_of_mem_keys h

/-- The value of a finite type that a literal is, as the text of the rows of tables. -/
theorem finKey_of_fits {v : ValueType} (hv : (L.values? v).isSome) {x : Lit} (hx : L.Fits v x) :
    ∃ k, finKey x = some k ∧ k ∈ (L.values? v).getD [] ∧ finLit v k = x := by
  rcases values?_isSome hv with rfl | ⟨e, vs, rfl, he⟩
  · obtain ⟨b, rfl⟩ := hx
    cases b <;> exact ⟨_, rfl, by simp only [values?, Option.getD_some]; decide, rfl⟩
  · simp only [Fits, FitsFlat, he] at hx
    obtain ⟨s, rfl, hs⟩ := hx
    exact ⟨s, rfl, by simp [values?, he, hs], by simp [finLit]⟩

theorem fits_finLit {w : ValueType} (hw : (L.values? w).isSome) {y : String}
    (hy : y ∈ (L.values? w).getD []) : L.Fits w (finLit w y) := by
  rcases values?_isSome hw with rfl | ⟨e, vs, rfl, he⟩
  · exact ⟨_, rfl⟩
  · simp only [values?, he, Option.getD_some] at hy
    simp only [Fits, FitsFlat, he, finLit]
    exact ⟨y, by simp, hy⟩

/-- A conversion out of a plain type takes a literal that fits its source to one that
fits its target. -/
theorem plainConvLit_fits (hL : L.Sound) {v w : ValueType} {n : String} (hv : v.isPlain = true)
    (h : L.plainConv? v n = some w) {x : Lit} (hx : L.Fits v x) :
    ∃ y, L.plainConvLit v n x = .ok y ∧ L.Fits w y := by
  by_cases hn : n = "some"
  · subst hn
    simp only [plainConv?, if_true, Option.some.injEq] at h
    subst h
    exact ⟨x, plainConvLit_some v x, .inr hx⟩
  rcases plainConv?_cases hn h with ⟨rfl, -, rfl⟩ | ⟨hs, hb⟩ | ⟨hs, hb, hc⟩ |
      ⟨hs, hb, hc, t, ht, rfl⟩ | ⟨hs, hb, hc, ht, hf⟩
  · exact ⟨_, plainConvLit_string v x, ⟨_, rfl⟩⟩
  · unfold builtinConv? at hb
    split at hb <;> cases hb
    · obtain ⟨s, rfl, -⟩ := hx
      exact ⟨_, by simp [plainConvLit]; rfl, ⟨_, rfl⟩⟩
    · obtain ⟨s, rfl, -⟩ := hx
      exact ⟨_, by simp [plainConvLit]; rfl, ⟨_, rfl⟩⟩
    · obtain ⟨s, rfl, -⟩ := hx
      exact ⟨_, by simp [plainConvLit]; rfl, ⟨_, rfl⟩⟩
    · obtain ⟨s, rfl⟩ := hx
      exact ⟨_, by simp [plainConvLit]; rfl, ⟨_, rfl⟩⟩
    · obtain ⟨s, rfl⟩ := hx
      exact ⟨_, by simp [plainConvLit]; rfl, ⟨_, rfl⟩⟩
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨_, by simp [plainConvLit]; rfl, ⟨_, rfl⟩⟩
  · refine ⟨x, plainConvLit_coerce hn hs hb hc x, ?_⟩
    rcases coerce?_some hc with ⟨m, b, rfl, hbm, rfl, rfl⟩ | ⟨hvb, hbn, rfl⟩
    · rw [fits_over hbm] at hx
      exact (fits_builtin (base?_isBuiltin hL hbm) x).mpr hx
    · rw [fits_over hbn]
      exact (fits_builtin hvb x).mp hx
  · obtain ⟨hvs, hwt⟩ := table?_values hL ht
    obtain ⟨-, -, hsrc⟩ := table?_some ht
    obtain ⟨k, hk, hkv, -⟩ := finKey_of_fits hvs hx
    have hsnd := table?_sound hL ht
    have hcov : k ∈ t.rows.map Prod.fst := hsnd.2.2.2.2.2.2.2.2 k (by rwa [hsrc])
    obtain ⟨y, hy⟩ := lookup_of_mem_keys hcov
    have hyt : y ∈ (L.values? t.target).getD [] := hsnd.2.2.2.2.2.2.2.1 _ (mem_of_lookup hy)
    exact ⟨_, plainConvLit_table hn hs hb hc ht (by simp [hk, hy]), fits_finLit hwt hyt⟩
  · obtain ⟨r, fs, rfl, hfs⟩ := field?_some hf
    have hfs' : L.lookup r = some (.record fs) := by
      unfold fields? at hfs
      split at hfs
      · rename_i fs' hl
        obtain rfl := Option.some.inj hfs
        exact hl
      · cases hfs
    simp only [Fits, hfs'] at hx
    obtain ⟨ys, rfl, hys⟩ := hx
    simp only [field?, hfs, Option.bind_some] at hf
    have hmem : (n, w) ∈ fs := mem_of_lookup hf
    obtain ⟨y, hy, hyf⟩ := hys (n, w) hmem
    have hflat := hL.fields _ (mem_of_lookup hfs') fs rfl (n, w) hmem
    exact ⟨y, plainConvLit_field hn hs hb hc ht hy, fits_of_flat hflat hyf⟩

/-- A conversion takes a literal that fits its source to one that fits its target; a lift
keeps `null`. -/
theorem convLit_fits (hL : L.Sound) {v w : ValueType} {n : String} (h : L.conv? v n = some w)
    {x : Lit} (hx : L.Fits v x) : ∃ y, L.convLit v n x = .ok y ∧ L.Fits w y := by
  cases v with
  | optional u =>
    obtain ⟨hu, w', hw', hwp, rfl⟩ := conv?_optional h
    rcases hx with rfl | hx
    · exact ⟨.null, rfl, .inl rfl⟩
    · obtain ⟨y, hy, hfy⟩ := plainConvLit_fits hL hu hw' hx
      exact ⟨y, by rw [convLit_lift (fun e => not_fits_null hu (e ▸ hx)), hy], .inr hfy⟩
  | _ =>
    rw [conv?_plain rfl] at h
    exact plainConvLit_fits hL rfl h hx

theorem applyLit_cons {v w : ValueType} {n : String} (h : L.conv? v n = some w) (ns : List String)
    (x : Lit) : L.applyLit v (n :: ns) x = (L.convLit v n x).bind (L.applyLit w ns) := by
  simp only [applyLit, h]
  rfl

/-- A path of conversions takes a literal that fits its source to one that fits its
target. -/
theorem applyLit_fits (hL : L.Sound) : ∀ {l : List String} {v o : ValueType} {x : Lit},
    L.convTgt? v l = some o → L.Fits v x → ∃ y, L.applyLit v l x = .ok y ∧ L.Fits o y
  | [], v, o, x, h, hx => by
    rw [convTgt?_nil, Option.some.injEq] at h
    subst h
    exact ⟨x, rfl, hx⟩
  | n :: ns, v, o, x, h, hx => by
    rw [convTgt?_cons] at h
    cases hc : L.conv? v n with
    | none => simp [hc] at h
    | some w =>
      rw [hc, Option.bind_some] at h
      obtain ⟨y, hy, hfy⟩ := convLit_fits hL hc hx
      obtain ⟨z, hz, hfz⟩ := applyLit_fits hL h hfy
      exact ⟨z, by rw [applyLit_cons hc, hy]; exact hz, hfz⟩

/-! ## The equations hold for literals -/

theorem bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α).bind f = f a := rfl

theorem convLit_string {v : ValueType} (hv : v.isPlain = true) (x : Lit) :
    L.convLit v "string" x = .ok (.text x.str) := by
  rw [convLit_plain hv, plainConvLit_string]

/-- A coercion to the base of a named type keeps the literal. -/
theorem convLit_down (hL : L.Sound) {m : String} {b : ValueType} (hb : L.base? m = some b)
    {x : Lit} (hx : L.Fits (.named m) x) : L.convLit (.named m) b.text x = .ok x := by
  have hbb := base?_isBuiltin hL hb
  rw [convLit_plain rfl]
  by_cases hs : b.text = "string"
  · obtain rfl : b = .string := text_inj hbb rfl hs
    rw [fits_over hb] at hx
    obtain ⟨s, rfl⟩ := hx
    exact plainConvLit_string _ _
  · exact plainConvLit_coerce (text_ne_some hbb) hs (by simp [builtinConv?])
      (coerce?_named hb) x

/-- A coercion into a named type keeps the literal. -/
theorem convLit_up (hL : L.Sound) {m : String} {b : ValueType} (hb : L.base? m = some b)
    (hm : m ≠ "some") (x : Lit) : L.convLit b m x = .ok x := by
  have hbb := base?_isBuiltin hL hb
  rw [convLit_plain (isPlain_of_isBuiltin hbb)]
  have hbn : builtinConv? b m = none := by
    cases h : builtinConv? b m with
    | none => rfl
    | some w => exact absurd (builtinConv?_name h) (base?_not_builtinName hL hb)
  exact plainConvLit_coerce hm (base?_ne hL hb (by simp [builtinNames])) hbn
    (coerce?_builtin hbb hb) x

theorem fits_up {m : String} {b : ValueType} (hL : L.Sound) (hb : L.base? m = some b) {x : Lit}
    (hx : L.Fits b x) : L.Fits (.named m) x := by
  rw [fits_over hb]
  exact (fits_builtin (base?_isBuiltin hL hb) x).mp hx

theorem finKey_finLit {w : ValueType} (hw : (L.values? w).isSome) {y : String}
    (hy : y ∈ (L.values? w).getD []) : finKey (finLit w y) = some y := by
  rcases values?_isSome hw with rfl | ⟨e, vs, rfl, -⟩
  · simp only [values?, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> rfl
  · simp [finLit, finKey]

/-- A path of tables takes the literal of a value to the literal of its image. -/
theorem applyLit_tables (hL : L.Sound) : ∀ {ns : List String} {u w : ValueType},
    (L.values? u).isSome → L.tablesTgt? u ns = some w → ∀ {x : Lit} {k : String},
      L.Fits u x → finKey x = some k → k ∈ (L.values? u).getD [] →
      ∃ y, L.tablesApply? u ns k = some y ∧ L.applyLit u ns x = .ok (finLit w y)
  | [], u, w, hu, ht, x, k, hx, hk, hkv => by
    rw [tablesTgt?, Option.some.injEq] at ht
    subst ht
    obtain ⟨k', hk', -, hfin⟩ := finKey_of_fits hu hx
    rw [hk] at hk'
    obtain rfl := Option.some.inj hk'
    exact ⟨k, rfl, by rw [hfin]; rfl⟩
  | n :: ns, u, w, hu, ht, x, k, hx, hk, hkv => by
    simp only [tablesTgt?] at ht
    cases htb : L.table? u n with
    | none => simp [htb] at ht
    | some t =>
      rw [htb, Option.bind_some] at ht
      obtain ⟨-, -, hsrc⟩ := table?_some htb
      have hsnd := table?_sound hL htb
      obtain ⟨hn₁, hn₂, hn₃⟩ := table?_name hL htb
      have hcov : k ∈ t.rows.map Prod.fst := hsnd.2.2.2.2.2.2.2.2 k (by rwa [hsrc])
      obtain ⟨y₁, hy₁⟩ := lookup_of_mem_keys hcov
      have hwt := (table?_values hL htb).2
      have hy₁t : y₁ ∈ (L.values? t.target).getD [] := hsnd.2.2.2.2.2.2.2.1 _ (mem_of_lookup hy₁)
      have hc := conv?_table hL htb
      have hs : n ≠ "string" := fun e => hn₁ (e ▸ by simp [builtinNames])
      have hb : builtinConv? u n = none := by
        cases h : builtinConv? u n with
        | none => rfl
        | some w => exact absurd (builtinConv?_name h) hn₁
      have hco : L.coerce? u n = none := by
        cases h : L.coerce? u n with
        | none => rfl
        | some w =>
          rcases coerce?_some h with ⟨m, b, rfl, hbm, rfl, -⟩ | ⟨-, hbm, -⟩
          · exact absurd (base?_of_values? hu) (by simp [hbm])
          · simp [base?, hn₂] at hbm
      have hcl : L.convLit u n x = .ok (finLit t.target y₁) := by
        rw [convLit_plain (isPlain_of_values? hu)]
        exact plainConvLit_table hn₃ hs hb hco htb (by simp [hk, hy₁])
      obtain ⟨y, hy, hap⟩ := applyLit_tables hL hwt ht (fits_finLit hwt hy₁t)
        (finKey_finLit hwt hy₁t) hy₁t
      refine ⟨y, ?_, ?_⟩
      · simp [tablesApply?, htb, hy₁, hy]
      · rw [applyLit_cons hc, hcl]
        exact hap

theorem applyLit_null : ∀ {l : List String} {p r : ValueType},
    L.convTgt? (.optional p) l = some r → L.applyLit (.optional p) l .null = .ok .null
  | [], _, _, _ => rfl
  | n :: ns, p, r, h => by
    rw [convTgt?_cons] at h
    cases hc : L.conv? (.optional p) n with
    | none => simp [hc] at h
    | some y =>
      rw [hc, Option.bind_some] at h
      obtain ⟨-, w, -, -, rfl⟩ := conv?_optional hc
      rw [applyLit_cons hc, convLit_null]
      exact applyLit_null h

theorem applyLit_lift (hL : L.Sound) : ∀ {l : List String} {p r : ValueType} {x : Lit},
    L.convTgt? (.optional p) l = some r → L.Fits p x →
      L.applyLit (.optional p) l x = L.applyLit p l x
  | [], _, _, _, _, _ => rfl
  | n :: ns, p, r, x, h, hx => by
    rw [convTgt?_cons] at h
    cases hc : L.conv? (.optional p) n with
    | none => simp [hc] at h
    | some y =>
      rw [hc, Option.bind_some] at h
      obtain ⟨hp, w, hw, hwp, rfl⟩ := conv?_optional hc
      have hpw : L.conv? p n = some w := by rw [conv?_plain hp, hw]
      obtain ⟨z, hz, hfz⟩ := plainConvLit_fits hL hp hw hx
      rw [applyLit_cons hc, applyLit_cons hpw, convLit_lift (fun e => not_fits_null hp (e ▸ hx)),
        convLit_plain hp, hz]
      exact applyLit_lift hL h hfz

theorem take_dropLast {α : Type} {l : List α} (h : 10 < l.length) :
    l.dropLast.take 10 = l.take 10 := by
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  omega

theorem drop_dropLast {α : Type} (l : List α) (n : Nat) :
    l.dropLast.drop n = (l.drop n).dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, List.drop_take, List.length_drop]
  congr 1
  omega

/-- The literals that fit a type satisfy the equations between conversions. -/
theorem applyLit_basic (hL : L.Sound) {u o : ValueType} {l r : List String} (h : L.Basic u l r)
    (hl : L.convTgt? u l = some o) (hr : L.convTgt? u r = some o) {x : Lit} (hx : L.Fits u x) :
    L.applyLit u l x = L.applyLit u r x := by
  induction h generalizing o x with
  | @coerceBack m b hb =>
    have hbb := base?_isBuiltin hL hb
    have hm : m ≠ "some" := by
      rintro rfl
      rw [convTgt?_nil, Option.some.injEq] at hr
      subst hr
      rw [convTgt?_cons, conv?_down hL hb, Option.bind_some, convTgt?_singleton,
        conv?_plain (isPlain_of_isBuiltin hbb)] at hl
      simp [plainConv?] at hl
    rw [applyLit_cons (conv?_down hL hb), convLit_down hL hb hx, bind_ok,
      applyLit_cons (conv?_up hL hb hm), convLit_up hL hb hm, bind_ok]
  | @coerceThere m b hb =>
    have hbb := base?_isBuiltin hL hb
    have hm : m ≠ "some" := by
      rintro rfl
      rw [convTgt?_nil, Option.some.injEq] at hr
      subst hr
      rw [convTgt?_cons, conv?_plain (isPlain_of_isBuiltin hbb)] at hl
      simp only [plainConv?, if_true, Option.bind_some] at hl
      obtain ⟨q, e, -⟩ := convTgt?_of_optional hl
      rw [e] at hbb
      cases hbb
    rw [applyLit_cons (conv?_up hL hb hm), convLit_up hL hb hm, bind_ok,
      applyLit_cons (conv?_down hL hb), convLit_down hL hb (fits_up hL hb hx), bind_ok]
  | @tables v ns ns' h₁ h₂ =>
    obtain ⟨hv, -⟩ := tablesFn?_isSome.mp h₁
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hv
    have htgt := tablesTgt?_of_tablesFn? h₂ h₁
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (tablesFn?_isSome.mp h₁).2
    have happ := tablesFn?_eq hxs h₂ ⟨htgt, (tablesFn?_isSome.mp h₁).2⟩
    obtain ⟨k, hk, hkv, -⟩ := finKey_of_fits hv hx
    obtain ⟨y, hy, hay⟩ := applyLit_tables hL hv hw hx hk hkv
    obtain ⟨y', hy', hay'⟩ := applyLit_tables hL hv (htgt ▸ hw) hx hk hkv
    have e : y = y' :=
      Option.some.inj (hy.symm.trans ((happ k (by simpa [hxs] using hkv)).trans hy'))
    rw [hay, hay', e]
  | @some v w n hv hn hw hwp =>
    have hs : L.conv? v "some" = some (.optional v) := by rw [conv?_plain hv]; simp [plainConv?]
    have hvn : L.conv? v n = some w := by rw [conv?_plain hv, hw]
    have hon : L.conv? (.optional v) n = some (.optional w) := conv?_lift hv hwp hvn
    have hws : L.conv? w "some" = some (.optional w) := by rw [conv?_plain hwp]; simp [plainConv?]
    obtain ⟨y, hy, -⟩ := plainConvLit_fits hL hv hw hx
    rw [applyLit_cons hs, convLit_plain hv, plainConvLit_some, bind_ok, applyLit_cons hon,
      convLit_lift (fun e => not_fits_null hv (e ▸ hx)), applyLit_cons hvn, convLit_plain hv, hy]
    simp only [bind_ok]
    rw [applyLit_cons hws, convLit_plain hwp, plainConvLit_some]
    rfl
  | date =>
    obtain ⟨s, rfl, hs⟩ := hx
    simp [applyLit, conv?, plainConv?, builtinConv?, convLit, plainConvLit, String.toList_ofList,
      take_dropLast (show 10 < s.toList.length by simpa using hs)]
  | time =>
    obtain ⟨s, rfl, -⟩ := hx
    simp [applyLit, conv?, plainConv?, builtinConv?, convLit, plainConvLit, String.toList_ofList,
      drop_dropLast]
  | @stringBack m b hb =>
    have hbb := base?_isBuiltin hL hb
    have hbp := isPlain_of_isBuiltin hbb
    have hbs : b ≠ .string := by
      rintro rfl
      rw [convTgt?_cons, conv?_down hL hb, Option.bind_some, convTgt?_singleton] at hl
      simp [conv?, plainConv?] at hl
    rw [applyLit_cons (conv?_down hL hb), convLit_down hL hb hx, bind_ok,
      applyLit_cons (conv?_string hbp hbs), convLit_string hbp,
      applyLit_cons (conv?_string (u := .named m) rfl (by simp)), convLit_string rfl]
  | @stringThere m b hb =>
    have hbb := base?_isBuiltin hL hb
    have hbp := isPlain_of_isBuiltin hbb
    have hbs : b ≠ .string := by
      rintro rfl
      rw [convTgt?_singleton] at hr
      simp [conv?, plainConv?] at hr
    have hm : m ≠ "some" := by
      rintro rfl
      rw [convTgt?_singleton, conv?_string hbp hbs, Option.some.injEq] at hr
      subst hr
      rw [convTgt?_cons, conv?_plain hbp] at hl
      simp only [plainConv?, if_true, Option.bind_some] at hl
      obtain ⟨q, e, -⟩ := convTgt?_of_optional hl
      cases e
    rw [applyLit_cons (conv?_up hL hb hm), convLit_up hL hb hm, bind_ok,
      applyLit_cons (conv?_string (u := .named m) rfl (by simp)), convLit_string rfl,
      applyLit_cons (conv?_string hbp hbs), convLit_string hbp]
  | @lift p l r hp h ih =>
    obtain ⟨q, rfl, hq, -, -⟩ := convTgt?_of_optional hl
    obtain ⟨q', e, hq', -, -⟩ := convTgt?_of_optional hr
    obtain rfl := ValueType.optional.inj e
    rcases hx with rfl | hx
    · rw [applyLit_null hl, applyLit_null hr]
    · rw [applyLit_lift hL hl hx, applyLit_lift hL hr hx]
      exact ih hq hq' hx

/-! ## The interpretation -/

variable (L) in
/-- A literal fits an object of the category of value types. -/
def FitsOb : Ob → Lit → Prop
  | .value v, x => L.Fits v x
  | .entity _, _ => False

variable (L) in
/-- The conversion named `n` of a literal, the literal itself where it fails. -/
def convLitD (v : ValueType) (n : String) (x : Lit) : Lit :=
  match L.convLit v n x with
  | .ok y => y
  | .error _ => x

variable (L) in
/-- `convLitD` at an object. -/
def convOb : Ob → String → Lit → Lit
  | .value v, n, x => L.convLitD v n x
  | .entity _, _, x => x

variable (L) in
/-- A path of conversions of a literal, by `convLitD`. -/
def applyD : ValueType → List String → Lit → Lit
  | _, [], x => x
  | v, n :: ns, x => match L.conv? v n with
    | some w => applyD w ns (L.convLitD v n x)
    | none => x

variable (L) in
/-- `applyD` at an object. -/
def applyOb : Ob → List String → Lit → Lit
  | .value v, l, x => L.applyD v l x
  | .entity _, _, x => x

theorem convLitD_eq {v : ValueType} {n : String} {x y : Lit} (h : L.convLit v n x = .ok y) :
    L.convLitD v n x = y := by
  simp [convLitD, h]

theorem applyLit_eq (hL : L.Sound) : ∀ {l : List String} {v o : ValueType} {x : Lit},
    L.convTgt? v l = some o → L.Fits v x → L.applyLit v l x = .ok (L.applyD v l x)
  | [], _, _, _, _, _ => rfl
  | n :: ns, v, o, x, h, hx => by
    rw [convTgt?_cons] at h
    cases hc : L.conv? v n with
    | none => simp [hc] at h
    | some w =>
      rw [hc, Option.bind_some] at h
      obtain ⟨y, hy, hfy⟩ := convLit_fits hL hc hx
      rw [applyLit_cons hc, hy, bind_ok, applyLit_eq hL h hfy]
      simp [applyD, hc, convLitD_eq hy]

theorem applyD_snoc : ∀ {l : List String} {v u w : ValueType} {n : String} (x : Lit),
    L.convTgt? v l = some u → L.conv? u n = some w →
      L.applyD v (l ++ [n]) x = L.convLitD u n (L.applyD v l x)
  | [], v, u, w, n, x, h, hn => by
    rw [convTgt?_nil, Option.some.injEq] at h
    subst h
    simp [applyD, hn]
  | n' :: ns, v, u, w, n, x, h, hn => by
    rw [convTgt?_cons] at h
    cases hc : L.conv? v n' with
    | none => simp [hc] at h
    | some v' =>
      rw [hc, Option.bind_some] at h
      simp only [List.cons_append, applyD, hc]
      exact applyD_snoc _ h hn

theorem litPre_fits (hL : L.Sound) {ao bo : Ob} {n : String}
    (hn : emptySchema.vstep? L ao n = some bo) {x : Lit} (hx : L.FitsOb ao x) :
    L.FitsOb bo (L.convOb ao n x) := by
  cases ao with
  | entity e => exact absurd hx id
  | value v =>
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨y, hy, hfy⟩ := convLit_fits hL hw hx
    change L.Fits w (L.convLitD v n x)
    rw [convLitD_eq hy]
    exact hfy

variable (L) in
/-- Each conversion acts on the literals that fit its source. -/
def litPre (hL : L.Sound) : emptySchema.VObj L ⥤q Type where
  obj a := { x : Lit // L.FitsOb a.1 x }
  map {a _} f x := ⟨L.convOb a.1 f.1 x.1, litPre_fits hL f.2 x.2⟩

theorem litPath (hL : L.Sound) {a b : emptySchema.VObj L} (p : Quiver.Path a b)
    (x : { x : Lit // L.FitsOb a.1 x }) :
    ((Paths.lift (L.litPre hL)).map p x).1 = L.applyOb a.1 (Schema.vnames p) x.1 := by
  induction p with
  | nil =>
    obtain ⟨⟨e⟩ | ⟨v⟩, ha⟩ := a
    · exact absurd x.2 id
    · rfl
  | cons p e ih =>
    rename_i c d
    rw [Paths.lift_cons, types_comp_apply, Schema.vnames_cons]
    change L.convOb c.1 e.1 ((Paths.lift (L.litPre hL)).map p x).1 = _
    rw [ih]
    obtain ⟨⟨ea⟩ | ⟨v⟩, ha⟩ := a
    · exact absurd x.2 id
    · obtain ⟨⟨ec⟩ | ⟨u⟩, hc⟩ := c
      · obtain ⟨u, hu, -⟩ := Schema.value_of_vtgt? (Schema.vtgt?_vnames p)
        cases hu
      · obtain ⟨u', hu, hpu⟩ := Schema.value_of_vtgt? (Schema.vtgt?_vnames p)
        cases hu
        obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.mp e.2
        change L.convLitD u e.1 (L.applyD v (Schema.vnames p) x.1) =
          L.applyD v (Schema.vnames p ++ [e.1]) x.1
        rw [applyD_snoc _ hpu hw]

theorem litPre_resp (hL : L.Sound) : ∀ (a b : Paths (emptySchema.VObj L)) (f₁ f₂ : a ⟶ b),
    emptySchema.vrel L f₁ f₂ →
      (Paths.lift (L.litPre hL)).map f₁ = (Paths.lift (L.litPre hL)).map f₂ := by
  rintro ⟨ao, hao⟩ b f₁ f₂ (⟨q, hq, -⟩ | ⟨u, ha, h⟩)
  · simp [emptySchema] at hq
  · simp only at ha
    subst ha
    funext x
    apply Subtype.ext
    rw [litPath, litPath]
    have t₁ := Schema.vtgt?_vnames (S := emptySchema) (L := L) f₁
    have t₂ := Schema.vtgt?_vnames (S := emptySchema) (L := L) f₂
    obtain ⟨o, hb, h₁⟩ := Schema.value_of_vtgt? t₁
    obtain ⟨o', hb', h₂⟩ := Schema.value_of_vtgt? t₂
    rw [hb] at hb'
    cases hb'
    have hx : L.Fits u x.1 := x.2
    have e := applyLit_basic hL h h₁ h₂ hx
    rw [applyLit_eq hL h₁ hx, applyLit_eq hL h₂ hx] at e
    exact Except.ok.inj e

variable (L) in
/-- The literal interpretation: the values of a type are the literals that fit it, and each
conversion acts as `TypeList.convLit`. -/
def litInterp (hL : L.Sound) : Interp L where
  F := CategoryTheory.Quotient.lift (emptySchema.vrel L) (Paths.lift (L.litPre hL))
    (litPre_resp hL)

theorem litInterp_K (hL : L.Sound) (v : ValueType) :
    (L.litInterp hL).K v = { x : Lit // L.Fits v x } := rfl

/-- `applyLit` computes the literal interpretation on paths of conversions. -/
theorem applyLit_litInterp (hL : L.Sound) {v : ValueType} {b : emptySchema.VObj L}
    (p : Quiver.Path (Schema.vval emptySchema L v) b) (x : (L.litInterp hL).K v) :
    L.applyLit v (Schema.vnames p) x.1 =
      .ok (((L.litInterp hL).F.map (Schema.vmor p) x : { x : Lit // L.FitsOb b.1 x }).1) := by
  obtain ⟨o, -, ho⟩ := Schema.value_of_vtgt? (Schema.vtgt?_vnames p)
  rw [applyLit_eq hL ho x.2]
  change _ = Except.ok ((Paths.lift (L.litPre hL)).map p x).1
  rw [litPath]
  rfl

/-- `convLit` computes the literal interpretation on conversions. -/
theorem convLit_litInterp (hL : L.Sound) {v w : ValueType} {n : String} (h : L.conv? v n = some w)
    (x : (L.litInterp hL).K v) :
    L.convLit v n x.1 = .ok ((L.litInterp hL).F.map (L.convMor n h) x : { x // L.Fits w x }).1 := by
  have e := applyLit_litInterp hL (Quiver.Hom.toPath (show @Quiver.Hom (emptySchema.VObj L) _
    ⟨.value v, trivial⟩ ⟨.value w, trivial⟩ from ⟨n, by simp [Schema.vstep?, h]⟩)) x
  rw [Schema.vnames_toPath, applyLit_cons h] at e
  obtain ⟨y, hy, -⟩ := convLit_fits hL h x.2
  rw [hy] at e ⊢
  exact e

end TypeList

namespace Schema

open TypeList

variable {S : Schema} {L : TypeList}

/-- Equal paths of conversions take a literal that fits their source to the same literal. -/
theorem applyLit_eq_of_vPathEq (hL : L.Sound) {v : ValueType} {l l' : List String}
    (h : S.VPathEq L (vval S L v) l l') {x : Lit} (hx : L.Fits v x) :
    L.applyLit v l x = L.applyLit v l' x := by
  have h' : emptySchema.VPathEq L (vval emptySchema L v) l l' :=
    convEq_sound emptySchema_wellFormed (convEq_complete hL h)
  obtain ⟨b, p, q, rfl, rfl, hpq⟩ := h'
  rw [applyLit_litInterp hL p ⟨x, hx⟩, applyLit_litInterp hL q ⟨x, hx⟩, hpq]

end Schema

namespace TypeList

variable {L : TypeList}

/-! ## Literals in normal form fit their type -/

theorem pad_length (w n : Nat) : w ≤ (Norm.pad w n).length := by
  simp only [Norm.pad, String.length_append, String.length_ofList, List.length_replicate]
  omega

theorem stamp_length (y m d : Nat) (t : String) :
    10 < (Norm.dateText y m d ++ "T" ++ t ++ "Z").length := by
  have h₁ := pad_length 4 y
  have h₂ := pad_length 2 m
  have h₃ := pad_length 2 d
  have h₄ : ("-" : String).length = 1 := rfl
  have hT : ("T" : String).length = 1 := rfl
  have hZ : ("Z" : String).length = 1 := rfl
  simp only [Norm.dateText, String.length_append, h₄, hT, hZ]
  omega

/-- The normal form of a timestamp has more than ten characters. -/
theorem timestamp_length {s s' : String} (h : Norm.timestamp s = .ok s') : 10 < s'.length := by
  unfold Norm.timestamp at h
  repeat' (split at h)
  all_goals first | (simp at h; done) | skip
  simp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    exact stamp_length _ _ _ _
  · simp [bind, Except.bind] at h

theorem map_text_ok {e : Except String String} {y : Lit} (h : (Lit.text <$> e) = .ok y) :
    ∃ s, e = .ok s ∧ y = .text s := by
  cases e with
  | error _ => cases h
  | ok s => exact ⟨s, rfl, (Except.ok.inj h).symm⟩

theorem fitsBuiltin_of_normalizeBuiltin {b : ValueType} {x y : Lit}
    (h : normalizeBuiltin b x = .ok y) : FitsBuiltin b y := by
  unfold normalizeBuiltin at h
  split at h <;> first
    | (obtain rfl := Except.ok.inj h; exact ⟨_, rfl⟩)
    | (obtain ⟨s, hs, rfl⟩ := map_text_ok h; exact ⟨s, rfl⟩)
    | (obtain ⟨s, hs, rfl⟩ := map_text_ok h; exact ⟨s, rfl, timestamp_length hs⟩)
    | cases h

theorem fitsFlat_of_normalizeFlat (hL : L.Sound) : ∀ {t : ValueType} {x y : Lit},
    L.normalizeFlat t x = .ok y → L.FitsFlat t y
  | .named n, x, y, h => by
    simp only [normalizeFlat] at h
    simp only [FitsFlat]
    split at h
    · cases h
    · rename_i vs hvs
      rw [hvs]
      split at h
      · split at h
        · obtain rfl := Except.ok.inj h
          exact ⟨_, rfl, by assumption⟩
        · cases h
      · cases h
      · cases h
    · rename_i b hb
      rw [hb]
      split at h
      · exact fitsBuiltin_of_normalizeBuiltin h
      · cases h
    · cases h
  | .optional (.optional _), _, _, h => by cases h
  | .optional (.named n), x, y, h => by
    by_cases hx : x = .null
    · subst hx
      exact .inl (Except.ok.inj h).symm
    · have h' : L.normalizeFlat (.named n) x = .ok y := by
        cases x <;> first | exact absurd rfl hx | exact h
      exact .inr (fitsFlat_of_normalizeFlat hL h')
  | .optional .int, x, y, h | .optional .decimal, x, y, h
  | .optional .string, x, y, h
  | .optional .date, x, y, h | .optional .uuid, x, y, h | .optional .bool, x, y, h
  | .optional .datetime, x, y, h | .optional .timestamp, x, y, h | .optional .time, x, y, h
  | .optional .duration, x, y, h => by
    by_cases hx : x = .null
    · subst hx
      exact .inl (Except.ok.inj h).symm
    · right
      apply fitsBuiltin_of_normalizeBuiltin (x := x)
      cases x <;> first | exact absurd rfl hx | exact h
  | .int, _, _, h | .decimal, _, _, h | .string, _, _, h | .date, _, _, h | .uuid, _, _, h
  | .bool, _, _, h | .datetime, _, _, h | .timestamp, _, _, h | .time, _, _, h
  | .duration, _, _, h => fitsBuiltin_of_normalizeBuiltin h

theorem lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => by simp at h
  | (k', v') :: l, k, v, hn, h => by
    rw [List.lookup_cons]
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with e | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      simp
    · have hk : k ≠ k' := fun e => hn.1 (e ▸ List.mem_map.mpr ⟨(k, v), h, rfl⟩)
      have : (k == k') = false := by simpa using hk
      rw [this]
      exact lookup_of_mem_nodup hn.2 h

theorem mapM_field {n : String} {xs : List (String × Lit)} (hL : L.Sound) :
    ∀ {fs : List (String × ValueType)} {out : List (String × Lit)},
      fs.mapM (L.normalizeField n xs) = .ok out →
        out.map Prod.fst = fs.map Prod.fst ∧ ∀ f ∈ fs, ∃ z, (f.1, z) ∈ out ∧ L.FitsFlat f.2 z
  | [], out, h => by
    simp only [List.mapM_nil] at h
    obtain rfl := (Except.ok.inj h).symm
    simp
  | (f, t) :: fs, out, h => by
    rw [List.mapM_cons] at h
    cases hf : L.normalizeField n xs (f, t) with
    | error _ => simp [hf, bind, Except.bind] at h
    | ok b =>
      cases hm : fs.mapM (L.normalizeField n xs) with
      | error _ => simp [hf, hm, bind, Except.bind] at h
      | ok bs =>
        simp only [hf, hm, bind, Except.bind, pure, Except.pure] at h
        obtain rfl := (Except.ok.inj h).symm
        obtain ⟨ih₁, ih₂⟩ := mapM_field hL hm
        simp only [normalizeField] at hf
        split at hf
        · split at hf
          · rename_i l hl z hz
            obtain rfl := (Except.ok.inj hf).symm
            refine ⟨by simp [ih₁], ?_⟩
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg
            · exact ⟨z, List.mem_cons_self, fitsFlat_of_normalizeFlat hL hz⟩
            · obtain ⟨z', hz', hfz'⟩ := ih₂ g hg
              exact ⟨z', List.mem_cons_of_mem _ hz', hfz'⟩
          · cases hf
        · cases hf

theorem normalizeFields_fits (hL : L.Sound) {n : String} {fs : List (String × ValueType)}
    (hnd : (fs.map Prod.fst).Nodup) {xs : List (String × Lit)} {y : Lit}
    (h : L.normalizeFields n fs xs = .ok y) :
    ∃ ys, y = .record ys ∧ ∀ f ∈ fs, ∃ z, ys.lookup f.1 = some z ∧ L.FitsFlat f.2 z := by
  unfold normalizeFields at h
  repeat' (split at h)
  all_goals (simp only at h)
  all_goals first | (simp [bind, Except.bind, pure, Except.pure] at h; done) | skip
  cases hm : fs.mapM (L.normalizeField n xs) with
  | error _ => simp [hm, bind, Except.bind, pure, Except.pure] at h
  | ok out =>
    simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hk, hf⟩ := mapM_field hL hm
    have hp := List.mergeSort_perm out fun a b => compare a.1 b.1 != .gt
    have hnd' : ((out.mergeSort fun a b => compare a.1 b.1 != .gt).map Prod.fst).Nodup :=
      (hp.map Prod.fst).nodup_iff.mpr (hk ▸ hnd)
    refine ⟨_, rfl, fun f hf' => ?_⟩
    obtain ⟨z, hz, hfz⟩ := hf f hf'
    exact ⟨z, lookup_of_mem_nodup hnd' (hp.mem_iff.mpr hz), hfz⟩

/-- A literal in normal form fits its type. -/
theorem fits_of_normalize (hL : L.Sound) : ∀ {v : ValueType} {x y : Lit},
    L.normalize v x = .ok y → L.Fits v y
  | .named n, x, y, h => by
    simp only [normalize] at h
    simp only [Fits]
    split at h
    · rename_i fs hfs
      rw [hfs]
      split at h
      · obtain ⟨-, hnd, -⟩ := hL.decl _ (mem_of_lookup hfs)
        exact normalizeFields_fits hL hnd h
      · cases h
      · cases h
    · rename_i hnr
      split
      · rename_i fs hfs
        exact absurd hfs (hnr fs)
      · exact fitsFlat_of_normalizeFlat hL h
  | .optional (.optional _), _, _, h => by cases h
  | .optional (.named n), x, y, h => by
    by_cases hx : x = .null
    · subst hx
      exact .inl (Except.ok.inj h).symm
    · have h' : L.normalize (.named n) x = .ok y := by
        cases x <;> first | exact absurd rfl hx | exact h
      exact .inr (fits_of_normalize hL h')
  | .optional .int, x, y, h | .optional .decimal, x, y, h | .optional .string, x, y, h
  | .optional .date, x, y, h | .optional .uuid, x, y, h | .optional .bool, x, y, h
  | .optional .datetime, x, y, h | .optional .timestamp, x, y, h | .optional .time, x, y, h
  | .optional .duration, x, y, h => by
    by_cases hx : x = .null
    · subst hx
      exact .inl (Except.ok.inj h).symm
    · right
      apply fitsBuiltin_of_normalizeBuiltin (x := x)
      cases x <;> first | exact absurd rfl hx | exact h
  | .int, _, _, h | .decimal, _, _, h | .string, _, _, h | .date, _, _, h | .uuid, _, _, h
  | .bool, _, _, h | .datetime, _, _, h | .timestamp, _, _, h | .time, _, _, h
  | .duration, _, _, h => fitsBuiltin_of_normalizeBuiltin h

/-- The result of a claim `conversion` is the image of its literal, in normal form, in the
literal interpretation. -/
theorem applyLit_normal (hL : L.Sound) {v : ValueType} {b : emptySchema.VObj L}
    (p : Quiver.Path (Schema.vval emptySchema L v) b) {x y : Lit}
    (hx : L.normalize v x = .ok x) (hy : L.applyLit v (Schema.vnames p) x = .ok y) :
    y = ((L.litInterp hL).F.map (Schema.vmor p) ⟨x, fits_of_normalize hL hx⟩ :
      { x : Lit // L.FitsOb b.1 x }).1 := by
  rw [applyLit_litInterp hL p ⟨x, fits_of_normalize hL hx⟩] at hy
  exact (Except.ok.inj hy).symm

end TypeList

end DDD
