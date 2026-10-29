import DDD.ContextMap
import DDD.Union

/-!
# Merging a component of a context map

Strict integration along several kernels. A component of a context map
(`ContextMap.Component`) is a list of contexts, its members, closed under the
arrows out of them: every arrow out of a member is an arrow out of a kernel into
a member, and every kernel with an arrow into a member is a member. The glued
schema of the component is the union of the schemas of its members
(`Schema.glueAll`), in the order of the list.

- The condition (`checkComponent`, decided by `decide`): the members share
  entity types, generators and value types only through kernels. Along the list,
  each member that shares an entity type or a generator with earlier members
  shares it with one of them through a kernel that has it and includes into both,
  and each member after the first shares the value types with an earlier one
  through a kernel. Kernels include into members along `links`, a list of the
  arrows out of kernels; a member includes into itself.
- `Component.isColimit`: the glued schema category is the colimit of `D`
  restricted to the members and the arrows between them, which are inclusions
  out of kernels. For one kernel with two arrows the diagram is a span, and the
  colimit is the pushout of `isPushout_kernel`.
- `Component.map`: the context map after the merge, on `Merged`: the component is
  one context with the glued schema, and every arrow into a member becomes an
  arrow into it, its translation composed with the inclusion of the member
  (`Translation.comp`; `diagram_into`). No arrow leaves the component
  (`Component.closed`), so no arrow leaves the glued context.
- Non-interference: lax non-interference for the merged map when the map has a
  rank (`Component.nonInterference`), and strict non-interference for each leg
  from `checkFullyFaithful` (`Component.leg_fullyFaithful`).
-/

namespace DDD

open CategoryTheory

variable {C : Type} [Quiver.{1} C]

/-- The contexts of a list, with the arrows between them. -/
def Members (ms : List C) : Type := { c : C // c ∈ ms }

instance (ms : List C) : Quiver (Members ms) := ⟨fun a b => a.1 ⟶ b.1⟩

/-- The contexts after merging the contexts of `ms` into one: the glued context,
and the contexts outside `ms`. -/
inductive Merged (ms : List C) where
  | glued
  | other (c : C) (h : c ∉ ms)

/-- The arrows after the merge: the arrows between contexts outside `ms`, and the
arrows into contexts of `ms`, each into the glued context. -/
def Merged.Hom {ms : List C} : Merged ms → Merged ms → Type
  | .other u _, .other d _ => u ⟶ d
  | .other u _, .glued => Σ d : Members ms, u ⟶ d.1
  | .glued, _ => PEmpty

instance (ms : List C) : Quiver (Merged ms) := ⟨Merged.Hom⟩

/-- A rank of the contexts after the merge: the rank of the contexts outside
`ms`, and the largest rank of the contexts of `ms` for the glued one. -/
def Merged.rank (ms : List C) (rank : C → ℕ) : Merged ms → ℕ
  | .glued => (ms.map rank).foldr max 0
  | .other c _ => rank c

omit [Quiver C] in
theorem le_foldr_max {rank : C → ℕ} : ∀ {ms : List C} {c : C}, c ∈ ms →
    rank c ≤ (ms.map rank).foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | d :: ms, c, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max h) (le_max_right _ _)

/-- A rank that increases along the arrows increases along the arrows after the
merge. -/
theorem Merged.rank_lt {ms : List C} {rank : C → ℕ}
    (hrank : ∀ {a b : C}, (a ⟶ b) → rank a < rank b) :
    ∀ {a b : Merged ms}, (a ⟶ b) → Merged.rank ms rank a < Merged.rank ms rank b
  | .other _ _, .other _ _, f => hrank f
  | .other _ _, .glued, f => lt_of_lt_of_le (hrank f.2) (le_foldr_max f.1.2)
  | .glued, _, f => PEmpty.elim f

namespace ContextMap

variable (M : ContextMap C)

/-- The routes between the contexts of `ms`, in the category of contexts. -/
def membersIncl (ms : List C) : Paths (Members ms) ⥤ M.J :=
  Paths.lift { obj := fun a => M.ctx a.1, map := fun f => M.arrow f }

/-- `D` restricted to the contexts of `ms` and the arrows between them. -/
def membersDiagram (ms : List C) : Paths (Members ms) ⥤ Cat.{0, 0} :=
  M.membersIncl ms ⋙ M.diagram

theorem membersDiagram_map {ms : List C} {a b : Members ms} (f : a ⟶ b) :
    (M.membersDiagram ms).map f.toPath =
      (M.translation f).functor (M.wellFormed _) (M.valid f) := by
  simp only [membersDiagram, membersIncl, Functor.comp_map, Paths.lift_toPath]
  exact M.diagram_map_arrow f

/-! ## The condition -/

variable [DecidableEq C]

/-- `k` includes into `c` along `links`: `k = c`, or a link runs from `k` to
`c`. -/
def reach (links : List (Σ k d : C, k ⟶ d)) (k c : C) : Bool :=
  decide (k = c) || links.any fun l => decide (l.1 = k) && decide (l.2.1 = c)

/-- `c` and `c'` share what the property `has` describes through a context of
`ms` that has it and includes into both. -/
def adjacent (ms : List C) (links : List (Σ k d : C, k ⟶ d)) (has : C → Bool) (c c' : C) :
    Bool :=
  ms.any fun k => has k && reach links k c && reach links k c'

/-- The check for a component: links run between members; along `ms`, every
entity type and every generator spans through kernels that have it, and the value
types span through kernels. -/
def checkComponent (ms : List C) (links : List (Σ k d : C, k ⟶ d)) : Bool :=
  links.all (fun l => decide (l.1 ∈ ms) && decide (l.2.1 ∈ ms)) &&
  ((ms.flatMap fun c => (M.schema c).entities).all fun e =>
    checkSpanning (fun c => decide (e ∈ (M.schema c).entities))
      (adjacent ms links fun c => decide (e ∈ (M.schema c).entities)) [] ms) &&
  ((ms.flatMap fun c => (M.schema c).gens).all fun g =>
    checkSpanning (fun c => decide (g ∈ (M.schema c).gens))
      (adjacent ms links fun c => decide (g ∈ (M.schema c).gens)) [] ms) &&
  checkSpanning (fun _ => true) (adjacent ms links fun _ => true) [] ms

/-- A component of a context map: its members, in an order along which the check
passes, the arrows out of kernels that witness it, and the conditions. -/
structure Component where
  members : List C
  links : List (Σ k d : C, k ⟶ d)
  nonempty : members ≠ []
  /-- Every arrow out of a member is an arrow out of a kernel into a member. -/
  closed : ∀ {u d : C} (_ : u ⟶ d), u ∈ members → d ∈ members ∧ M.kernel u = true
  /-- Every kernel with an arrow into a member is a member. -/
  kernels : ∀ {u d : C} (_ : u ⟶ d), d ∈ members → M.kernel u = true → u ∈ members
  check : M.checkComponent members links = true
  wf_glued : (Schema.glueAll (members.map M.schema)).WellFormed

namespace Component

variable {M} (P : M.Component)

/-- The glued schema of the component. -/
abbrev glued : Schema := Schema.glueAll (P.members.map M.schema)

theorem check_links : ∀ l ∈ P.links, l.1 ∈ P.members ∧ l.2.1 ∈ P.members := by
  have h := P.check
  simp only [checkComponent, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem check_entities : ∀ e ∈ P.members.flatMap (fun c => (M.schema c).entities),
    checkSpanning (fun c => decide (e ∈ (M.schema c).entities))
      (adjacent P.members P.links fun c => decide (e ∈ (M.schema c).entities)) [] P.members =
        true := by
  have h := P.check
  simp only [checkComponent, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.2

theorem check_gens : ∀ g ∈ P.members.flatMap (fun c => (M.schema c).gens),
    checkSpanning (fun c => decide (g ∈ (M.schema c).gens))
      (adjacent P.members P.links fun c => decide (g ∈ (M.schema c).gens)) [] P.members =
        true := by
  have h := P.check
  simp only [checkComponent, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2

theorem check_values :
    checkSpanning (fun _ => true) (adjacent P.members P.links fun _ => true) [] P.members =
      true := by
  have h := P.check
  simp only [checkComponent, Bool.and_eq_true] at h
  exact h.2

/-- A context that reaches another along the links includes into it. -/
theorem valid_of_reach {k c : C} (h : reach P.links k c = true) :
    ({} : Translation).Valid (M.schema k) (M.schema c) := by
  simp only [reach, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true] at h
  rcases h with rfl | ⟨⟨k', d', f⟩, hl, e₁, e₂⟩
  · exact Translation.empty_valid_self (M.wellFormed k)
  · subst e₁ e₂
    have hm := P.check_links _ hl
    exact M.valid_empty f (P.closed f hm.1).2

/-- Unpacks `adjacent`. -/
theorem adjacent_spec {has : C → Bool} {c c' : C}
    (h : adjacent P.members P.links has c c' = true) :
    ∃ k ∈ P.members, has k = true ∧ reach P.links k c = true ∧ reach P.links k c' = true := by
  simp only [adjacent, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨k, hk, ⟨h₁, h₂⟩, h₃⟩ := h
  exact ⟨k, hk, h₁, h₂, h₃⟩

/-- Members give each shared generator the same target. -/
theorem step_agree : ∀ i ∈ P.members, ∀ j ∈ P.members, ∀ (o : Ob) (n : String) (y y' : Ob),
    (M.schema i).step? o n = some y → (M.schema j).step? o n = some y' → y = y' := by
  intro i hi j hj o n y y' h h'
  obtain ⟨e, rfl, -⟩ := Schema.exists_gen_of_step? h
  have hgi : (e, n) ∈ (M.schema i).gens := Schema.step?_isSome_iff.mp (by simp [h])
  have hgj : (e, n) ∈ (M.schema j).gens := Schema.step?_isSome_iff.mp (by simp [h'])
  have hsp := P.check_gens (e, n) (List.mem_flatMap.mpr ⟨i, hi, hgi⟩)
  have hR := pairwise_of_checkSpanning
    (fun c c' => (M.schema c).step? (.entity e) n = (M.schema c').step? (.entity e) n)
    P.members (fun _ _ _ => rfl) (fun _ _ _ _ _ _ h => h.symm)
    (fun _ _ _ _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun c _ c' _ _ _ ha => by
      obtain ⟨k, -, hk, r₁, r₂⟩ := P.adjacent_spec ha
      have hks := Schema.step?_isSome_iff.mpr (of_decide_eq_true hk)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hks
      rw [Schema.step?_of_sub (P.valid_of_reach r₁) hx,
        Schema.step?_of_sub (P.valid_of_reach r₂) hx])
    [] P.members (List.nil_subset _) (List.Subset.refl _) (by simp) hsp
    i hi j hj (decide_eq_true hgi) (decide_eq_true hgj)
  exact Option.some.inj (h.symm.trans (hR.trans h'))

/-- The members cover the glued schema. -/
theorem cover : Schema.Cover P.glued (fun a : Members P.members => M.schema a.1) :=
  Schema.Cover.glueAll P.members M.schema P.nonempty P.wf_glued (fun c _ => M.wellFormed c)
    P.step_agree

/-- Each member includes into the glued schema. -/
theorem sub (a : Members P.members) : ({} : Translation).Valid (M.schema a.1) P.glued :=
  P.cover.sub a

/-- The inclusion of a member into the glued schema category. -/
def leg (a : Members P.members) : (M.schema a.1).cat ⥤ P.glued.cat := P.cover.leg a

/-- Along an arrow between members, the legs commute: the arrow is an inclusion
out of a kernel. -/
theorem leg_arrow {a b : Members P.members} (f : a ⟶ b) :
    (M.membersDiagram P.members).map f.toPath ⋙ P.leg b = P.leg a := by
  have hk := (P.closed f a.2).2
  rw [membersDiagram_map, Translation.functor_congr _ _ (M.valid_empty f hk) (M.inclusion f hk)]
  exact Translation.functor_empty_comp_empty _ _ _ _ _

/-! ## The colimit -/

/-- Along a route between members, the legs commute. -/
theorem leg_path {a : Members P.members} : ∀ {b : Members P.members} (p : Quiver.Path a b),
    (M.membersDiagram P.members).map p ≫ P.leg b = P.leg a
  | _, .nil => ((congrArg (· ≫ P.leg a) ((M.membersDiagram P.members).map_id a)).trans
      (Category.id_comp _))
  | _, .cons (b := b) p f => by
    have hc : (M.membersDiagram P.members).map (p.cons f) =
        (M.membersDiagram P.members).map p ≫ (M.membersDiagram P.members).map f.toPath := by
      simp only [membersDiagram, Functor.comp_map, membersIncl, Paths.lift_cons,
        Paths.lift_toPath, CategoryTheory.Functor.map_comp]
    rw [hc, Category.assoc,
      show (M.membersDiagram P.members).map f.toPath ≫ P.leg _ = P.leg b from P.leg_arrow f]
    exact leg_path p

/-- The glued schema category with the legs, as a cocone over `D` restricted to
the members. -/
def cocone : Limits.Cocone (M.membersDiagram P.members) where
  pt := P.glued.cat
  ι :=
    { app := fun a => P.leg a
      naturality := by
        intro a b φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact P.leg_path φ }

section Agree

variable {X : Type*} [Category X] {F : ∀ a : Members P.members, (M.schema a.1).cat ⥤ X}
  (hF : ∀ {a b : Members P.members} (f : a ⟶ b),
    (M.membersDiagram P.members).map f.toPath ⋙ F b = F a)

include hF in
/-- Along a link, the functors are related by the inclusion. -/
theorem compat_link {k c : C} (hk : k ∈ P.members) (hc : c ∈ P.members) (f : k ⟶ c) :
    Translation.functor (M.wellFormed c) (M.valid_empty f (P.closed f hk).2) ⋙ F ⟨c, hc⟩ =
      F ⟨k, hk⟩ := by
  have h := hF (a := ⟨k, hk⟩) (b := ⟨c, hc⟩) f
  rwa [membersDiagram_map, Translation.functor_congr _ _ (M.valid_empty f (P.closed f hk).2)
    (M.inclusion f (P.closed f hk).2)] at h

include hF in
/-- Where `k` reaches `c`, the functor of `c` agrees with the functor of `k` on an
object of `k`. -/
theorem obj_reach {k c : C} (hk : k ∈ P.members) (hc : c ∈ P.members)
    (h : reach P.links k c = true) (o : Ob) (hok : (M.schema k).IsOb o)
    (hoc : (M.schema c).IsOb o) :
    (F ⟨c, hc⟩).obj ((M.schema c).obj ⟨o, hoc⟩) = (F ⟨k, hk⟩).obj ((M.schema k).obj ⟨o, hok⟩) := by
  simp only [reach, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true] at h
  rcases h with rfl | ⟨⟨k', d', f⟩, -, e₁, e₂⟩
  · rfl
  · subst e₁ e₂
    have h := Functor.congr_obj (P.compat_link hF hk hc f) ((M.schema k').obj ⟨o, hok⟩)
    rw [← h, Functor.comp_obj, Translation.functor_obj, Translation.obj_empty]

include hF in
/-- Where `k` reaches `c`, the functor of `c` agrees with the functor of `k` on a
generator of `k`. -/
theorem gen_reach {k c : C} (hk : k ∈ P.members) (hc : c ∈ P.members)
    (h : reach P.links k c = true) (a b : Ob) (n : String) (hak : (M.schema k).IsOb a)
    (hbk : (M.schema k).IsOb b) (hac : (M.schema c).IsOb a) (hbc : (M.schema c).IsOb b)
    (hsk : (M.schema k).step? a n = some b) (hsc : (M.schema c).step? a n = some b) :
    Arrow.mk ((F ⟨c, hc⟩).map ((M.schema c).genMor (a := ⟨a, hac⟩) (b := ⟨b, hbc⟩) n hsc)) =
      Arrow.mk ((F ⟨k, hk⟩).map ((M.schema k).genMor (a := ⟨a, hak⟩) (b := ⟨b, hbk⟩) n hsk)) := by
  simp only [reach, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true] at h
  rcases h with rfl | ⟨⟨k', d', f⟩, -, e₁, e₂⟩
  · rfl
  · subst e₁ e₂
    rw [← P.compat_link hF hk hc f, Functor.comp_map,
      Translation.functor_empty_genMor _ _ n hsk hac hbc hsc]
    simp [eqToHom_map]

include hF in
/-- Functors out of the members that commute with the arrows between members agree
where the members overlap. -/
theorem agree : Schema.Agree (fun a : Members P.members => M.schema a.1) F where
  ob := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ o hoi hoj
    -- The relation: agreement on `o` of the functors of two members that have it.
    let R : C → C → Prop := fun c c' => ∀ (hc : c ∈ P.members) (hc' : c' ∈ P.members)
      (h : (M.schema c).IsOb o) (h' : (M.schema c').IsOb o),
      (F ⟨c, hc⟩).obj ((M.schema c).obj ⟨o, h⟩) = (F ⟨c', hc'⟩).obj ((M.schema c').obj ⟨o, h'⟩)
    have hrefl : ∀ c, R c c := fun _ _ _ _ _ => rfl
    have hsymm : ∀ c c', R c c' → R c' c := fun c c' h hc' hc h' h₁ => (h hc hc' h₁ h').symm
    cases o with
    | entity e =>
      let has : C → Bool := fun c => decide (e ∈ (M.schema c).entities)
      have hR := pairwise_of_checkSpanning (has := has)
        (adj := adjacent P.members P.links has) R P.members
        (fun c _ _ => hrefl c) (fun c _ c' _ _ _ => hsymm c c')
        (fun c _ c' hc' c'' _ _ h₂ _ h₁ h₂' hc hc'' hh hh'' =>
          (h₁ hc hc' hh (of_decide_eq_true h₂)).trans (h₂' hc' hc'' (of_decide_eq_true h₂) hh''))
        (fun c _ c' _ _ _ ha hc hc' hh hh' => by
          obtain ⟨k, hk, hkk, r₁, r₂⟩ := P.adjacent_spec ha
          have hok : (M.schema k).IsOb (.entity e) := of_decide_eq_true hkk
          exact (P.obj_reach hF hk hc r₁ (.entity e) hok hh).trans
            (P.obj_reach hF hk hc' r₂ (.entity e) hok hh').symm)
        [] P.members (List.nil_subset _) (List.Subset.refl _) (by simp)
        (P.check_entities e (List.mem_flatMap.mpr ⟨i, hi, hoi⟩))
      exact hR i hi j hj (decide_eq_true hoi) (decide_eq_true hoj) hi hj hoi hoj
    | value v =>
      have hR := pairwise_of_checkSpanning (has := fun _ => true)
        (adj := adjacent P.members P.links fun _ => true) R P.members
        (fun c _ _ => hrefl c) (fun c _ c' _ _ _ => hsymm c c')
        (fun c _ c' hc' c'' _ _ _ _ h₁ h₂' hc hc'' hh hh'' =>
          (h₁ hc hc' hh trivial).trans (h₂' hc' hc'' trivial hh''))
        (fun c _ c' _ _ _ ha hc hc' hh hh' => by
          obtain ⟨k, hk, -, r₁, r₂⟩ := P.adjacent_spec ha
          exact (P.obj_reach hF hk hc r₁ (.value v) trivial hh).trans
            (P.obj_reach hF hk hc' r₂ (.value v) trivial hh').symm)
        [] P.members (List.nil_subset _) (List.Subset.refl _) (by simp) P.check_values
      exact hR i hi j hj rfl rfl hi hj hoi hoj
  gen := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ a b n hai hbi haj hbj hsi hsj
    obtain ⟨e, rfl, -⟩ := Schema.exists_gen_of_step? hsi
    have hgi : (e, n) ∈ (M.schema i).gens := Schema.step?_isSome_iff.mp (by simp [hsi])
    have hgj : (e, n) ∈ (M.schema j).gens := Schema.step?_isSome_iff.mp (by simp [hsj])
    let has : C → Bool := fun c => decide ((e, n) ∈ (M.schema c).gens)
    -- A member with the generator gives it the target `b`.
    have htgt : ∀ c ∈ P.members, has c = true → (M.schema c).step? (.entity e) n = some b := by
      intro c hc hh
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
        (Schema.step?_isSome_iff.mpr (of_decide_eq_true hh))
      rw [hx, P.step_agree c hc i hi _ n x b hx hsi]
    let R : C → C → Prop := fun c c' => ∀ (hc : c ∈ P.members) (hc' : c' ∈ P.members)
      (hac : (M.schema c).IsOb (.entity e)) (hbc : (M.schema c).IsOb b)
      (hac' : (M.schema c').IsOb (.entity e)) (hbc' : (M.schema c').IsOb b)
      (hs : (M.schema c).step? (.entity e) n = some b)
      (hs' : (M.schema c').step? (.entity e) n = some b),
      Arrow.mk ((F ⟨c, hc⟩).map ((M.schema c).genMor (a := ⟨_, hac⟩) (b := ⟨b, hbc⟩) n hs)) =
        Arrow.mk ((F ⟨c', hc'⟩).map ((M.schema c').genMor (a := ⟨_, hac'⟩) (b := ⟨b, hbc'⟩) n hs'))
    have hR := pairwise_of_checkSpanning (has := has)
      (adj := adjacent P.members P.links has) R P.members
      (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ h hc' hc hac' hbc' hac hbc hs' hs =>
        (h hc hc' hac hbc hac' hbc' hs hs').symm)
      (fun c _ c' hc'm c'' _ _ h₂ _ h₁ h₂' hc hc'' hac hbc hac'' hbc'' hs hs'' => by
        have hs' := htgt c' hc'm h₂
        have wf := M.wellFormed c'
        exact (h₁ hc hc'm hac hbc (Schema.isOb_src_of_step? wf hs') (Schema.isOb_of_step? wf hs')
          hs hs').trans (h₂' hc'm hc'' _ _ hac'' hbc'' hs' hs''))
      (fun c _ c' _ _ _ ha hc hc' hac hbc hac' hbc' hs hs' => by
        obtain ⟨k, hk, hkk, r₁, r₂⟩ := P.adjacent_spec ha
        have hsk := htgt k hk hkk
        have wf := M.wellFormed k
        have hak := Schema.isOb_src_of_step? wf hsk
        have hbk := Schema.isOb_of_step? wf hsk
        exact (P.gen_reach hF hk hc r₁ _ _ n hak hbk hac hbc hsk hs).trans
          (P.gen_reach hF hk hc' r₂ _ _ n hak hbk hac' hbc' hsk hs').symm)
      [] P.members (List.nil_subset _) (List.Subset.refl _) (by simp)
      (P.check_gens (e, n) (List.mem_flatMap.mpr ⟨i, hi, hgi⟩))
    exact hR i hi j hj (decide_eq_true hgi) (decide_eq_true hgj) hi hj hai hbi haj hbj hsi hsj

end Agree

/-- The legs of a cocone over `D` restricted to the members. -/
def coconeLegs (s : Limits.Cocone (M.membersDiagram P.members)) :
    ∀ a : Members P.members, (M.schema a.1).cat ⥤ s.pt := fun a => s.ι.app a

/-- The legs of a cocone over `D` restricted to the members agree where the
members overlap. -/
theorem agree_cocone (s : Limits.Cocone (M.membersDiagram P.members)) :
    Schema.Agree (fun a : Members P.members => M.schema a.1) (P.coconeLegs s) :=
  P.agree fun f => s.w f.toPath

/-- Strict integration along the kernels of a component: the glued schema
category is the colimit of `D` restricted to the members and the arrows between
them. -/
noncomputable def isColimit : Limits.IsColimit P.cocone where
  desc s := P.cover.desc (P.agree_cocone s)
  fac _ a := P.cover.leg_desc _ a
  uniq _ m hm := P.cover.desc_unique _ m hm

/-- Strict non-interference for a leg, from the check. -/
theorem leg_fullyFaithful (a : Members P.members) (hA : (M.schema a.1).Acyclic)
    (hA' : P.glued.Acyclic)
    (h : ({} : Translation).checkFullyFaithful (M.schema a.1) P.glued = true) :
    (P.leg a).Full ∧ (P.leg a).Faithful :=
  Translation.checkFullyFaithful_sound (M.wellFormed _) P.wf_glued hA hA' (P.sub a) h

/-! ## The merged map -/

/-- The schema of each context after the merge. -/
def mergedSchema : Merged P.members → Schema
  | .glued => P.glued
  | .other c _ => M.schema c

theorem mergedWellFormed : ∀ c, (P.mergedSchema c).WellFormed
  | .glued => P.wf_glued
  | .other c _ => M.wellFormed c

/-- The translation along each arrow after the merge: the translation of the arrow,
composed with the inclusion of the member for an arrow into the glued context. -/
def mergedTranslation : ∀ {u d : Merged P.members}, (u ⟶ d) → Translation
  | .other _ _, .other _ _, f => M.translation f
  | .other u _, .glued, f => (M.translation f.2).comp (M.schema u) (M.schema f.1.1) {}
  | .glued, _, f => PEmpty.elim f

theorem mergedValid : ∀ {u d : Merged P.members} (f : u ⟶ d),
    (P.mergedTranslation f).Valid (P.mergedSchema u) (P.mergedSchema d)
  | .other _ _, .other _ _, f => M.valid f
  | .other u _, .glued, f =>
    Translation.comp_valid (M.wellFormed u) P.wf_glued (M.valid f.2) (P.sub f.1)
  | .glued, _, f => PEmpty.elim f

/-- The kernels after the merge: the kernels outside the component. -/
def mergedKernel : Merged P.members → Bool
  | .glued => false
  | .other c _ => M.kernel c

theorem mergedInclusion : ∀ {u d : Merged P.members} (f : u ⟶ d),
    P.mergedKernel u = true → P.mergedTranslation f = {}
  | .other _ _, .other _ _, f, h => M.inclusion f h
  | .other _ hu, .glued, f, h => absurd (P.kernels f.2 f.1.2 h) hu
  | .glued, _, _, h => Bool.noConfusion h

/-- The context map after the merge. It declares no equation between routes. -/
def map : ContextMap (Merged P.members) where
  schema := P.mergedSchema
  translation := P.mergedTranslation
  wellFormed := P.mergedWellFormed
  valid := P.mergedValid
  kernel := P.mergedKernel
  inclusion := P.mergedInclusion

/-- An arrow into a member goes to the glued context, with the functor of the
arrow followed by the leg of the member. -/
theorem diagram_into {u : C} (hu : u ∉ P.members) (d : Members P.members) (f : u ⟶ d.1) :
    P.map.diagram.map (P.map.arrow (u := .other u hu) (d := .glued) ⟨d, f⟩) =
      M.diagram.map (M.arrow f) ⋙ P.leg d := by
  rw [diagram_map_arrow, diagram_map_arrow]
  exact Translation.functor_comp (M.wellFormed u) (M.wellFormed d.1) P.wf_glued (M.valid f)
    (P.sub d)

/-- An arrow between contexts outside the component is unchanged. -/
theorem diagram_other {u d : C} (hu : u ∉ P.members) (hd : d ∉ P.members) (f : u ⟶ d) :
    P.map.diagram.map (P.map.arrow (u := .other u hu) (d := .other d hd) f) =
      M.diagram.map (M.arrow f) := by
  rw [diagram_map_arrow, diagram_map_arrow]

/-- Lax non-interference after the merge, for a map with a rank that increases
along its arrows. -/
theorem nonInterference (rank : C → ℕ) (hrank : ∀ {a b : C}, (a ⟶ b) → rank a < rank b)
    (c : Merged P.members) :
    (P.map.embed c).Full ∧ (P.map.embed c).Faithful ∧ Function.Injective (P.map.embed c).obj :=
  P.map.nonInterference
    (P.map.endo_eq_id (endo_eq_id_of_rank (Merged.rank P.members rank) (Merged.rank_lt hrank))) c

end Component

end ContextMap

end DDD
