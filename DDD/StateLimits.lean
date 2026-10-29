import DDD.States
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Limits and colimits of attributed states

The attributed states `Schema.State K S` have all small limits and colimits, with
the values fixed: at a value type `v`, a limit or a colimit has `K v` again. They
are not the pointwise limits and colimits of functors: the pointwise product of
two states has `K v × K v` at `v`, the pointwise coproduct `K v ⊕ K v`.

Morphisms out of a value type are identities (`Schema.eq_value_of_hom`), so a
state is determined at value types by its bijections.

- Profiles: the profile of an entity is the family of values of its paths into
  value types (`Schema.Profile`, `State.profile`); morphisms of states preserve
  profiles (`State.Hom.profile_app`).
- The terminal state (`State.terminal`) has, at each object, all profiles. The
  initial state (`State.initial`) has no entity, and the values at value types.
- Limits (`State.limitCone`): at an object `a`, a profile and a compatible family
  of elements with that profile. For a connected shape the profile is that of
  any member of the family, and the limit is computed pointwise
  (`State.toEntity` preserves it).
- Colimits (`State.colimitCocone`): at an object `a`, the quotient of the
  elements of the members and the values at `a`, by the arrows of the diagram
  and by the values of the members. At an entity type no value lies, so
  colimits of every shape are computed pointwise there
  (`State.preservesColimitsOfShape_entity`); for a connected shape they are
  computed pointwise everywhere. A pushout along a shared sub-state merges two
  states: entities of the two, identified along the sub-state.
-/

namespace DDD

open CategoryTheory Limits

namespace Schema

variable {S : Schema}

/-! ## Morphisms out of value types -/

/-- The object of `S.cat` for the value type `v`. -/
abbrev valueObj (S : Schema) (v : ValueType) : S.cat := S.obj ⟨.value v, trivial⟩

/-- A morphism out of a value type ends at that value type. -/
theorem eq_value_of_hom {v : ValueType} {b : S.Obj} (f : S.valueObj v ⟶ S.obj b) :
    b.1 = .value v := by
  obtain ⟨p, -⟩ := S.mor_surjective f
  exact (eq_nil_of_tgt?_value (tgt?_names p)).2

/-- A morphism between value types is between equal value types. -/
theorem value_eq_of_hom {v v' : ValueType} (f : S.valueObj v ⟶ S.valueObj v') : v = v' :=
  (Ob.value.inj (eq_value_of_hom (b := ⟨.value v', trivial⟩) f)).symm

/-- There is at most one morphism out of a value type to an object. -/
instance {v : ValueType} {b : S.cat} : Subsingleton (S.valueObj v ⟶ b) := by
  constructor
  intro f g
  obtain ⟨b, rfl⟩ := S.obj_surjective b
  obtain ⟨p, rfl⟩ := S.mor_surjective f
  obtain ⟨q, rfl⟩ := S.mor_surjective g
  rw [names_injective p q ((eq_nil_of_tgt?_value (tgt?_names p)).1.trans
    (eq_nil_of_tgt?_value (tgt?_names q)).1.symm)]

/-- No morphism goes from a value type to an entity type. -/
theorem not_hom_value_entity {v : ValueType} {e : String} {he : S.IsOb (.entity e)}
    (f : S.valueObj v ⟶ S.obj ⟨.entity e, he⟩) : False := by
  cases eq_value_of_hom f

variable (S) (K : ValueType → Type)

/-! ## Profiles -/

/-- A profile at `a`: a value for each morphism from `a` to a value type. -/
def Profile (a : S.cat) : Type := ∀ v, (a ⟶ S.valueObj v) → K v

variable {S K} in
/-- A profile at a value type is determined by its value at the identity. -/
theorem Profile.ext_value {v : ValueType} {φ ψ : S.Profile K (S.valueObj v)}
    (h : φ v (𝟙 _) = ψ v (𝟙 _)) : φ = ψ := by
  funext v' g
  obtain rfl := value_eq_of_hom g
  rwa [Subsingleton.elim g (𝟙 _)]

/-- Profiles as a functor: a morphism `f : a ⟶ b` sends a profile at `a` to the
profile at `b` that reads the value of `g` at `f ≫ g`. -/
@[simps]
def profileFunctor : S.cat ⥤ Type where
  obj a := S.Profile K a
  map f φ v g := φ v (f ≫ g)
  map_id a := by funext φ v g; simp
  map_comp f f' := by funext φ v g; simp

/-- The values at `a`: a value of `K v` and a morphism from `v` to `a`. There are
none at an entity type. -/
@[simps]
def valueFunctor : S.cat ⥤ Type where
  obj a := Σ v, (S.valueObj v ⟶ a) × K v
  map f z := ⟨z.1, z.2.1 ≫ f, z.2.2⟩
  map_id a := by funext z; simp
  map_comp f f' := by funext z; simp

variable {S K}

/-- The value at `v` of a value at `v`. -/
def valueAt {v : ValueType} (z : (S.valueFunctor K).obj (S.valueObj v)) : K v :=
  cast (congrArg K (value_eq_of_hom z.2.1)) z.2.2

@[simp] theorem valueAt_id {v : ValueType} (k : K v) :
    valueAt (S := S) ⟨v, 𝟙 _, k⟩ = k := rfl

theorem valueAt_eq {v : ValueType} (z : (S.valueFunctor K).obj (S.valueObj v)) :
    z = ⟨v, 𝟙 _, valueAt z⟩ := by
  obtain ⟨v', g, k⟩ := z
  obtain rfl := value_eq_of_hom g
  rw [Subsingleton.elim g (𝟙 _)]
  rfl

instance {e : String} {he : S.IsOb (.entity e)} :
    IsEmpty ((S.valueFunctor K).obj (S.obj ⟨.entity e, he⟩)) :=
  ⟨fun z => not_hom_value_entity z.2.1⟩

namespace State

variable (X : S.State K)

/-- The profile of an element: the values of its images along the morphisms to value
types. -/
def profile (a : S.cat) (x : X.F.obj a) : S.Profile K a := fun v g => X.values v (X.F.map g x)

@[simp] theorem profile_apply (a : S.cat) (x : X.F.obj a) (v : ValueType)
    (g : a ⟶ S.valueObj v) : X.profile a x v g = X.values v (X.F.map g x) := rfl

theorem profile_id {v : ValueType} (x : X.F.obj (S.valueObj v)) :
    X.profile _ x v (𝟙 _) = X.values v x := by simp

theorem profile_map {a b : S.cat} (f : a ⟶ b) (x : X.F.obj a) :
    X.profile b (X.F.map f x) = (S.profileFunctor K).map f (X.profile a x) := by
  funext v g
  simp

/-- The element at `a` of a value at `a`: the image of the element with that value. -/
def ofValue (a : S.cat) (z : (S.valueFunctor K).obj a) : X.F.obj a :=
  X.F.map z.2.1 ((X.values z.1).symm z.2.2)

theorem ofValue_map {a b : S.cat} (f : a ⟶ b) (z : (S.valueFunctor K).obj a) :
    X.ofValue b ((S.valueFunctor K).map f z) = X.F.map f (X.ofValue a z) := by
  simp [ofValue]

theorem values_ofValue {v : ValueType} (z : (S.valueFunctor K).obj (S.valueObj v)) :
    X.values v (X.ofValue _ z) = valueAt z := by
  rw [valueAt_eq z]
  simp [ofValue]

/-- The underlying functor of states. -/
@[simps]
def toEntity : S.State K ⥤ S.EntityState where
  obj X := X.F
  map f := f.α

@[simp] theorem comp_α {X Y Z : S.State K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).α = f.α ≫ g.α := rfl

@[simp] theorem id_α : (𝟙 X : X ⟶ X).α = 𝟙 X.F := rfl

@[ext] theorem hom_ext {X Y : S.State K} {f g : X ⟶ Y}
    (h : ∀ a x, f.α.app a x = g.α.app a x) : f = g :=
  State.Hom.ext (NatTrans.ext (funext fun a => funext fun x => h a x))

variable {X} {Y : S.State K}

/-- A morphism is determined at value types. -/
theorem Hom.app_value (m : X ⟶ Y) {v : ValueType} (x : X.F.obj (S.valueObj v)) :
    m.α.app _ x = (Y.values v).symm (X.values v x) := by
  rw [← m.values v x, Equiv.symm_apply_apply]

/-- Morphisms preserve profiles. -/
theorem Hom.profile_app (m : X ⟶ Y) (a : S.cat) (x : X.F.obj a) :
    Y.profile a (m.α.app a x) = X.profile a x := by
  funext v g
  simp only [profile_apply]
  rw [← FunctorToTypes.naturality]
  exact m.values v _

/-- Morphisms preserve the elements of values. -/
theorem Hom.app_ofValue (m : X ⟶ Y) (a : S.cat) (z : (S.valueFunctor K).obj a) :
    m.α.app a (X.ofValue a z) = Y.ofValue a z := by
  simp only [ofValue]
  rw [FunctorToTypes.naturality, Hom.app_value, Equiv.apply_symm_apply]

/-! ## The terminal and the initial state -/

variable (S K)

/-- The terminal state: at each object, all profiles. -/
def terminal : S.State K where
  F := S.profileFunctor K
  values v :=
    { toFun := fun φ => φ v (𝟙 _)
      invFun := fun k _ g => cast (congrArg K (value_eq_of_hom g)) k
      left_inv := fun _ => Profile.ext_value rfl
      right_inv := fun _ => rfl }

/-- The initial state: no entity, and the values at value types. -/
def initial : S.State K where
  F := S.valueFunctor K
  values v :=
    { toFun := valueAt
      invFun := fun k => ⟨v, 𝟙 _, k⟩
      left_inv := fun z => (valueAt_eq z).symm
      right_inv := fun _ => rfl }

variable {S K}

@[simp] theorem terminal_values (v : ValueType) (φ : (terminal S K).F.obj (S.valueObj v)) :
    (terminal S K).values v φ = φ v (𝟙 _) := rfl

@[simp] theorem initial_values (v : ValueType) (z : (initial S K).F.obj (S.valueObj v)) :
    (initial S K).values v z = valueAt z := rfl

theorem initial_ofValue (a : S.cat) (z : (S.valueFunctor K).obj a) :
    (initial S K).ofValue a z = z := by
  obtain ⟨v, g, k⟩ := z
  change (⟨v, 𝟙 _ ≫ g, k⟩ : (S.valueFunctor K).obj a) = _
  rw [Category.id_comp]

variable (X)

/-- The morphism to the terminal state: each element goes to its profile. -/
def toTerminal : X ⟶ terminal S K where
  α := { app := X.profile, naturality := fun _ _ f => funext fun x => X.profile_map f x }
  values _ x := X.profile_id x

/-- The morphism from the initial state: each value goes to its element. -/
def fromInitial : initial S K ⟶ X where
  α := { app := X.ofValue, naturality := fun _ _ f => funext fun z => X.ofValue_map f z }
  values _ z := X.values_ofValue z

variable (S K)

/-- The state of all profiles is terminal: a morphism into it sends an element to
its profile. -/
def terminalIsTerminal : IsTerminal (terminal S K) :=
  IsTerminal.ofUniqueHom toTerminal fun Y m => by
    ext a y
    funext v g
    have h := m.values v (Y.F.map g y)
    rw [FunctorToTypes.naturality] at h
    simpa [terminal, toTerminal] using h

/-- The state with no entity is initial: a morphism out of it sends a value to its
element. -/
def initialIsInitial : IsInitial (initial S K) :=
  IsInitial.ofUniqueHom fromInitial fun Y m => by
    ext a z
    have h := m.app_ofValue a z
    rwa [initial_ofValue] at h

/-! ## Limits -/

variable {S K} {J : Type} [SmallCategory J] (F : J ⥤ S.State K)

/-- An element of the limit at `a`: a profile, and a compatible family of elements
of the members with that profile. -/
@[ext]
structure LimitElem (a : S.cat) where
  profile : S.Profile K a
  elem : ∀ j, (F.obj j).F.obj a
  compat : ∀ ⦃j j' : J⦄ (u : j ⟶ j'), (F.map u).α.app a (elem j) = elem j'
  agree : ∀ j, (F.obj j).profile a (elem j) = profile

/-- The limit as a functor. -/
@[simps]
def limitFunctor : S.cat ⥤ Type where
  obj a := LimitElem F a
  map f x :=
    { profile := (S.profileFunctor K).map f x.profile
      elem := fun j => (F.obj j).F.map f (x.elem j)
      compat := fun j j' u => by rw [FunctorToTypes.naturality, x.compat u]
      agree := fun j => by rw [State.profile_map, x.agree j] }
  map_id a := by
    funext x
    ext <;> simp
  map_comp f f' := by
    funext x
    ext <;> simp

/-- The limit of states: the bijection at a value type reads the profile at the
identity. -/
def limitState : S.State K where
  F := limitFunctor F
  values v :=
    { toFun := fun x => x.profile v (𝟙 _)
      invFun := fun k =>
        { profile := ((terminal S K).values v).symm k
          elem := fun j => ((F.obj j).values v).symm k
          compat := fun j j' u => by simp [Hom.app_value]
          agree := fun j => Profile.ext_value (by simp [terminal]) }
      left_inv := fun x => by
        apply LimitElem.ext
        · exact Profile.ext_value rfl
        · funext j
          rw [Equiv.symm_apply_eq]
          change x.profile v (𝟙 _) = _
          rw [← x.agree j, profile_id]
      right_inv := fun _ => rfl }

theorem limitState_profile (a : S.cat) (x : (limitState F).F.obj a) :
    (limitState F).profile a x = x.profile := by
  funext v g
  simp [limitState]

/-- The limit cone. -/
def limitCone : Cone F where
  pt := limitState F
  π :=
    { app := fun j =>
        { α := { app := fun a x => x.elem j }
          values := fun v x => by rw [← profile_id, x.agree j]; rfl }
      naturality := fun j j' u => by
        ext a x
        exact (x.compat u).symm }

/-- The cone is a limit. -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift s :=
    { α :=
        { app := fun a y =>
            { profile := s.pt.profile a y
              elem := fun j => (s.π.app j).α.app a y
              compat := fun j j' u => by
                have h := s.w u
                exact congrArg (fun m : s.pt ⟶ F.obj j' => m.α.app a y) h
              agree := fun j => Hom.profile_app _ a y }
          naturality := fun a b f => by
            funext y
            apply LimitElem.ext
            · exact s.pt.profile_map f y
            · funext j; exact FunctorToTypes.naturality _ _ _ f y }
      values := fun v y => s.pt.profile_id y }
  fac s j := by ext a y; rfl
  uniq s m hm := by
    ext a y
    apply LimitElem.ext
    · change (m.α.app a y).profile = s.pt.profile a y
      rw [← limitState_profile]
      exact Hom.profile_app m a y
    · funext j
      exact congrArg (fun m : s.pt ⟶ F.obj j => m.α.app a y) (hm j)

/-- Attributed states have limits of every small shape. -/
instance : HasLimitsOfShape J (S.State K) :=
  ⟨fun F => HasLimit.mk ⟨limitCone F, limitConeIsLimit F⟩⟩

instance : HasLimits (S.State K) := ⟨fun _ _ => inferInstance⟩

/-- For a connected shape, the limit at each object is the limit of the members:
the profile is that of any member of the family. -/
noncomputable def limitConeIsLimitEval [IsConnected J] (a : S.cat) :
    IsLimit (((evaluation S.cat Type).obj a).mapCone (toEntity.mapCone (limitCone F))) where
  lift s y :=
    { profile := (F.obj (Classical.arbitrary J)).profile a (s.π.app _ y)
      elem := fun j => s.π.app j y
      compat := fun j j' u => congrFun (s.w u) y
      agree := fun j => by
        refine constant_of_preserves_morphisms
          (fun j => (F.obj j).profile a (s.π.app j y)) (fun j j' u => ?_) j _
        simp only
        rw [← congrFun (s.w u) y]
        exact (Hom.profile_app (F.map u) a _).symm }
  fac s j := rfl
  uniq s m hm := by
    funext y
    apply LimitElem.ext
    · show (m y).profile = _
      rw [← (m y).agree (Classical.arbitrary J)]
      exact congrArg _ (congrFun (hm _) y)
    · funext j
      exact congrFun (hm j) y

/-- Connected limits of states are computed pointwise. -/
instance preservesLimitsOfShape_connected [IsConnected J] :
    PreservesLimitsOfShape J (toEntity (S := S) (K := K)) :=
  ⟨fun {F} => preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (evaluationJointlyReflectsLimits _ fun a => limitConeIsLimitEval F a)⟩

/-! ## Colimits -/

/-- The generators of an element of the colimit at `a`: a value at `a`, or an
element of a member. -/
abbrev ColimitPre (a : S.cat) : Type := (S.valueFunctor K).obj a ⊕ Σ j, (F.obj j).F.obj a

/-- The relation the colimit at `a` is the quotient by: an element is related to
its image along an arrow of `J`, and a value to its element in each member. -/
inductive ColimitRel (a : S.cat) : ColimitPre F a → ColimitPre F a → Prop
  | map {j j' : J} (u : j ⟶ j') (x : (F.obj j).F.obj a) (y : (F.obj j').F.obj a)
      (h : (F.map u).α.app a x = y) : ColimitRel a (.inr ⟨j, x⟩) (.inr ⟨j', y⟩)
  | value (j : J) (z : (S.valueFunctor K).obj a) (x : (F.obj j).F.obj a)
      (h : (F.obj j).ofValue a z = x) : ColimitRel a (.inl z) (.inr ⟨j, x⟩)

/-- The image of a generator along a morphism `f : a ⟶ b`. -/
def colimitPreMap {a b : S.cat} (f : a ⟶ b) : ColimitPre F a → ColimitPre F b :=
  Sum.map ((S.valueFunctor K).map f) fun p => ⟨p.1, (F.obj p.1).F.map f p.2⟩

theorem colimitRel_map {a b : S.cat} (f : a ⟶ b) {p q : ColimitPre F a}
    (h : ColimitRel F a p q) : ColimitRel F b (colimitPreMap F f p) (colimitPreMap F f q) := by
  cases h with
  | map u x y h => exact .map u _ _ (by rw [← h, FunctorToTypes.naturality])
  | value j z x h => exact .value j _ _ (by rw [← h, ofValue_map])

/-- The colimit as a functor. -/
@[simps]
def colimitFunctor : S.cat ⥤ Type where
  obj a := Quot (ColimitRel F a)
  map f := Quot.map (colimitPreMap F f) fun _ _ h => colimitRel_map F f h
  map_id a := by
    funext q
    induction q using Quot.ind with
    | mk p =>
      cases p with
      | inl z =>
        change Quot.mk _ (Sum.inl ((S.valueFunctor K).map (𝟙 a) z)) = Quot.mk _ (Sum.inl z)
        rw [FunctorToTypes.map_id_apply]
      | inr p =>
        change Quot.mk _ (Sum.inr ⟨p.1, (F.obj p.1).F.map (𝟙 a) p.2⟩ : ColimitPre F a) =
          Quot.mk _ (Sum.inr p)
        rw [FunctorToTypes.map_id_apply]
  map_comp f f' := by
    funext q
    induction q using Quot.ind with
    | mk p =>
      cases p with
      | inl z =>
        change Quot.mk _ (Sum.inl ((S.valueFunctor K).map (f ≫ f') z)) =
          Quot.mk _ (Sum.inl ((S.valueFunctor K).map f' ((S.valueFunctor K).map f z)))
        rw [FunctorToTypes.map_comp_apply]
      | inr p =>
        change Quot.mk _ (Sum.inr ⟨p.1, (F.obj p.1).F.map (f ≫ f') p.2⟩ : ColimitPre F _) =
          Quot.mk _ (Sum.inr ⟨p.1, (F.obj p.1).F.map f' ((F.obj p.1).F.map f p.2)⟩ : ColimitPre F _)
        rw [FunctorToTypes.map_comp_apply]

/-- The value at `v` of a generator at `v`. -/
def colimitValue {v : ValueType} : ColimitPre F (S.valueObj v) → K v
  | .inl z => valueAt z
  | .inr p => (F.obj p.1).values v p.2

theorem colimitValue_rel {v : ValueType} {p q : ColimitPre F (S.valueObj v)}
    (h : ColimitRel F _ p q) : colimitValue F p = colimitValue F q := by
  cases h with
  | map u x y h => exact (h ▸ (F.map u).values v x).symm
  | value j z x h => exact (h ▸ (F.obj j).values_ofValue z).symm

/-- The colimit of states: at a value type, the value of a generator. -/
def colimitState : S.State K where
  F := colimitFunctor F
  values v :=
    { toFun := Quot.lift (colimitValue F) fun _ _ h => colimitValue_rel F h
      invFun := fun k => Quot.mk _ (Sum.inl ⟨v, 𝟙 _, k⟩)
      left_inv := fun q => by
        induction q using Quot.ind with
        | mk p =>
          cases p with
          | inl z =>
            exact congrArg (fun z => (Quot.mk (ColimitRel F _) (Sum.inl z) : Quot _))
              (valueAt_eq z).symm
          | inr p =>
            exact Quot.sound (.value p.1 _ _ (by simp [ofValue, colimitValue]))
      right_inv := fun _ => rfl }

/-- The elements of values in the colimit are the generators. -/
theorem colimitState_ofValue (a : S.cat) (z : (S.valueFunctor K).obj a) :
    (colimitState F).ofValue a z = Quot.mk _ (Sum.inl z) := by
  obtain ⟨v, g, k⟩ := z
  change Quot.mk _ (Sum.inl ⟨v, 𝟙 _ ≫ g, k⟩ : ColimitPre F a) = _
  rw [Category.id_comp]

/-- The colimit cocone. -/
def colimitCocone : Cocone F where
  pt := colimitState F
  ι :=
    { app := fun j =>
        { α := { app := fun a x => Quot.mk _ (.inr ⟨j, x⟩) }
          values := fun _ _ => rfl }
      naturality := fun j j' u => by
        ext a x
        exact Quot.sound (.map u x _ rfl) |>.symm }

/-- The map out of the colimit to the apex of a cocone, on generators. -/
def colimitDesc (s : Cocone F) (a : S.cat) : ColimitPre F a → s.pt.F.obj a
  | .inl z => s.pt.ofValue a z
  | .inr p => (s.ι.app p.1).α.app a p.2

theorem colimitDesc_rel (s : Cocone F) (a : S.cat) {p q : ColimitPre F a}
    (h : ColimitRel F a p q) : colimitDesc F s a p = colimitDesc F s a q := by
  cases h with
  | map u x y h =>
    subst h
    exact (congrArg (fun m : F.obj _ ⟶ s.pt => m.α.app a x) (s.w u)).symm
  | value j z x h =>
    subst h
    exact (Hom.app_ofValue (s.ι.app j) a z).symm

/-- The cocone is a colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc s :=
    { α :=
        { app := fun a => Quot.lift (colimitDesc F s a) fun _ _ h => colimitDesc_rel F s a h
          naturality := fun a b f => by
            funext q
            induction q using Quot.ind with
            | mk p =>
              cases p with
              | inl z => exact s.pt.ofValue_map f z
              | inr p => exact FunctorToTypes.naturality _ _ (s.ι.app p.1).α f p.2 }
      values := fun v q => by
        induction q using Quot.ind with
        | mk p =>
          cases p with
          | inl z => exact s.pt.values_ofValue z
          | inr p => exact (s.ι.app p.1).values v p.2 }
  fac s j := by ext a x; rfl
  uniq s m hm := by
    ext a q
    induction q using Quot.ind with
    | mk p =>
      cases p with
      | inl z =>
        rw [← colimitState_ofValue]
        exact (Hom.app_ofValue m a z).trans (Hom.app_ofValue _ a z).symm
      | inr p => exact congrArg (fun m : F.obj p.1 ⟶ s.pt => m.α.app a p.2) (hm p.1)

/-- Attributed states have colimits of every small shape. -/
instance : HasColimitsOfShape J (S.State K) :=
  ⟨fun F => HasColimit.mk ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩

instance : HasColimits (S.State K) := ⟨fun _ _ => inferInstance⟩

/-- At an entity type, the colimit is the colimit of the members, for every shape. -/
def colimitCoconeIsColimitEntity {e : String} (he : S.IsOb (.entity e)) :
    IsColimit (((evaluation S.cat Type).obj (S.obj ⟨.entity e, he⟩)).mapCocone
      (toEntity.mapCocone (colimitCocone F))) where
  desc s := Quot.lift (fun p => match p with
      | .inl z => isEmptyElim z
      | .inr p => s.ι.app p.1 p.2) fun p q h => by
    cases h with
    | map u x y h => subst h; exact (congrFun (s.w u) x).symm
    | value j z x h => exact isEmptyElim z
  fac s j := rfl
  uniq s m hm := by
    funext q
    induction q using Quot.ind with
    | mk p =>
      cases p with
      | inl z => exact isEmptyElim z
      | inr p => exact congrFun (hm p.1) p.2

/-- For a connected shape, the colimit at each object is the colimit of the members:
a value is identified with its element in any member. -/
noncomputable def colimitCoconeIsColimitEval [IsConnected J] (a : S.cat) :
    IsColimit (((evaluation S.cat Type).obj a).mapCocone
      (toEntity.mapCocone (colimitCocone F))) where
  desc s := Quot.lift (fun p => match p with
      | .inl z => s.ι.app (Classical.arbitrary J) ((F.obj _).ofValue a z)
      | .inr p => s.ι.app p.1 p.2) fun p q h => by
    cases h with
    | map u x y h => subst h; exact (congrFun (s.w u) x).symm
    | value j z x h =>
      subst h
      refine constant_of_preserves_morphisms
        (fun j => s.ι.app j ((F.obj j).ofValue a z)) (fun j j' u => ?_) _ j
      simp only
      rw [← congrFun (s.w u), types_comp_apply]
      exact congrArg _ (Hom.app_ofValue (F.map u) a z)
  fac s j := rfl
  uniq s m hm := by
    funext q
    induction q using Quot.ind with
    | mk p =>
      cases p with
      | inl z =>
        change m _ = s.ι.app (Classical.arbitrary J) ((F.obj _).ofValue a z)
        rw [← congrFun (hm (Classical.arbitrary J)) ((F.obj _).ofValue a z)]
        exact congrArg m (Quot.sound (.value _ z _ rfl))
      | inr p => exact congrFun (hm p.1) p.2

/-- Connected colimits of states are computed pointwise. -/
instance preservesColimitsOfShape_connected [IsConnected J] :
    PreservesColimitsOfShape J (toEntity (S := S) (K := K)) :=
  ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
    (evaluationJointlyReflectsColimits _ fun a => colimitCoconeIsColimitEval F a)⟩

/-- At an entity type, colimits of states of every shape are computed pointwise. -/
instance preservesColimitsOfShape_entity {e : String} (he : S.IsOb (.entity e)) :
    PreservesColimitsOfShape J
      (toEntity (S := S) (K := K) ⋙ (evaluation S.cat Type).obj (S.obj ⟨.entity e, he⟩)) :=
  ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
    (colimitCoconeIsColimitEntity F he)⟩

end State

end Schema

end DDD
