import DDD.Compose
import DDD.Glue
import DDD.Union

/-!
# Open schemas

An open schema from `I` to `O` is a structured cospan `I ⟶ S ⟵ O` of schemas: a
schema `S` with two interfaces, each included in `S` by the empty translation and
containing roots only, as published languages do (`OpenSchema`). `I` is the
interface on the input side, `O` the one on the output side.

- Composition (`OpenSchema.comp`): `X : I → M` and `Y : M → O` compose by gluing
  their schemas along `M`, when `M` is all they share and the glued schema is
  well-formed (`Composable`). The legs of the composite are the legs of `X` and
  `Y` followed by the legs of the gluing (`comp_legI`, `comp_legO`), and its
  schema category is the pushout in `Cat` of the two schema categories over
  `M` (`isPushout_comp`).
- Identities (`OpenSchema.id`): an interface with both legs the identity.
- Associativity (`assocIso`) and the identity laws (`compIdIso`, `idCompIso`)
  hold up to an isomorphism of schema categories that commutes with the legs.
  The proofs paste the pushout squares in `Cat`; the glued presentations differ
  in the order of their lists.
-/

namespace DDD

open CategoryTheory Limits Schema

namespace Translation

/-- Inclusions compose: the empty translation is valid from `A` to `C` when it is
valid from `A` to `B` and from `B` to `C`. -/
theorem empty_valid_trans {A B C : Schema} (hA : A.WellFormed) (hC : C.WellFormed)
    (h₁ : ({} : Translation).Valid A B) (h₂ : ({} : Translation).Valid B C) :
    ({} : Translation).Valid A C where
  entity e he := h₂.entity _ (h₁.entity e he)
  ref r hr := by
    have h := h₁.ref r hr
    simp only [ob_empty, gen_empty, tgt?_singleton] at h ⊢
    exact step?_of_sub h₂ h
  attr a ha := by
    have h := h₁.attr a ha
    simp only [ob_empty, gen_empty, tgt?_singleton] at h ⊢
    exact step?_of_sub h₂ h
  eqn q hq := by
    obtain ⟨o, hl, hr⟩ := hA.eqn_parallel q hq
    obtain ⟨hm, hpe⟩ := h₁.eqn q hq
    rw [mapPath_empty hl, mapPath_empty hr] at hpe ⊢
    have hmap := PathEq.map hC h₂ hpe
    obtain ⟨b, p, p', hp, hp', -⟩ := hpe
    have hl' := tgt?_names p
    have hr' := tgt?_names p'
    rw [hp] at hl'
    rw [hp'] at hr'
    rw [mapPath_empty hl', mapPath_empty hr'] at hmap
    exact ⟨h₂.entity _ hm, by
      have hobj : obj h₂ ⟨.entity (({} : Translation).ent q.src), hm⟩ =
          ⟨.entity (({} : Translation).ent q.src), h₂.entity _ hm⟩ := Subtype.ext (by simp [obj])
      rwa [hobj] at hmap⟩

end Translation

/-- An open schema from `I` to `O`: a schema with two interfaces, each included by
the empty translation and containing roots only. -/
structure OpenSchema (I O : Schema) where
  S : Schema
  wfI : I.WellFormed
  wfO : O.WellFormed
  wf : S.WellFormed
  inI : ({} : Translation).Valid I S
  inO : ({} : Translation).Valid O S
  rootsI : I.RootsOnly S
  rootsO : O.RootsOnly S

namespace OpenSchema

variable {I M N O : Schema}

/-- The leg of the input interface. -/
def legI (X : OpenSchema I O) : I.cat ⥤ X.S.cat := Translation.functor X.wf X.inI

/-- The leg of the output interface. -/
def legO (X : OpenSchema I O) : O.cat ⥤ X.S.cat := Translation.functor X.wf X.inO

/-- The identity on an interface that contains roots only in itself: both legs are
the identity. -/
def id (I : Schema) (hI : I.WellFormed) (hR : I.RootsOnly I) : OpenSchema I I where
  S := I
  wfI := hI
  wfO := hI
  wf := hI
  inI := Translation.empty_valid_self hI
  inO := Translation.empty_valid_self hI
  rootsI := hR
  rootsO := hR

theorem legI_id (hI : I.WellFormed) (hR : I.RootsOnly I) : (id I hI hR).legI = 𝟭 _ :=
  Translation.functor_empty_self hI _

theorem legO_id (hI : I.WellFormed) (hR : I.RootsOnly I) : (id I hI hR).legO = 𝟭 _ :=
  Translation.functor_empty_self hI _

/-! ## Composition -/

/-- `X` and `Y` compose: they share only the names of `M`, the glued schema is
well-formed, and the outer interfaces contain roots only in it. -/
structure Composable (X : OpenSchema I M) (Y : OpenSchema M O) : Prop where
  gluable : Gluable M X.S Y.S
  wf : (glue X.S Y.S).WellFormed
  rootsI : I.RootsOnly (glue X.S Y.S)
  rootsO : O.RootsOnly (glue X.S Y.S)

variable (X : OpenSchema I M) (Y : OpenSchema M O) (h : Composable X Y)

/-- The gluing of `X` and `Y` along `M`. -/
def gluing : Gluing where
  kernel := M
  left := X.S
  right := Y.S
  wf_kernel := X.wfO
  wf_left := X.wf
  wf_right := Y.wf
  wf_glued := h.wf
  gluable := h.gluable

/-- The composite of `X` and `Y`: their schemas glued along `M`. -/
def comp : OpenSchema I O where
  S := glue X.S Y.S
  wfI := X.wfI
  wfO := Y.wfO
  wf := h.wf
  inI := Translation.empty_valid_trans X.wfI h.wf X.inI (X.gluing Y h).inl_valid
  inO := Translation.empty_valid_trans Y.wfO h.wf Y.inO (X.gluing Y h).inr_valid
  rootsI := h.rootsI
  rootsO := h.rootsO

/-- The input leg of the composite: the input leg of `X`, then the left leg of the
gluing. -/
theorem comp_legI : (X.comp Y h).legI = X.legI ⋙ (X.gluing Y h).inl :=
  (Translation.functor_empty_comp_empty X.wf h.wf _ _ _).symm

/-- The output leg of the composite: the output leg of `Y`, then the right leg of
the gluing. -/
theorem comp_legO : (X.comp Y h).legO = Y.legO ⋙ (X.gluing Y h).inr :=
  (Translation.functor_empty_comp_empty Y.wf h.wf _ _ _).symm

/-- The schema category of the composite is the pushout in `Cat` of the schema
categories of `X` and `Y` over `M`. -/
theorem isPushout_comp :
    IsPushout (C := Cat.{0, 0}) X.legO Y.legI (X.gluing Y h).inl (X.gluing Y h).inr :=
  (X.gluing Y h).isPushout

/-! ## Associativity -/

section Assoc

variable (X : OpenSchema I M) (Y : OpenSchema M N) (Z : OpenSchema N O)
  (hXY : Composable X Y) (hXY_Z : Composable (X.comp Y hXY) Z)
  (hYZ : Composable Y Z) (hX_YZ : Composable X (Y.comp Z hYZ))

/-- The schema category of `X ∘ Y` maps to that of `X ∘ (Y ∘ Z)`: `X` by its leg,
`Y` through `Y ∘ Z`. -/
noncomputable def assocMap :
    (X.comp Y hXY).S.cat ⟶ (X.comp (Y.comp Z hYZ) hX_YZ).S.cat :=
  (X.isPushout_comp Y hXY).desc (C := Cat.{0, 0}) (X.gluing (Y.comp Z hYZ) hX_YZ).inl
    ((Y.gluing Z hYZ).inl ⋙ (X.gluing (Y.comp Z hYZ) hX_YZ).inr) (by
      have hw := (X.isPushout_comp (Y.comp Z hYZ) hX_YZ).w
      rw [comp_legI] at hw
      exact hw)

theorem inl_assocMap : (X.gluing Y hXY).inl ⋙ assocMap X Y Z hXY hYZ hX_YZ =
    (X.gluing (Y.comp Z hYZ) hX_YZ).inl :=
  (X.isPushout_comp Y hXY).inl_desc (C := Cat.{0, 0}) _ _ _

theorem inr_assocMap : (X.gluing Y hXY).inr ⋙ assocMap X Y Z hXY hYZ hX_YZ =
    (Y.gluing Z hYZ).inl ⋙ (X.gluing (Y.comp Z hYZ) hX_YZ).inr :=
  (X.isPushout_comp Y hXY).inr_desc (C := Cat.{0, 0}) _ _ _

/-- `X ∘ (Y ∘ Z)` is a pushout of `X ∘ Y` and `Z` over `N`. -/
theorem isPushout_assoc :
    IsPushout (C := Cat.{0, 0}) (X.comp Y hXY).legO Z.legI (assocMap X Y Z hXY hYZ hX_YZ)
      ((Y.gluing Z hYZ).inr ⋙ (X.gluing (Y.comp Z hYZ) hX_YZ).inr) := by
  have hbot : IsPushout (C := Cat.{0, 0}) (X.gluing Y hXY).inr (Y.gluing Z hYZ).inl
      (assocMap X Y Z hXY hYZ hX_YZ) (X.gluing (Y.comp Z hYZ) hX_YZ).inr := by
    refine IsPushout.of_top (C := Cat.{0, 0}) ?_ (inr_assocMap X Y Z hXY hYZ hX_YZ)
      (X.isPushout_comp Y hXY)
    have hs := X.isPushout_comp (Y.comp Z hYZ) hX_YZ
    rw [comp_legI, ← inl_assocMap X Y Z hXY hYZ hX_YZ] at hs
    exact hs
  have hpaste := IsPushout.paste_horiz (C := Cat.{0, 0}) (Y.isPushout_comp Z hYZ) hbot
  rw [comp_legO]
  exact hpaste

/-- Associativity: the schema categories of `(X ∘ Y) ∘ Z` and `X ∘ (Y ∘ Z)` are
isomorphic. -/
noncomputable def assocIso :
    ((X.comp Y hXY).comp Z hXY_Z).S.cat ≅ (X.comp (Y.comp Z hYZ) hX_YZ).S.cat :=
  ((X.comp Y hXY).isPushout_comp Z hXY_Z).isoIsPushout _ _ (isPushout_assoc X Y Z hXY hYZ hX_YZ)

/-- The isomorphism commutes with the input legs. -/
theorem assocIso_legI :
    ((X.comp Y hXY).comp Z hXY_Z).legI ⋙ (assocIso X Y Z hXY hXY_Z hYZ hX_YZ).hom =
      (X.comp (Y.comp Z hYZ) hX_YZ).legI := by
  have h := IsPushout.inl_isoIsPushout_hom (C := Cat.{0, 0}) _ _
    ((X.comp Y hXY).isPushout_comp Z hXY_Z) (isPushout_assoc X Y Z hXY hYZ hX_YZ)
  change ((X.comp Y hXY).gluing Z hXY_Z).inl ⋙ (assocIso X Y Z hXY hXY_Z hYZ hX_YZ).hom =
    assocMap X Y Z hXY hYZ hX_YZ at h
  simp only [comp_legI, Functor.assoc]
  rw [h, inl_assocMap]

/-- The isomorphism commutes with the output legs. -/
theorem assocIso_legO :
    ((X.comp Y hXY).comp Z hXY_Z).legO ⋙ (assocIso X Y Z hXY hXY_Z hYZ hX_YZ).hom =
      (X.comp (Y.comp Z hYZ) hX_YZ).legO := by
  have h := IsPushout.inr_isoIsPushout_hom (C := Cat.{0, 0}) _ _
    ((X.comp Y hXY).isPushout_comp Z hXY_Z) (isPushout_assoc X Y Z hXY hYZ hX_YZ)
  change ((X.comp Y hXY).gluing Z hXY_Z).inr ⋙ (assocIso X Y Z hXY hXY_Z hYZ hX_YZ).hom =
    (Y.gluing Z hYZ).inr ⋙ (X.gluing (Y.comp Z hYZ) hX_YZ).inr at h
  simp only [comp_legO, Functor.assoc]
  rw [h]

end Assoc

/-! ## Identities -/

section Identity

variable (X : OpenSchema I O)

theorem isPushout_id_right (hO : O.WellFormed) (hR : O.RootsOnly O) :
    IsPushout (C := Cat.{0, 0}) X.legO (id O hO hR).legI (𝟭 X.S.cat) X.legO := by
  rw [legI_id]
  exact IsPushout.id_vert (C := Cat.{0, 0}) X.legO

theorem isPushout_id_left (hI : I.WellFormed) (hR : I.RootsOnly I) :
    IsPushout (C := Cat.{0, 0}) (id I hI hR).legO X.legI X.legI (𝟭 X.S.cat) := by
  rw [legO_id]
  exact IsPushout.id_horiz (C := Cat.{0, 0}) X.legI

/-- The right identity law: the schema category of `X ∘ id` is isomorphic to that
of `X`. -/
noncomputable def compIdIso (hO : O.WellFormed) (hR : O.RootsOnly O)
    (h : Composable X (id O hO hR)) : (X.comp (id O hO hR) h).S.cat ≅ X.S.cat :=
  (X.isPushout_comp (id O hO hR) h).isoIsPushout _ _ (X.isPushout_id_right hO hR)

theorem compIdIso_legI (hO : O.WellFormed) (hR : O.RootsOnly O)
    (h : Composable X (id O hO hR)) :
    (X.comp (id O hO hR) h).legI ⋙ (X.compIdIso hO hR h).hom = X.legI := by
  have h' := IsPushout.inl_isoIsPushout_hom (C := Cat.{0, 0}) _ _
    (X.isPushout_comp (id O hO hR) h) (X.isPushout_id_right hO hR)
  change (X.gluing (id O hO hR) h).inl ⋙ (X.compIdIso hO hR h).hom = 𝟭 _ at h'
  rw [comp_legI, Functor.assoc, h']
  rfl

theorem compIdIso_legO (hO : O.WellFormed) (hR : O.RootsOnly O)
    (h : Composable X (id O hO hR)) :
    (X.comp (id O hO hR) h).legO ⋙ (X.compIdIso hO hR h).hom = X.legO := by
  have h' := IsPushout.inr_isoIsPushout_hom (C := Cat.{0, 0}) _ _
    (X.isPushout_comp (id O hO hR) h) (X.isPushout_id_right hO hR)
  change (X.gluing (id O hO hR) h).inr ⋙ (X.compIdIso hO hR h).hom = X.legO at h'
  rw [comp_legO, Functor.assoc, h', legO_id, Functor.id_comp]

/-- The left identity law: the schema category of `id ∘ X` is isomorphic to that
of `X`. -/
noncomputable def idCompIso (hI : I.WellFormed) (hR : I.RootsOnly I)
    (h : Composable (id I hI hR) X) : ((id I hI hR).comp X h).S.cat ≅ X.S.cat :=
  ((id I hI hR).isPushout_comp X h).isoIsPushout _ _ (X.isPushout_id_left hI hR)

theorem idCompIso_legI (hI : I.WellFormed) (hR : I.RootsOnly I)
    (h : Composable (id I hI hR) X) :
    ((id I hI hR).comp X h).legI ⋙ (X.idCompIso hI hR h).hom = X.legI := by
  have h' := IsPushout.inl_isoIsPushout_hom (C := Cat.{0, 0}) _ _
    ((id I hI hR).isPushout_comp X h) (X.isPushout_id_left hI hR)
  change ((id I hI hR).gluing X h).inl ⋙ (X.idCompIso hI hR h).hom = X.legI at h'
  rw [comp_legI, Functor.assoc, h', legI_id, Functor.id_comp]

theorem idCompIso_legO (hI : I.WellFormed) (hR : I.RootsOnly I)
    (h : Composable (id I hI hR) X) :
    ((id I hI hR).comp X h).legO ⋙ (X.idCompIso hI hR h).hom = X.legO := by
  have h' := IsPushout.inr_isoIsPushout_hom (C := Cat.{0, 0}) _ _
    ((id I hI hR).isPushout_comp X h) (X.isPushout_id_left hI hR)
  change ((id I hI hR).gluing X h).inr ⋙ (X.idCompIso hI hR h).hom = 𝟭 _ at h'
  rw [comp_legO, Functor.assoc, h']
  rfl

end Identity

end OpenSchema

end DDD
