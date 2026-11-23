module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory

theorem surjective_of_epi_of_field_to_field {K L : Type} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) [Epi φ] : Function.Surjective φ.hom := by
  letI : Algebra K L := φ.hom.toAlgebra
  have h : ∀ a : L, (a ⊗ₜ[K] (1 : L)) = (1 : L) ⊗ₜ[K] a := by
    intro a
    have e : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L))
        = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom := by
      rw [← cancel_epi φ]
      ext c
      exact congr($(Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := K) (A := L) (B := L)) c)
    exact congr(($e).hom a)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have g1 : g 1 = 1 := by simpa using congr($hg 1)
  intro a
  refine ⟨g a, ?_⟩
  have := congr(TensorProduct.rid K L (LinearMap.lTensor L g $(h a)))
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at this
  exact (Algebra.algebraMap_eq_smul_one (A := L) (g a)).trans this.symm

theorem residueFieldMap_surjective_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) :
    Function.Surjective (f.residueFieldMap x).hom := by
  have h1 : Mono (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have h2 : Mono (Spec.map (f.residueFieldMap x)) := mono_of_mono _ (Y.fromSpecResidueField (f x))
  have h3 : Mono (f.residueFieldMap x).op :=
    Scheme.Spec.mono_of_mono_map (f := (f.residueFieldMap x).op) h2
  have h4 : Epi (f.residueFieldMap x) := (CategoryTheory.op_mono_iff _).1 h3
  exact surjective_of_epi_of_field_to_field (K := Y.residueField (f x)) (L := X.residueField x) (f.residueFieldMap x)

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.SmallLift

theorem map_closedPoint {X : Scheme.{0}} {x : X} {R : CommRingCat.{0}} [IsLocalRing R]
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (closedPoint R) = x := by
  refine (Scheme.Hom.comp_apply (Spec.map φ) (X.fromSpecStalk x) (closedPoint R)).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans
    Scheme.fromSpecStalk_closedPoint

theorem step {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) [IsLocalRing (C ⧸ I)]
    (H : ∀ (a : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of C) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
      ∃ l : Spec (CommRingCat.of C) ⟶ X,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b)
    (π : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C)
    (ψ : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ I)) [IsLocalHom ψ.hom]
    (hψ : ψ.hom.comp (f.stalkMap x).hom = (Ideal.Quotient.mk I).comp π.hom) :
    ∃ g : X.presheaf.stalk x →+* C, IsLocalHom g ∧ g.comp (f.stalkMap x).hom = π.hom := by
  have e : f.stalkMap x ≫ ψ =
      π ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext1
    exact hψ
  obtain ⟨l, hl, hs⟩ := H (Spec.map ψ ≫ X.fromSpecStalk x)
    (Spec.map π ≫ Y.fromSpecStalk (f x)) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, e])
  obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.surjective l
  rw [SpecToEquivOfLocalRing_symm_apply] at hs hl
  dsimp only at hs hl
  have hmk : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hx : x' = x := by
    rw [← Spec.map_comp_assoc] at hl
    have : IsLocalHom (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ _ φ.hom hmk hφ
    have h1 := map_closedPoint (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))
    rw [hl] at h1
    exact h1.symm.trans (map_closedPoint ψ)
  subst hx
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
  have : Mono (Y.fromSpecStalk (f x')) :=
    SurjectiveOnStalks.mono_of_injective (Y.fromSpecStalk (f x')).isEmbedding.injective
  have key := Spec.map_injective ((cancel_mono _).1 hs)
  exact ⟨φ.hom, hφ, congrArg CommRingCat.Hom.hom key⟩

theorem pow_ne_top {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self n.succ_ne_zero))

theorem isLocalRing_quot {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  haveI := Ideal.Quotient.nontrivial_iff.2 (pow_ne_top (A := A) n)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem map_maximalIdeal_quot {A : Type} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)] :
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) :=
  IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) := by
  haveI := isLocalRing_quot (A := A) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  rw [← map_maximalIdeal_quot, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

theorem exists_retraction : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  intro X Y f H x _ hs n
  suffices h : ∃ ψ : X.presheaf.stalk x →+*
      Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1),
      IsLocalHom ψ ∧ ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ from
    let ⟨ψ, _, h⟩ := h; ⟨ψ, h⟩
  induction n with
  | zero =>
    let e : ResidueField (Y.presheaf.stalk (f x)) ≃+* ResidueField (X.presheaf.stalk x) :=
      RingEquiv.ofBijective (f.residueFieldMap x).hom ⟨(f.residueFieldMap x).hom.injective, hs⟩
    let q : (Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (0 + 1)) ≃+*
        ResidueField (Y.presheaf.stalk (f x)) :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    let r := (q.trans e).symm
    haveI := isLocalRing_quot (A := Y.presheaf.stalk (f x)) 0
    refine ⟨r.toRingHom.comp (residue _), ?_, ?_⟩
    · have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
      infer_instance
    · ext a
      change r (residue _ ((f.stalkMap x).hom a)) = _
      rw [RingEquiv.symm_apply_eq]
      rfl
  | succ n ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    set A := Y.presheaf.stalk (f x) with hA
    haveI := isLocalRing_quot (A := A) n
    haveI := isLocalRing_quot (A := A) (n + 1)
    haveI := isArtinianRing_quot (A := A) (n + 1)
    have hle : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1) :=
      Ideal.pow_le_pow_right (Nat.le_succ _)
    let I : Ideal (A ⧸ maximalIdeal A ^ (n + 1 + 1)) :=
      (maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mk _)
    let r : (A ⧸ maximalIdeal A ^ (n + 1)) ≃+* ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) :=
      (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    haveI : IsLocalRing ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) := r.isLocalRing
    have h1 : I ≤ maximalIdeal _ := by
      rw [← map_maximalIdeal_quot]
      exact Ideal.map_mono (Ideal.pow_le_self n.succ_ne_zero)
    have h2 : maximalIdeal _ * I = ⊥ := by
      rw [← map_maximalIdeal_quot, ← Ideal.map_mul, ← pow_succ', Ideal.map_quotient_self]
    have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
    have hl : IsLocalHom (r.toRingHom.comp ψ) := inferInstance
    let π : A →+* A ⧸ maximalIdeal A ^ (n + 1 + 1) := Ideal.Quotient.mk _
    refine @step X Y f x _ _ _ I _ (H _ I h1 h2) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (r.toRingHom.comp ψ)) hl ?_
    change (r.toRingHom.comp ψ).comp _ = _
    rw [RingHom.comp_assoc, h]
    ext a
    rfl

end GlobalTheory.SmallLift
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective m
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm
  have hx : x = t := by
    have h := congr($hm (IsLocalRing.closedPoint _))
    have e₁ := Scheme.fromSpecResidueField_apply x
      (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))
    have e₂ := Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)
    exact e₁.symm.trans (h.trans e₂)
  subst hx
  rw [← Category.assoc, ← Spec.map_comp] at hm
  have hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]
    exact (Category.id_comp _).symm
  rw [eq_top_iff]
  intro y _
  have hy : K.subtype (φ.hom y) = y := congr($hφ y)
  rw [← hy]
  exact (φ.hom y).2


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.closure_range_residueFieldMap_pullback_eq_top (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom)
  let ι : CommRingCat.of L ⟶ (pullback f g).residueField t := CommRingCat.ofHom L.subtype
  let cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.fst f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  let cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.snd f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
  have hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t := rfl
  have hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t := rfl
  have hι : Mono ι := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have e : f (pullback.fst f g t) = g (pullback.snd f g t) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have key : f.residueFieldMap (pullback.fst f g t) ≫ cx =
      (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy := by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hcx, hcy]
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr pullback.condition t
  have hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f =
      (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g := by
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Spec.map_comp_assoc]
  have hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab =
      (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
    · rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
  exact _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.ResidueDegreeChart

theorem inertiaDeg_eq_finrank_of_ker {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra K L] (φ : R →+* K) (ψ : S →+* L) (q : Ideal S)
    (hq : ∀ s, s ∈ q ↔ ψ s = 0)
    (hφ : ∀ z : K, ∃ a b, z = φ a / φ b) (hψ : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hc : ∀ r, algebraMap K L (φ r) = ψ (algebraMap R S r)) :
    q.inertiaDeg R = Module.finrank K L := by
  have hq' : q = RingHom.ker ψ := by ext s; simp [hq, RingHom.mem_ker]
  subst hq'
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
    ext r
    simp only [RingHom.mem_ker, Ideal.under, Ideal.mem_comap, ← hc]
    simp⟩
  let _ : Algebra R K := φ.toAlgebra
  let _ : Algebra S L := ψ.toAlgebra
  let _ : Algebra R L := (ψ.comp (algebraMap R S)).toAlgebra
  let _ : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  let _ : Algebra (S ⧸ RingHom.ker ψ) L := (RingHom.kerLift ψ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  have : FaithfulSMul (S ⧸ RingHom.ker ψ) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  have : IsFractionRing (R ⧸ RingHom.ker φ) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsFractionRing (S ⧸ RingHom.ker ψ) L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hψ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsScalarTower R (R ⧸ RingHom.ker φ) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⧸ RingHom.ker ψ) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Ideal.inertiaDeg_eq_of_isFractionRing (RingHom.ker φ) (RingHom.ker ψ) K L

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s, ← IsLocalRing.residue_eq_zero_iff]
  rfl

theorem exists_eq_div_evaluation {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (z : X.residueField x) :
    ∃ a b, z = (X.evaluation U x hx).hom a / (X.evaluation U x hx).hom b := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk x) t
  refine ⟨a, b, ?_⟩
  have hb : (X.evaluation U x hx).hom b ≠ 0 := fun h0 =>
    b.2 ((mem_primeIdealOf_iff hU x hx b).2 h0)
  rw [eq_div_iff hb]
  have := congrArg (X.residue x).hom h
  rw [map_mul] at this
  exact this

theorem residueDegree_eq_inertiaDeg : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  intro X Y g V hV hU w hw
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra (X.residueField (g w)) (Y.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  symm
  exact inertiaDeg_eq_finrank_of_ker (X.evaluation V (g w) hw).hom
    (Y.evaluation (g ⁻¹ᵁ V) w hw).hom _ (mem_primeIdealOf_iff hU w hw)
    (exists_eq_div_evaluation hV (g w) hw) (exists_eq_div_evaluation hU w hw)
    (fun r => Scheme.evaluation_naturality_apply g w hw r)

end GlobalTheory.ResidueDegreeChart
end

section

namespace GlobalTheory.ClosureDimensionSpecialization

open Order TopologicalSpace Topology

theorem dim_closure_le_of_specializes : ∀ (X : AlgebraicGeometry.Scheme) (z w : ↥X) (j : ℕ),
    z ⤳ w → w ≠ z →
    topologicalKrullDim (↑(closure {z}) : Type) = (↑(j + (1 : ℕ)) : WithBot ℕ∞) →
    topologicalKrullDim (↑(closure {w}) : Type) ≤ (↑j : WithBot ℕ∞) := by
  intro X z w j hzw hne hdim
  have hsub : closure ({w} : Set X) ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzw))
      isClosed_closure
  have hind : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  haveI : IrreducibleSpace (closure ({z} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  let top : IrreducibleCloseds (closure ({z} : Set X)) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hlt : ∀ a, IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a < top := by
    intro a
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro h
    have hz : (⟨z, subset_closure rfl⟩ : closure ({z} : Set X)) ∈
        (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) := by
      rw [h]; exact Set.mem_univ _
    have hcl : IsClosed {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} :=
      isClosed_closure.preimage continuous_subtype_val
    have hsub' : (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) ⊆
        {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} := by
      rw [IrreducibleCloseds.coe_map]
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hwz : w ⤳ z := specializes_iff_mem_closure.mpr (hsub' hz)
    exact hne ((hzw.antisymm hwz).eq).symm
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun a => ?_
  have h1 : height a + 1 ≤ height top :=
    calc height a + 1 ≤ height (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a) + 1 := by
          gcongr
          exact height_le_height_apply_of_strictMono _
            (IrreducibleCloseds.map_strictMono_of_isInducing hind) a
      _ ≤ height top := height_add_one_le (hlt a)
  have h2 : (height top : WithBot ℕ∞) ≤ (↑(j + (1 : ℕ)) : WithBot ℕ∞) := by
    rw [← hdim]; exact height_le_krullDim top
  have h3 : height top ≤ ((j : ℕ∞) + 1) := by exact_mod_cast h2
  have h4 : height a ≤ (j : ℕ∞) :=
    (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h1.trans h3)
  exact_mod_cast h4

end GlobalTheory.ClosureDimensionSpecialization
end

section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.PinchLift

def Glues {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
    (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
    ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b

end GlobalTheory.PinchLift
end
