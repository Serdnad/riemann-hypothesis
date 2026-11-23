module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle175
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent


open MvPolynomial in
theorem normIdeal_top (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
    [FiniteDimensional K L] [CommRing B] [Algebra B L] :
    GlobalTheory.NormSheaf.normIdeal A K L B (⊤ : Ideal B) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨1, fun _ => 1, fun _ => Submodule.mem_top, Finsupp.single 0 (Module.finrank K L), ?_⟩
  have hform : GlobalTheory.NormSheaf.normForm K L (fun _ : Fin 1 => algebraMap B L 1) =
      X 0 ^ Module.finrank K L := by
    unfold GlobalTheory.NormSheaf.normForm
    simp [Fin.sum_univ_one, map_one, Matrix.det_smul]
  rw [hform, coeff_X_pow]
  simp

theorem ideal_eq_top_of_forall_not_mem {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ x ∈ I.support, x ∉ V.1) : I.ideal V = ⊤ := by
  have hV : IsAffineOpen V.1 := V.2
  have hempty : X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) ∩ V.1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxV
    exact h x ((Scheme.IdealSheafData.mem_support_iff_of_mem hxV).2 hx) hxV
  rw [← hV.fromSpec_image_zeroLocus] at hempty
  have h0 : PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(X, V.1)) = ∅ := Set.image_eq_empty.mp hempty
  rw [PrimeSpectrum.zeroLocus_empty_iff_eq_top] at h0
  exact h0

theorem famIdeal_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  intro Y Z π _ _ hK hfd I U hU
  unfold famIdeal
  split_ifs with h
  · have hV : I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ = ⊤ :=
      ideal_eq_top_of_forall_not_mem I _ (fun y hy hyV => hU y hy hyV)
    simp only [hV]
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    exact normIdeal_top _ _ _ _
  · rfl

end GlobalTheory.NormSheafDescent
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem finiteDimensional_functionField : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  letI := fieldK π hK
  letI := algKL π
  obtain ⟨U, hU, hζU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := genPt π) trivial
  have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
  let f : Γ(Z, U) →+* Z.presheaf.stalk (genPt π) := (Z.presheaf.germ U (genPt π) hζU).hom
  let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField :=
    (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hηU).hom
  let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
  have hsq : ∀ a, algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) = φ (g a) :=
    fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
  have hfin : g.Finite := IsFinite.finite_app π U hU
  letI : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
  haveI : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  letI : Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField := φ.toAlgebra
  haveI : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ hV
  have hint : ∀ b, IsIntegral (Z.presheaf.stalk (genPt π)) (φ b) := by
    intro b
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
    refine ⟨p.map f, hp.map f, ?_⟩
    have e : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp f = φ.comp g :=
      RingHom.ext hsq
    have hpb' : p.eval₂ g b = 0 := hpb
    rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
  haveI : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
  have hF : FiniteDimensional (Z.presheaf.stalk (genPt π))
      (IntermediateField.adjoin (Z.presheaf.stalk (genPt π)) (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
  have hmem : ∀ b, φ b ∈ IntermediateField.adjoin (Z.presheaf.stalk (genPt π))
      (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := by
    intro b
    have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have e : φ (a • x) = algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) * φ x := by
        rw [hsq, Algebra.smul_def, map_mul]; rfl
      rw [e]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
  have htop : IntermediateField.adjoin (Z.presheaf.stalk (genPt π))
      (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
    exact div_mem (hmem b) (hmem c)
  have h2 : FiniteDimensional (Z.presheaf.stalk (genPt π))
      (⊤ : IntermediateField (Z.presheaf.stalk (genPt π)) Y.functionField) := htop ▸ hF
  exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv

end GlobalTheory.NormSheafDescent
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    letI := GlobalTheory.NormSheafDescent.algKL π;
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  let := GlobalTheory.NormSheafDescent.fieldK π hK
  let := GlobalTheory.NormSheafDescent.algKL π
  let K := Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)
  have hFinite : FiniteDimensional K Y.functionField := by
    obtain ⟨U, hU, hζU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := Z) (U := ⊤) (x := GlobalTheory.NormSheafDescent.genPt π) trivial
    have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
    have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
    let f : Γ(Z, U) →+* K :=
      (Z.presheaf.germ U (GlobalTheory.NormSheafDescent.genPt π) hζU).hom
    let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField := (Y.germToFunctionField (π ⁻¹ᵁ U)).hom
    let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
    have hsq : ∀ a, algebraMap K Y.functionField (f a) = φ (g a) :=
      fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
    let : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
    have : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := π.finite_app U hU
    have : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ hV
    have hint (b : Γ(Y, π ⁻¹ᵁ U)) : IsIntegral K (φ b) := by
      obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
      refine ⟨p.map f, hp.map f, ?_⟩
      have e : (algebraMap K Y.functionField).comp f = φ.comp g := RingHom.ext hsq
      have hpb' : p.eval₂ g b = 0 := hpb
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
    have : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
    let E := IntermediateField.adjoin K (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))
    have hE : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
    have hmem (b : Γ(Y, π ⁻¹ᵁ U)) : φ b ∈ E := by
      have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) :=
        hs ▸ Submodule.mem_top
      induction hb using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        have e : φ (a • x) = algebraMap K Y.functionField (f a) * φ x := by
          rw [hsq, Algebra.smul_def, map_mul]
          rfl
        rw [e]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    have htop : E = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨b, c, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
      exact div_mem (hmem b) (hmem c)
    have : FiniteDimensional K (⊤ : IntermediateField K Y.functionField) := htop ▸ hE
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  exact hFinite
end

section

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem hasSum_integral_theta (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ)
    (hC : ∀ j, ‖a j‖ ≤ C) (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (hint : ∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j)))
    (hsum : Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖)) :
    HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y)
      (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  set F : ι → (I → ℝ) → ℂ := fun j y => a j * ((p y : ℂ) * term n s (e j) y) with hF
  have hpm : AEStronglyMeasurable (fun y => (p y : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hp).aestronglyMeasurable
  have hpb : ∀ᵐ y ∂(volume : Measure (I → ℝ)), ‖(p y : ℂ)‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]; exact hp1 y
  have hpint : ∀ j, Integrable (fun y => (p y : ℂ) * term n s (e j) y) :=
    fun j => (hint j).bdd_mul hpm hpb
  have hFint : ∀ j, Integrable (F j) := fun j => (hpint j).const_mul (a j)
  have hnorm : ∀ j y, ‖F j y‖ = ‖a j‖ * (p y * ‖term n s (e j) y‖) := by
    intro j y
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]
  have hFsum : Summable fun j => ∫ y, ‖F j y‖ := by
    have hi : ∀ j, ∫ y, ‖F j y‖ = ‖a j‖ * ∫ y, p y * ‖term n s (e j) y‖ := by
      intro j; simp_rw [hnorm]; exact integral_const_mul _ _
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) (fun j => ?_) (hsum.mul_left C)
    rw [hi]
    exact mul_le_mul_of_nonneg_right (hC j)
      (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))
  have h := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hl : (fun j => ∫ y, F j y) = fun j => a j * ∫ y, (p y : ℂ) * term n s (e j) y := by
    funext j; exact integral_const_mul _ _
  have hr : (fun y => ∑' j, F j y) =
      fun y => (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
    funext y
    simp only [hF, GlobalTheory.HeckeTheta.theta, term]
    rw [← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext j; ring
  rw [hl, hr] at h
  exact h

end GlobalTheory.HeckeMellin
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_surjective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (U : T.affineOpens) : Function.Surjective (kappa A B g I U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (str A B) g) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hle : (⊤ : Subring Γ(pullback (str A B) g, W)) ≤
      (kappa A B g I U).range.comap (I.subschemeι.app W).hom := by
    rw [← hgen, Subring.closure_le]
    rintro _ (⟨z, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1 ⊗ₜ (Scheme.ΓSpecIso (CommRingCat.of B)).hom z, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, one_mul, Iso.hom_inv_id_apply]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      rfl
    · refine ⟨c ⊗ₜ 1, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, mul_one]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE]
      rfl
  intro y
  obtain ⟨x, hx⟩ := I.subschemeι_app_surjective ⟨W, hW⟩ y
  obtain ⟨w, hw⟩ := hle (Subring.mem_top x)
  exact ⟨w, hw.trans hx⟩

end GlobalTheory.HilbAff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem secAlg_toSpecΓ_top (Z : Scheme.{0}) :
    secAlg Γ(Z, ⊤) Z.toSpecΓ ⊤ = RingHom.id _ := by
  ext a
  have e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop := (Scheme.Hom.app_eq_appLE _).symm
  simp only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]
  simp

theorem exists_hom_secAlg_top (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)) :
    ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩
  rw [secAlg_comp, secAlg_toSpecΓ_top]
  rfl

end GlobalTheory.HilbAff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_res_apply (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    {U V : T.Opens} (h : U ≤ V) :
    letI := (secAlg A g U).toAlgebra
    letI := (secAlg A g V).toAlgebra
    ∀ (ρ : Γ(T, V) →ₐ[A] Γ(T, U)), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom →
    ∀ t : Γ(T, V) ⊗[A] B,
      kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (kappa A B g I V t) := by
  letI := (secAlg A g U).toAlgebra
  letI := (secAlg A g V).toAlgebra
  intro ρ hρ t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
    have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := by
      rw [← hρ]; rfl
    rw [hc]
    congr 1
    · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
          (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
          (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
      exact (congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm

theorem kappa_res (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (U V : T.affineOpens) (h : (U : T.Opens) ≤ V) :
    letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
    letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
    ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
      (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤ RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        change _ = GlobalTheory.HilbAff.secAlg A g U a
        rw [← GlobalTheory.HilbAff.secAlg_res A g h]; rfl }
  refine ⟨ρ, rfl, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [GlobalTheory.HilbAff.kappa_res_apply A B g I h ρ rfl t, ht, map_zero]

end GlobalTheory.HilbAff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct


theorem _root_.GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
      (g : T ⟶ Spec (CommRingCat.of A))
      (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
      (U V : T.affineOpens) (h : (U : T.Opens) ≤ V),
      letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
      ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
        (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
          (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤
        RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  intro A B _ _ _ T g I U V h
  let := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  let := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
          (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op) }
  refine ⟨ρ, rfl, ?_⟩
  have kappa_tmul (W : T.Opens) (c : Γ(T, W)) (b : B) :
      letI := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
      GlobalTheory.HilbAff.kappa A B g I W (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd _ g).app W).hom c *
          ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) (by simp)).hom
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
    let := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
    let : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) :=
      (((I.subschemeι ≫ pullback.snd _ g).app W).hom.comp
        (GlobalTheory.HilbAff.secAlg A g W)).toAlgebra
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hκ (t : Γ(T, V) ⊗[A] B) :
      GlobalTheory.HilbAff.kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (GlobalTheory.HilbAff.kappa A B g I V t) := by
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
      have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := rfl
      rw [hc]
      congr 1
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
        rfl
      · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
            (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
            (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
        exact (congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [hκ t, ht, map_zero]
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.intertwiner_fixes_of_local_vacuum' : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M), (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = e) → ∀ P : X →ₗ[R] X, (∀ x y, γ (P x) y = γ x (P y)) → (∀ a ∈ A, P a ∈ A) → (∀ x, φ (x - P x) = x - P x) → ∀ m : M, (∀ a ∈ A, W (P a) m = m) → T m = m := by
  first | exact @GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum | exact GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum | (intros; apply GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum <;> assumption)
end
