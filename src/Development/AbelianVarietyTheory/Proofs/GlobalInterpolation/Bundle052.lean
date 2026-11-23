module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCompactMatrixEntryAbsSumSublevel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle044
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

namespace GlobalTheory.RealPlaceMeasuresProof

open MeasureTheory FourierTransform Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal NNReal

theorem selfDual_of_map {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (β : V → V → ℝ) (hs : ∀ x y, β x y = β y x)
    (T : V ≃L[ℝ] E) (R : V → E) (hRm : MeasurableEmbedding R)
    (hR : ∀ x y, β x y = inner ℝ (T x) (R y)) (a b : ℝ≥0) (hab : a * b = 1)
    (hT : μ.map T = a • (volume : Measure E)) (hRv : μ.map R = b • (volume : Measure E)) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((β x y : ℝ) : ℂ))) := by
  have gen : ∀ (S : V → E) (c : ℝ≥0), c ≠ 0 → MeasurableEmbedding S →
      μ.map S = c • (volume : Measure E) →
      (∀ g : E → ℂ, ∫ x, g (S x) ∂μ = ((c : ℝ) : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (S x)) μ ↔ Integrable g := by
    intro S c hc he h
    refine ⟨fun g => ?_, fun g => ?_⟩
    · rw [← he.integral_map, h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · have := he.integrable_map_iff (μ := μ) (g := g)
      rw [h] at this
      refine this.symm.trans ?_
      exact integrable_smul_measure (by exact_mod_cast hc) ENNReal.coe_ne_top
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have hb : b ≠ 0 := right_ne_zero_of_mul_eq_one hab
  obtain ⟨haI, haG⟩ := gen T a ha T.toHomeomorph.measurableEmbedding hT
  obtain ⟨hbI, hbG⟩ := gen R b hb hRm hRv
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  have hab' : ((a : ℝ) : ℂ) * ((b : ℝ) : ℂ) = 1 := by exact_mod_cast hab
  have key : ∀ (Φ : V → ℂ) (y : V),
      ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((β x y : ℝ) : ℂ)) ∂μ =
        ((a : ℝ) : ℂ) * 𝓕⁻ (fun w => Φ (T.symm w)) (R y) := by
    intro Φ y
    rw [Real.fourierInv_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  refine ⟨hμ, fun Φ hc hsup hF z => ?_⟩
  have hi : Integrable Φ μ := hc.integrable_of_hasCompactSupport hsup
  simp only [key Φ] at hF ⊢
  have hf : Integrable (fun w => Φ (T.symm w)) := by
    rw [← haG]; simpa using hi
  have hF' : Integrable (𝓕⁻ (fun w => Φ (T.symm w))) := by
    rw [← hbG]
    simpa [← mul_assoc, ha'] using hF.const_mul ((a : ℝ) : ℂ)⁻¹
  have h1 : 𝓕⁻ (fun w => Φ (T.symm w)) = 𝓕 (fun w => Φ (T.symm (-w))) :=
    Real.fourierInv_eq_fourier_comp_neg _
  have h2 : 𝓕⁻ (𝓕 (fun w => Φ (T.symm (-w)))) = fun w => Φ (T.symm (-w)) :=
    Continuous.fourierInv_fourier_eq (by fun_prop) hf.comp_neg (h1 ▸ hF')
  have h3 := congrFun h2 (T z)
  rw [← h1, Real.fourierInv_eq'] at h3
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply] at h3
  rw [← h3, ← one_mul (∫ v : E, _), ← hab', mul_assoc ((a : ℝ) : ℂ), ← hbI, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]
  rw [hs y z, hR, real_inner_comm, mul_assoc ((a : ℝ) : ℂ)]
  congr 1
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem selfDual_line {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    SelfDual (volume : Measure ℝ)
      (fun t s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (t * s) : ℝ) : ℂ))) := by
  rcases hε with rfl | rfl
  · exact selfDual_of_map volume inferInstance (fun t s => 1 * (t * s)) (fun x y => by ring)
      (ContinuousLinearEquiv.refl ℝ ℝ) id MeasurableEmbedding.id (fun x y => by simp [mul_comm])
      1 1 (one_mul 1) (by simp) (by simp)
  · exact selfDual_of_map volume inferInstance (fun t s => -1 * (t * s)) (fun x y => by ring)
      (ContinuousLinearEquiv.refl ℝ ℝ) Neg.neg (Homeomorph.neg ℝ).measurableEmbedding
      (fun x y => by simp [mul_comm]) 1 1 (one_mul 1) (by simp) (by simp)

theorem selfDual_dx {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (P Q : ℕ) :
    SelfDual (PerpendicularEmbedding.dx P Q) (fun x y : PerpendicularEmbedding.Sp P Q =>
      Complex.exp (2 * Real.pi * Complex.I *
        ((ε * (2 * (PerpendicularEmbedding.herm x y).re) : ℝ) : ℂ))) := by
  obtain ⟨u, hu1, hu2⟩ : ∃ u : Fin P ⊕ Fin Q → (ℂ ≃ₗᵢ[ℝ] ℂ),
      (∀ i z, u (Sum.inl i) z = ε * z) ∧ ∀ i z, u (Sum.inr i) z = -(ε * z) := by
    rcases hε with rfl | rfl
    · exact ⟨Sum.elim (fun _ => .refl ℝ ℂ) (fun _ => .neg ℝ), by simp, by simp⟩
    · exact ⟨Sum.elim (fun _ => .neg ℝ) (fun _ => .refl ℝ ℂ), by simp, by simp⟩
  let T : PerpendicularEmbedding.Sp P Q ≃L[ℝ] EuclideanSpace ℂ (Fin P ⊕ Fin Q) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin P ⊕ Fin Q => ℂ).symm
  let S : EuclideanSpace ℂ (Fin P ⊕ Fin Q) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin P ⊕ Fin Q) :=
    LinearIsometryEquiv.piLpCongrRight 2 u
  have hT : MeasurePreserving T volume volume :=
    (show MeasurePreserving T.toHomeomorph.toMeasurableEquiv.symm volume volume from
      GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)).symm _
  have hST : MeasurePreserving (S ∘ T) volume volume := S.measurePreserving.comp hT
  have h2 : MeasurableEmbedding fun w : EuclideanSpace ℂ (Fin P ⊕ Fin Q) => (2 : ℝ) • w :=
    (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).measurableEmbedding
  refine selfDual_of_map _ (GlobalTheory.RealPlaceCompare.isAddHaar_dx P Q)
    (fun x y => ε * (2 * (PerpendicularEmbedding.herm x y).re))
    (fun x y => by rw [← GlobalTheory.RealPlaceCompare.herm_star x y]; simp) T
    ((fun w => (2 : ℝ) • w) ∘ (S ∘ T))
    (h2.comp (S.toHomeomorph.measurableEmbedding.comp T.toHomeomorph.measurableEmbedding))
    (fun x y => ?_) (2 ^ (P + Q)) (2 ^ (P + Q))⁻¹ (mul_inv_cancel₀ (by positivity)) ?_ ?_
  · simp only [Function.comp, PiLp.inner_apply, Fintype.sum_sum_type,
      PerpendicularEmbedding.herm, Complex.sub_re, Complex.re_sum]
    have e : ∀ i, S (T y) i = u i (y i) := fun i => rfl
    have e' : ∀ i, T x i = x i := fun i => rfl
    simp only [e', Complex.inner, mul_sub, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [e, hu1, hu2] <;> ring
  · rw [PerpendicularEmbedding.dx, Measure.map_smul _ T.continuous.measurable.aemeasurable, hT.map_eq]
    ext s hs
    simp [ENNReal.smul_def]
  · rw [← Measure.map_map h2.measurable hST.measurable, PerpendicularEmbedding.dx,
      Measure.map_smul _ hST.measurable.aemeasurable, hST.map_eq,
      Measure.map_smul _ h2.measurable.aemeasurable, Measure.map_addHaar_smul _ two_ne_zero,
      GlobalTheory.finrank_real_euclideanSpace_complex, smul_smul, ENNReal.smul_def]
    congr 1
    rw [abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.coe_inv (by positivity)]
    simp only [Fintype.card_sum, Fintype.card_fin, ENNReal.ofReal_ofNat, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
    generalize P + Q = n
    rw [two_mul, pow_add, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem selfDualReal : PerpendicularEmbedding.SelfDualReal := fun _ hε =>
  ⟨selfDual_dx hε, selfDual_line hε⟩

theorem realPlaceMeasures : ActionCoordinates.RealPlaceMeasures :=
  GlobalTheory.RealPlaceCompare.typings_agree.2.2.2.1
    ⟨selfDualReal, GlobalTheory.SphereMassProof.sphereMass, GlobalTheory.CompactDualQuot.compactDualQuotient⟩

end GlobalTheory.RealPlaceMeasuresProof
end
end

section

namespace GlobalTheory.LatticeDensityClosed

theorem selfDualLatticeDensity : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity :=
  GlobalTheory.LocalDensityCompare.localDensity_iff.1
    (GlobalTheory.LatticeDensity.localDensity_of_selfDualLatticeLemmas
      GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)

end GlobalTheory.LatticeDensityClosed
end

section

noncomputable section

namespace GlobalTheory.LatticePeriodEtaObj

theorem latticePeriodEta_obj : GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement.LatticePeriodEta :=
  GlobalTheory.LatticePeriodEtaProof.latticePeriodEta

end GlobalTheory.LatticePeriodEtaObj
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.EvenThetaBound

open Complex

theorem norm_thetaChar_term_le (a b : Fin 2) (τ : ℂ) (hτ : 1 / 2 ≤ τ.im) (n : ℤ) :
    ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖ ≤
      Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) := by
  set r : ℝ := (n : ℝ) + ((a : ℕ) : ℝ) / 2 with hr
  have hw : (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2) =
      ((Real.pi * r ^ 2 : ℝ) : ℂ) * τ * I + ((Real.pi * r * ((b : ℕ) : ℝ) : ℝ) : ℂ) * I := by
    rw [hr]; push_cast; ring
  rw [hw, Complex.norm_exp, Real.exp_le_exp, add_re, mul_I_re, mul_I_re, im_ofReal_mul,
    ofReal_im, neg_zero, add_zero]
  have ha : ((a : ℕ) : ℝ) = 0 ∨ ((a : ℕ) : ℝ) = 1 := by
    rcases a with ⟨_ | _ | k, hk⟩
    · left; simp
    · right; simp
    · omega
  have hpi := Real.pi_pos
  have hr2 : (n : ℝ) ^ 2 / 2 - |(n : ℝ)| ≤ r ^ 2 / 2 := by
    have h1 : -|(n : ℝ)| ≤ (n : ℝ) := neg_abs_le _
    have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    rcases ha with h | h <;> rw [hr, h] <;> nlinarith
  have hr3 : r ^ 2 / 2 ≤ r ^ 2 * τ.im := by nlinarith [sq_nonneg r]
  have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (hr2.trans hr3) hpi.le]

theorem evenThetaConst_bounded :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀ := by
  have hs := summable_pow_mul_jacobiTheta₂_term_bound 1 (by norm_num : (0 : ℝ) < 1 / 2) 0
  simp only [pow_zero, one_mul] at hs
  have hs' : Summable (fun n : ℤ => Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|))) := by
    simpa [Int.cast_abs] using hs
  refine ⟨1 + ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)), ?_, ?_⟩
  · have : 0 ≤ ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) :=
      tsum_nonneg fun n => (Real.exp_pos _).le
    linarith
  · intro a b τ hτ
    rw [JacobiThetaHalfCharacteristic.thetaChar_eq_tsum]
    have hb : Summable (fun n : ℤ => ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
        2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖) :=
      hs'.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaChar_term_le a b τ hτ)
    calc _ ≤ ∑' n : ℤ, ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
          2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖ :=
          norm_tsum_le_tsum_norm hb
      _ ≤ ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) :=
          hb.tsum_le_tsum (norm_thetaChar_term_le a b τ hτ) hs'
      _ ≤ _ := le_add_of_nonneg_left zero_le_one

end GlobalTheory.Glob.EvenThetaBound
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.ThetaParity

open Complex

theorem jacobiTheta₂_add_int (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (z + (k : ℂ)) τ = jacobiTheta₂ z τ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : z + ((k + 1 : ℤ) : ℂ) = (z + (k : ℂ)) + 1 := by push_cast; ring
    rw [this, jacobiTheta₂_add_left]; exact_mod_cast ih
  | pred k ih =>
    have : z + ((-(k : ℤ) : ℤ) : ℂ) = (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 1 := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(k : ℤ) : ℤ) : ℂ)) τ = jacobiTheta₂ z τ := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left]

theorem jacobiTheta₂_add_int_mul_eq_zero_iff (z τ : ℂ) (l : ℤ) :
    jacobiTheta₂ (z + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  induction l using Int.induction_on with
  | zero => simp
  | succ l ih =>
    have : z + ((l + 1 : ℤ) : ℂ) * τ = (z + (l : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((l : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    exact_mod_cast ih'
  | pred l ih =>
    have : z + ((-(l : ℤ) : ℤ) : ℂ) * τ = (z + ((-(l : ℤ) - 1 : ℤ) : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(l : ℤ) : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]

theorem jacobiTheta₂_shift_eq_zero_iff (z τ : ℂ) (k l : ℤ) :
    jacobiTheta₂ (z + (k : ℂ) + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  rw [jacobiTheta₂_add_int_mul_eq_zero_iff, jacobiTheta₂_add_int]

theorem thetaChar_half_period_eq_zero_iff :
    ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  intro τ hJ m n a b _
  set t : ℂ := (τ : ℂ)

  have hprod : ThetaConstantWeber.thetaConst 0 0 τ * ThetaConstantWeber.thetaConst 0 1 τ * ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero τ.2))
  have h00 : jacobiTheta₂ 0 t ≠ 0 := by
    have := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h01 : jacobiTheta₂ (1 / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h10 : jacobiTheta₂ (t / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul hprod
    simp only [ThetaConstantWeber.thetaConst, mul_eq_zero, Complex.exp_ne_zero, false_or, ne_eq] at this
    simpa [t] using this
  have h11 : jacobiTheta₂ ((1 + t) / 2) t = 0 := by
    rw [add_comm]; exact GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period t

  set p : ℤ := m + ((b : ℕ) : ℤ)
  set q : ℤ := n + ((a : ℕ) : ℤ)
  have hred : JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * t) / 2) t = 0 ↔
      jacobiTheta₂ ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) t = 0 := by
    unfold JacobiThetaHalfCharacteristic.thetaChar
    rw [mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    have hp := Int.emod_add_mul_ediv p 2
    have hq := Int.emod_add_mul_ediv q 2
    have hp' : ((p % 2 : ℤ) : ℂ) + 2 * ((p / 2 : ℤ) : ℂ) = (m : ℂ) + ((b : ℕ) : ℂ) := by
      exact_mod_cast hp
    have hq' : ((q % 2 : ℤ) : ℂ) + 2 * ((q / 2 : ℤ) : ℂ) = (n : ℂ) + ((a : ℕ) : ℂ) := by
      exact_mod_cast hq
    have : ((m : ℂ) + (n : ℂ) * t) / 2 + (((a : ℕ) : ℂ) * t + ((b : ℕ) : ℂ)) / 2 =
        ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) := by
      linear_combination (-(1:ℂ)/2) * hp' + (-(t:ℂ)/2) * hq'
    rw [this]
  rw [hred, jacobiTheta₂_shift_eq_zero_iff, Int.odd_iff, Int.odd_iff]
  rcases Int.emod_two_eq_zero_or_one p with hp | hp <;>
    rcases Int.emod_two_eq_zero_or_one q with hq | hq <;>
    rw [hp, hq] <;> push_cast
  · simpa using h00
  · simpa using h10
  · simpa using h01
  · simpa [add_comm] using h11

end GlobalTheory.Glob.ThetaParity
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.brunTitchmarsh_exists_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  first | exact @GlobalTheory.Lin.brun_titchmarsh_const | exact GlobalTheory.Lin.brun_titchmarsh_const | (intros; apply GlobalTheory.Lin.brun_titchmarsh_const <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ, ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  first | exact @GlobalTheory.Alc.gel_dualWeyl_field | exact GlobalTheory.Alc.gel_dualWeyl_field | (intros; apply GlobalTheory.Alc.gel_dualWeyl_field <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory

theorem decay_integrable_periodise : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧
      (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧
      Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  intro F _ _ N hF Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hsz : ∀ u : Fin N → AF F, 0 ≤ sz u := fun u =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun w _ => abs_nonneg _
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [hsz 0]) k)) (hC 0)
  have key : ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧
      (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
    intro ω hω
    obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
    refine ⟨c, hcs, hc0, fun ξ y hy => ?_⟩
    by_cases hmem : fin (rat ξ + y) ∈ K
    · have h1 := hcb ξ y hy hmem
      have h2 := hC (rat ξ + y)
      calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_measure_isCov1 F
    obtain ⟨-, -, -, ⟨K₀, hK₀, hcov⟩, -⟩ := GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hν
    obtain ⟨c, hcs, hc0, hcb⟩ := key K₀ hK₀
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    let S : (Fin N → F) → Set (Fin N → AF F) := fun ξ => (fun u => u + -rat ξ) ⁻¹' K₀
    have hSm : ∀ ξ, MeasurableSet (S ξ) := fun ξ =>
      hK₀.measurableSet.preimage (measurable_add_const _)
    have hSμ : ∀ ξ, μ (S ξ) = μ K₀ := fun ξ => measure_preimage_add_right μ (-rat ξ) K₀
    have hpt : ∀ u, ‖Φ u‖ₑ ≤ ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u := by
      intro u
      obtain ⟨ξ, hξ⟩ := hcov u
      have hu : u ∈ S ξ := by
        show u + -rat ξ ∈ K₀
        rw [← sub_eq_add_neg]; exact hξ
      refine le_trans ?_ (ENNReal.le_tsum ξ)
      rw [Set.indicator_of_mem hu]
      have h3 := hcb ξ (u - rat ξ) hξ
      rw [add_sub_cancel] at h3
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h3
    have hfin : (∑' ξ, ENNReal.ofReal (C * c ξ)) < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg hC0 (hc0 ξ)) (hcs.mul_left C)]
      exact ENNReal.ofReal_lt_top
    unfold HasFiniteIntegral
    calc ∫⁻ u, ‖Φ u‖ₑ ∂μ
        ≤ ∫⁻ u, ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ := lintegral_mono hpt
      _ = ∑' ξ, ∫⁻ u, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ :=
          lintegral_tsum fun ξ => (measurable_const.indicator (hSm ξ)).aemeasurable
      _ = ∑' ξ, ENNReal.ofReal (C * c ξ) * μ K₀ := by
          congr 1; ext ξ; rw [lintegral_indicator_const (hSm ξ), hSμ]
      _ = (∑' ξ, ENNReal.ofReal (C * c ξ)) * μ K₀ := ENNReal.tsum_mul_right
      _ < ∞ := ENNReal.mul_lt_top hfin hK₀.measure_lt_top
  · intro u
    obtain ⟨c, hcs, hc0, hcb⟩ := key {u} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb ξ u rfl) (hcs.mul_left C)
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
    obtain ⟨c, hcs, hc0, hcb⟩ := key ω hωc
    have hon : ContinuousOn (fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u)) ω :=
      continuousOn_tsum (fun ξ => (hc.comp (continuous_const.add continuous_id)).continuousOn)
        (hcs.mul_left C) (fun ξ y hy => hcb ξ y hy)
    exact hon.continuousAt hωn

end GlobalTheory
end
