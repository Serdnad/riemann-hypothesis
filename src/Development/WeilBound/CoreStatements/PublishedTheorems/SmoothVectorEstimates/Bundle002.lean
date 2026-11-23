module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace HaarPairing

open scoped FourierTransform RealInnerProductSpace Real SchwartzMap

theorem inv_E {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ w, 𝐞 ⟪w, v⟫ • (∫ z, 𝐞 (-⟪z, w⟫) • g z) = g v := by
  have hI : Integrable (𝓕 g) := by
    let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := 𝓕 (hc.toSchwartzMap hg)
    have e : (𝓕 g) = ⇑G := by
      simp only [G, SchwartzMap.fourier_coe]; rfl
    rw [e]; exact G.integrable
  have h := congrFun (hg.continuous.fourierInv_fourier_eq
    (hg.continuous.integrable_of_hasCompactSupport hc) hI) v
  rw [Real.fourierInv_eq] at h
  simpa only [Real.fourier_eq] using h

theorem haar_E {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {d : ℕ}
    (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d) → ℂ,
      ∫ x, h (e x) ∂μ = ((c : ℝ) : ℂ) * ∫ z, h z := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set c := Measure.addHaarScalarFactor (μ.map e) volume with hc
  have hm : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun h => ?_⟩
  have key : ∫ x, h (e x) ∂μ = ∫ z, h z ∂(μ.map e) :=
    (e.toHomeomorph.measurableEmbedding.integral_map h).symm
  rw [key, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem pair {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ T A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x y, β x y = 2 * π * ⟪T x, A y⟫ := by
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let φ : V → StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := fun y =>
    (2 * π)⁻¹ • (β.flip y).comp (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)
  have φadd : ∀ y y', φ (y + y') = φ y + φ y' := by
    intro y y'; simp only [φ, map_add (f := _), ContinuousLinearMap.add_comp, smul_add]
  have φsmul : ∀ (r : ℝ) y, φ (r • y) = r • φ y := by
    intro r y; simp only [φ, map_smul, ContinuousLinearMap.smul_comp, smul_comm r]
  let L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ _).symm (φ y)
      map_add' := fun y y' => by simp only [φadd, map_add (f := _)]
      map_smul' := fun r y => by
        simp only [φsmul, LinearIsometryEquiv.map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }
  have hL : ∀ x y, ⟪T x, L y⟫ = (2 * π)⁻¹ * β x y := by
    intro x y
    rw [real_inner_comm]
    change ⟪(InnerProductSpace.toDual ℝ _).symm (φ y), T x⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp [φ]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hβ
    intro x
    have h1 := hL x y
    rw [hy, inner_zero_right] at h1
    have hp : (2 * π)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hp
  let A := (L.linearEquivOfInjective hinj finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv
  refine ⟨T, A, fun x y => ?_⟩
  have hA : A y = L y := rfl
  rw [hA, hL]
  field_simp

end HaarPairing

theorem haar_measure_pairing : S5 := by
  intro V _ _ _ _ _ μ _ β hβ
  obtain ⟨T, A, hTA⟩ := HaarPairing.pair β hβ
  obtain ⟨c1, hc1, h1⟩ := HaarPairing.haar_E μ T
  obtain ⟨c2, hc2, h2⟩ := HaarPairing.haar_E μ A
  refine ⟨((c1 : ℝ) : ℂ) * ((c2 : ℝ) : ℂ), mul_ne_zero (by exact_mod_cast hc1) (by exact_mod_cast hc2),
    fun f hf hc ξ => ?_⟩
  set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ := f ∘ T.symm with hg_def
  have hgs : ContDiff ℝ ∞ g := hf.comp T.symm.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph T.symm.toHomeomorph
  have hFT : ∀ y, FT μ β f y = ((c1 : ℝ) : ℂ) *
      ∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z := by
    intro y
    rw [FT, ← h1 (fun z => Real.fourierChar (-inner ℝ z (A y)) • g z)]
    congr 1 with x
    simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul, hTA]
    push_cast
    ring_nf
  have step : ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ =
      ((c1 : ℝ) : ℂ) * ∫ y, Real.fourierChar (inner ℝ (A y) (T ξ)) •
        (∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z) ∂μ := by
    rw [← integral_const_mul]
    congr 1 with y
    simp only [hFT, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA, real_inner_comm (A y)]
    push_cast
    ring_nf
  have h2' := h2 (fun w => Real.fourierChar (inner ℝ w (T ξ)) •
    ∫ z, Real.fourierChar (-inner ℝ z w) • g z)
  rw [step, h2', HaarPairing.inv_E g hgs hgc]
  simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  ring

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace FourierIntegralBound

open Real

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) :=
  _root_.UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main t ht N

lemma pi_pow_le {d : ℕ} (z : Fin d → ℝ) (N : ℕ) : ‖z‖ ^ N ≤ 1 + ∑ i, |z i| ^ N := by
  have hs : 0 ≤ ∑ i, |z i| ^ N := Finset.sum_nonneg (fun i _ => by positivity)
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · have : ‖z‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => isEmptyElim i)
    have h0 : ‖z‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) this
    linarith
  · obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |z i|) Finset.univ_nonempty
    have h1 : ‖z‖ ≤ |z i0| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun i => by
      rw [Real.norm_eq_abs]; exact hi0 i (Finset.mem_univ _))
    have h2 : ‖z‖ ^ N ≤ |z i0| ^ N := pow_le_pow_left₀ (norm_nonneg _) h1 N
    have h3 : |z i0| ^ N ≤ ∑ i, |z i| ^ N :=
      Finset.single_le_sum (f := fun i => |z i| ^ N) (fun i _ => by positivity) (Finset.mem_univ i0)
    linarith

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sc (β : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ := (2 * π)⁻¹ • β

lemma sc_apply (β : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) : sc β x y = (2 * π)⁻¹ * β x y := by
  simp [sc]

lemma FT_eq [MeasurableSpace V] {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (μ : Measure V) (β : V →L[ℝ] V →L[ℝ] ℝ) (F : V → X) :
    FT μ β F = VectorFourier.fourierIntegral Real.fourierChar μ (sc β).toLinearMap₁₂ F := by
  ext y
  unfold FT VectorFourier.fourierIntegral
  congr 1
  ext x
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  rw [show (sc β).toLinearMap₁₂ x y = sc β x y from rfl, sc_apply]
  push_cast
  field_simp

lemma exists_strictHenselian_absolutely_closed_local_ring [FiniteDimensional ℝ V] (β : V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ (d : ℕ) (b : Fin d → V) (K : ℝ), 0 ≤ K ∧
      ∀ y, ‖y‖ ≤ K * ‖(fun i => β (b i) y : Fin d → ℝ)‖ := by
  let b := Module.finBasis ℝ V
  let T : V →ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearMap.pi (fun i => ((β (b i) : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ))
  have hT : ∀ y, T y = fun i => β (b i) y := fun y => rfl
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply hβ y
    have h1 : ∀ i, β (b i) y = 0 := fun i => by
      have := congrFun hy i
      rw [hT] at this
      simpa using this
    have h2 : ((β.flip y : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) = 0 :=
      b.ext (fun i => by simpa using h1 i)
    intro x
    have := LinearMap.congr_fun h2 x
    simpa using this
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hker
  refine ⟨_, b, K, K.2, fun y => ?_⟩
  have := hK.le_mul_dist y 0
  rw [map_zero, dist_zero_right, dist_zero_right] at this
  exact this

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [FiniteDimensional ℝ V] in
lemma integ {F : V → X} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (μ : Measure V)
    [IsFiniteMeasureOnCompacts μ] (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow k).mul (hF.continuous_iteratedFDeriv (mod_cast le_top)).norm
  · exact (hc.iteratedFDeriv n).norm.mul_left

lemma pw_bd (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →L[ℝ] V →L[ℝ] ℝ) {F : V → X}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (n : ℕ) :
    ∃ B : ℝ, ∀ v y, |β v y| ^ n * ‖FT μ β F y‖ ≤ ‖v‖ ^ n * B := by
  refine ⟨(2 * π) ^ n * ((2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
      ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ), fun v y => ?_⟩
  have H := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (L := sc β) (μ := μ)
    (K := ⊤) (N := ⊤) hF (fun k n _ _ => integ hF hc μ k n) (k := 0) (n := n) le_top le_top v y
  rw [norm_iteratedFDeriv_zero, ← FT_eq] at H
  have e : |β v y| = 2 * π * |sc β v y| := by
    rw [sc_apply, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
    field_simp
  rw [e, mul_pow, mul_assoc]
  calc (2 * π) ^ n * (|sc β v y| ^ n * ‖FT μ β F y‖)
      ≤ (2 * π) ^ n * (‖v‖ ^ n * (2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
          ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
            ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ) := by gcongr
    _ = _ := by ring

end FourierIntegralBound

open FourierIntegralBound in
theorem valuation_bound_of_three : S4 := by
  unfold S4 ForV
  intro V _ _ _ _ _ μ _ β hβ X _ _ _ F hF hc
  refine ⟨?_, fun N => ?_⟩
  · rw [FT_eq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by apply (sc β).continuous₂) (hF.continuous.integrable_of_hasCompactSupport hc)
  · obtain ⟨d, b, K, hK0, hK⟩ := exists_strictHenselian_absolutely_closed_local_ring β hβ
    obtain ⟨A, hA⟩ := pw_bd μ β hF hc 0
    obtain ⟨B, hB⟩ := pw_bd μ β hF hc N
    refine ⟨2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)), fun y => ?_⟩
    have hA' : ‖FT μ β F y‖ ≤ A := by simpa using hA 0 y
    have hy := pi_pow_le (fun i => β (b i) y) N
    have h1 : ‖y‖ ^ N ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) := by
      calc ‖y‖ ^ N ≤ (K * ‖(fun i => β (b i) y : Fin d → ℝ)‖) ^ N :=
            pow_le_pow_left₀ (norm_nonneg _) (hK y) N
        _ = K ^ N * ‖(fun i => β (b i) y : Fin d → ℝ)‖ ^ N := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have h3 : (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ ≤ A + ∑ i, ‖b i‖ ^ N * B := by
      rw [add_mul, Finset.sum_mul, one_mul]
      exact add_le_add hA' (Finset.sum_le_sum fun i _ => hB (b i) y)
    have hFn := norm_nonneg (FT μ β F y)
    calc (1 + ‖y‖) ^ N * ‖FT μ β F y‖ ≤ 2 ^ N * (1 + ‖y‖ ^ N) * ‖FT μ β F y‖ := by
          gcongr; exact one_add_pow_le _ (norm_nonneg _) N
      _ = 2 ^ N * (‖FT μ β F y‖ + ‖y‖ ^ N * ‖FT μ β F y‖) := by ring
      _ ≤ 2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hA' ?_) (by positivity)
          calc ‖y‖ ^ N * ‖FT μ β F y‖
              ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ := by gcongr
            _ = K ^ N * ((1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖) := by ring
            _ ≤ _ := by gcongr

end PositivityTheory.jumpWindows

end
end
