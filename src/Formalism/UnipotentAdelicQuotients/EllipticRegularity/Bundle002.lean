module

public import Formalism.UnipotentAdelicQuotients.Bundle003
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

lemma eF_eq_exp {d : ℕ} (ξ : E d) : eF ξ = fun y => Complex.exp (eL ξ y) := by
  funext y
  simp only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]
  ring_nf

lemma hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp

lemma eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by
  simp only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]
  simp

theorem iteratedPartialFourierChar : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma norm_fourier_le_integral_norm {d : ℕ} (g : E d → ℂ) (ξ : E d) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem sobolevOfCompactSupport : BaseLevel := by
  intro d g hg hgs
  unfold Hs nrm
  have hint : MeasureTheory.Integrable g := hg.integrable_of_hasCompactSupport hgs
  set B : ℝ := ∫ x, ‖g x‖ with hB
  have hBnn : 0 ≤ B := MeasureTheory.integral_nonneg fun x => norm_nonneg _
  have hI : MeasureTheory.Integrable
      (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    have : (Module.finrank ℝ (E d) : ℝ) = d := by simp
    rw [this]
    linarith
  have hI2 := (hI.const_mul (B ^ 2)).hasFiniteIntegral
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun ξ => ?_) hI2
  have ha : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hom : om (-(d : ℝ) - 1) 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2) := by simp [om]
  have hsq : ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have h1 : ‖𝓕 g ξ‖ₑ ≤ ENNReal.ofReal B := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (norm_fourier_le_integral_norm g ξ)
  have h2 : ‖B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)‖ₑ =
      ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
  rw [h2, hom]
  calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ENNReal.ofReal B ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hBnn,
          ← ENNReal.ofReal_mul (by positivity), hsq, mul_comm]

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem moments_integrable_of_nrm {d : ℕ} (F : E d → ℂ) (hF : Continuous F)
    (h : ∀ s : ℕ, nrm (s : ℝ) 0 0 F < ⊤) (n : ℕ) :
    Integrable (fun v : E d => ‖v‖ ^ n * ‖F v‖) := by
  set m : ℕ := n + (d + 1) with hm
  let A : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ m * ‖F v‖ ^ 2
  let B : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)
  have hAm : Continuous A := by
    have : Continuous fun v : E d => (1 + ‖v‖ ^ 2) := by fun_prop
    exact (this.pow m).mul ((continuous_norm.comp hF).pow 2)
  have hA : Integrable A := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    have hs := h m
    unfold nrm om at hs
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (lintegral_mono fun v => le_of_eq ?_) hs
    have ht0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [A]
    congr 1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero,
      Real.rpow_zero, mul_one]
    rw [← Real.rpow_natCast ((1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)), ← Real.rpow_mul ht0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hB : Integrable B := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  refine (hA.add hB).mono' ((continuous_norm.pow n).mul (continuous_norm.comp hF)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  have ht1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have ht0 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by linarith
  have hBv : B v = ((1 + ‖v‖ ^ 2) ^ (d + 1))⁻¹ := by
    simp only [B]
    rw [show -(2 * ((d : ℝ) + 1)) / 2 = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg ht0.le,
      Real.rpow_natCast]
  have hAB : A v * B v = (1 + ‖v‖ ^ 2) ^ n * ‖F v‖ ^ 2 := by
    rw [hBv]
    simp only [A, hm, pow_add]
    field_simp
  have hx : (‖v‖ ^ n * ‖F v‖) ^ 2 ≤ A v * B v := by
    rw [hAB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    gcongr
    linarith
  have hA0 : 0 ≤ A v := by positivity
  have hB0 : 0 ≤ B v := by simp only [B]; positivity
  have hx0 : 0 ≤ ‖v‖ ^ n * ‖F v‖ := by positivity
  rw [Real.norm_of_nonneg hx0]
  show ‖v‖ ^ n * ‖F v‖ ≤ A v + B v
  nlinarith [sq_nonneg (A v - B v), mul_nonneg hA0 hB0]

theorem smoothOfSobolevAll : MomentsSmooth := by
  intro d g hg hgc hs
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hFc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ (E d)) Real.continuous_fourierChar
      (by simpa using continuous_inner) hgi
  have hmom := moments_integrable_of_nrm (𝓕 g) hFc hs
  have hFi : Integrable (𝓕 g) := by
    have h0 := hmom 0
    simp only [pow_zero, one_mul] at h0
    exact (integrable_norm_iff hFc.aestronglyMeasurable).mp h0
  have hinv := hg.fourierInv_fourier_eq hgi hFi
  have hsm : ContDiff ℝ ∞ (𝓕 (𝓕 g)) :=
    VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) (μ := volume) (N := ⊤) (f := 𝓕 g)
      (fun n _ => hmom n)
  have hg' : g = fun w => 𝓕 (𝓕 g) (-w) := by
    conv_lhs => rw [← hinv]
    ext w
    exact Real.fourierInv_eq_fourier_neg _ w
  rw [hg']
  exact hsm.comp contDiff_neg

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem integralFourierChar : FourierPair := by
  intro d g _ _ ξ
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y
  rw [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 1
  simp only [eF]
  congr 1
  push_cast
  ring

theorem existsBump : Bump := by
  intro d x0 r hr
  let f : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball (show r / 2 < r by linarith)
  · filter_upwards [ball_mem_nhds x0 (show (0 : ℝ) < r / 4 by positivity)] with y hy
    exact f.one_of_mem_closedBall (ball_subset_closedBall hy)

theorem cutoffContinuous : CutCont := by
  intro d U u χ hU hu hχs hχc hχt
  have hχ' : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχs.continuous
  have hsub : tsupport (cut χ u) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    by_contra h0
    apply hx
    have h0' : χ x = 0 := by simpa using h0
    simp [cut, h0']
  have hcont : ContinuousOn (cut χ u) U := hχ'.continuousOn.mul hu
  exact ⟨hcont.continuous_of_tsupport_subset hU (hsub.trans hχt),
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub⟩

theorem smoothOfLocallySmooth : LocalGlobal := by
  intro d U f _ h x hx
  obtain ⟨χ, hχ1, hχf⟩ := h x hx
  have heq : cut χ f =ᶠ[𝓝 x] f := by
    filter_upwards [hχ1] with y hy
    simp [cut, hy]
  exact (hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma dw_eventuallyEq {d : ℕ} (w : List (Fin d)) {f f' : E d → ℂ} {y : E d} (h : f =ᶠ[𝓝 y] f') :
    dw w f =ᶠ[𝓝 y] dw w f' := by
  induction w with
  | nil => simpa [dw] using h
  | cons j w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with x hx
    show fderiv ℝ (dw w f) x (ev j) = fderiv ℝ (dw w f') x (ev j)
    rw [hx]

theorem adjointPairingLocal : PairingLocal := by
  intro d m b b' g φ V hV hg hb
  congr 1
  funext y
  by_cases hy : y ∈ V
  · congr 1
    unfold trOp
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
    congr 1

    have hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [hb n w z hz]
    exact (dw_eventuallyEq _ hev).eq_of_nhds
  · have hg0 : g y = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))
    rw [hg0, zero_mul, zero_mul]

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

private theorem symb_smul_covector_eq_pow_ord_mul {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x ξ : E d) (t : ℝ) :
    P.symb i x (t • ξ) = (t : ℂ) ^ (P.ord i) * P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ l, (((t • ξ) (w l) : ℝ) : ℂ) = (t : ℂ) * ((ξ (w l) : ℝ) : ℂ) := fun l => by simp
  simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem continuous_symb_covector {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x : E d) : Continuous fun ξ : E d => P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  fun_prop

theorem symbolLowerBound : SymbLower := by
  intro d ι _ P x0 k hk hell
  obtain ⟨f, hf⟩ : ∃ f : E d → ℝ,
      f = fun ξ => ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := ⟨_, rfl⟩
  have hfξ : ∀ ξ, f ξ = ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := by
    intro ξ; rw [hf]
  have hcont : Continuous f := by
    rw [hf]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_norm.pow _).mul
      ((continuous_symb_covector P i x0).norm.pow 2)
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ ξ : E d, f (t • ξ) = t ^ (2 * k) * f ξ := by
    intro t ht ξ
    rw [hfξ, hfξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
    have h2 : ‖(t : ℂ) ^ (P.ord i) * P.symb i x0 ξ‖
        = t ^ (P.ord i) * ‖P.symb i x0 ξ‖ := by
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht]
    rw [symb_smul_covector_eq_pow_ord_mul, h1, h2]
    have hk' : 2 * k = 2 * (k - P.ord i) + 2 * P.ord i := by have := hk i; omega
    rw [hk', pow_add]
    ring
  rcases (sphere (0 : E d) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun ξ hξ => ?_⟩
    exfalso
    have hmem : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
    rw [hS] at hmem
    exact hmem
  · obtain ⟨η0, hη0S, hmin⟩ := (isCompact_sphere (0 : E d) 1).exists_isMinOn hS hcont.continuousOn
    have hη0n : ‖η0‖ = 1 := mem_sphere_zero_iff_norm.mp hη0S
    have hne : η0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hη0n
      exact zero_ne_one hη0n
    obtain ⟨i, hi⟩ := hell η0 hne
    have hpos : 0 < f η0 := by
      have hle : ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 ≤ f η0 := by
        rw [hfξ]
        exact Finset.single_le_sum
          (f := fun j => ‖η0‖ ^ (2 * (k - P.ord j)) * ‖P.symb j x0 η0‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ i)
      have hlt : 0 < ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 := by
        rw [hη0n, one_pow, one_mul]
        exact pow_pos (norm_pos_iff.mpr hi) 2
      linarith
    refine ⟨f η0, hpos, fun ξ hξ => ?_⟩
    have ht : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hηS : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
    have hξη : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hle : f η0 ≤ f (‖ξ‖⁻¹ • ξ) := hmin hηS
    have hfx : f ξ = ‖ξ‖ ^ (2 * k) * f (‖ξ‖⁻¹ • ξ) := by
      conv_lhs => rw [hξη]
      exact hhom _ ht.le _
    rw [← hfξ, hfx, mul_comm]
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end ZetaZeros.D.EllReg
end
