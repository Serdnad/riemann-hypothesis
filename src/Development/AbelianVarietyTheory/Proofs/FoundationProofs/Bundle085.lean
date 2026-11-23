module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory

theorem norm_root_monic_le (n : ℕ) (s : Fin n → ℂ) (y : ℂ)
    (hy : y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0) : ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  apply GlobalTheory.monic_root_norm_le_one_add_sum <;> assumption

end GlobalTheory

namespace GlobalTheory

theorem quotient_integral_holomorphic : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  intro U n A D s hU hUc hA hD hs ⟨z₁, hz₁U, hz₁⟩ heq
  classical
  have hiso : ∀ z₀ ∈ U, ∀ᶠ w in 𝓝[≠] z₀, D w ≠ 0 := by
    intro z₀ hz₀
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_not] at hcon
    have := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hcon
    exact hz₁ (this hz₁U)
  have hroot : ∀ w ∈ U, D w ≠ 0 → (A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ) = 0 := by
    intro w hw hDw
    have hDn : D w ^ n ≠ 0 := pow_ne_zero _ hDw
    have key : D w ^ n * ((A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ))
        = A w ^ n + ∑ j, s j w * A w ^ (j : ℕ) * D w ^ (n - j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · rw [div_pow, mul_div_cancel₀ _ hDn]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (j : ℕ) ≤ n := j.isLt.le
        have hsplit : D w ^ n = D w ^ (j : ℕ) * D w ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hj]
        rw [hsplit, div_pow]
        field_simp
    have := heq w hw
    rw [← key] at this
    exact (mul_eq_zero.1 this).resolve_left hDn
  have hAz : ∀ w ∈ U, D w = 0 → A w = 0 := by
    intro w hw hDw
    have := heq w hw
    have hsum : ∑ j : Fin n, s j w * A w ^ (j : ℕ) * D w ^ (n - j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := j.isLt
      rw [hDw, zero_pow (by omega : n - (j : ℕ) ≠ 0), mul_zero]
    rw [hsum, add_zero] at this
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at this
    · exact (pow_eq_zero_iff hn.ne').1 this
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, ∀ z, h z =
      if D z = 0 then limUnder (𝓝[≠] z) (fun w => A w / D w) else A z / D z := ⟨_, fun z => rfl⟩
  have hdiffAt : ∀ z₀ ∈ U, DifferentiableAt ℂ h z₀ := by
    intro z₀ hz₀
    have hUn : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
    by_cases hDz : D z₀ = 0
    · have h1 : ∀ᶠ w in 𝓝 z₀, w ∈ U := hUn
      have h2 : ∀ᶠ w in 𝓝 z₀, w ≠ z₀ → D w ≠ 0 := eventually_nhdsWithin_iff.1 (hiso z₀ hz₀)
      have h3 : ∀ᶠ w in 𝓝 z₀, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := by
        rw [Filter.eventually_all]
        intro j
        have hc : ContinuousAt (fun w => ‖s j w‖) z₀ :=
          ((hs j).differentiableAt hUn).continuousAt.norm
        exact hc.eventually (Iio_mem_nhds (lt_add_one _))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
      have hsub : ∀ w ∈ Metric.ball z₀ r, w ∈ U := fun w hw => (hball w hw).1
      have hne : ∀ w ∈ Metric.ball z₀ r, w ≠ z₀ → D w ≠ 0 := fun w hw => (hball w hw).2.1
      have hsb : ∀ w ∈ Metric.ball z₀ r, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := fun w hw => (hball w hw).2.2
      have hfd : DifferentiableOn ℂ (fun w => A w / D w) (Metric.ball z₀ r \ {z₀}) := by
        intro w hw
        have hwU : U ∈ 𝓝 w := hU.mem_nhds (hsub w hw.1)
        exact ((hA.differentiableAt hwU).div (hD.differentiableAt hwU)
          (hne w hw.1 hw.2)).differentiableWithinAt
      have hbd : BddAbove (norm ∘ (fun w => A w / D w) '' (Metric.ball z₀ r \ {z₀})) := by
        refine ⟨1 + ∑ j, (‖s j z₀‖ + 1), ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have := GlobalTheory.norm_root_monic_le n (fun j => s j w) (A w / D w) (hroot w (hsub w hw.1) (hne w hw.1 hw.2))
        show ‖A w / D w‖ ≤ _
        refine this.trans ?_
        gcongr with j
        exact (hsb w hw.1 j).le
      have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds z₀ hr) hfd hbd
      have heqg : h =ᶠ[𝓝 z₀] Function.update (fun w => A w / D w) z₀
          (limUnder (𝓝[≠] z₀) (fun w => A w / D w)) := by
        filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
        by_cases hw0 : w = z₀
        · subst hw0; rw [hh, if_pos hDz, Function.update_self]
        · rw [hh, if_neg (hne w hw hw0), Function.update_of_ne hw0]
      exact (hg.differentiableAt (Metric.ball_mem_nhds z₀ hr)).congr_of_eventuallyEq heqg
    · have hDc : ContinuousAt D z₀ := (hD.differentiableAt hUn).continuousAt
      have heqf : h =ᶠ[𝓝 z₀] fun w => A w / D w := by
        filter_upwards [hDc.eventually_ne hDz] with w hw
        rw [hh, if_neg hw]
      exact ((hA.differentiableAt hUn).div (hD.differentiableAt hUn) hDz).congr_of_eventuallyEq heqf
  refine ⟨h, fun z hz => (hdiffAt z hz).differentiableWithinAt, ?_, ?_⟩
  · intro z hz
    by_cases hDz : D z = 0
    · rw [hDz, mul_zero]; exact hAz z hz hDz
    · rw [hh, if_neg hDz, div_mul_cancel₀ _ hDz]
  · intro z hz
    by_cases hDz : D z = 0
    · have hUn : U ∈ 𝓝 z := hU.mem_nhds hz
      have hFd : DifferentiableAt ℂ (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) z := by
        apply ((hdiffAt z hz).pow n).add
        have hsum := DifferentiableAt.sum (u := Finset.univ)
          (A := fun (j : Fin n) (w : ℂ) => s j w * h w ^ (j : ℕ))
          (fun j _ => ((hs j).differentiableAt hUn).mul ((hdiffAt z hz).pow _))
        convert hsum using 1
        ext w
        simp [Finset.sum_apply]
      have hev : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ j, s j w * h w ^ (j : ℕ) = 0 := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds hUn] with w hw hwU
        rw [hh, if_neg hw]
        exact hroot w hwU hw
      have ht : Tendsto (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) (𝓝[≠] z) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique (hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht
    · rw [hh, if_neg hDz]
      exact hroot z hz hDz

end GlobalTheory
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.diamondMatrix_normalizes_gammaOneGammaZeroLevel : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ → ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev | exact GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev | (intros; apply GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.limit_poly_of_periodic_slash_family_const : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → Q = C (Q.coeff 0) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.QConst.qconst | exact GlobalTheory.HeckeFamilyMatrices.QConst.qconst | (intros; apply GlobalTheory.HeckeFamilyMatrices.QConst.qconst <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedSiegelUnit_index_add_intVector : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x → sg c (fun i => x i + n i) τ = sg c x τ := by
  first | exact @GlobalTheory.Sieg.Per.sg_add_int | exact GlobalTheory.Sieg.Per.sg_add_int | (intros; apply GlobalTheory.Sieg.Per.sg_add_int <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant | exact GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant | (intros; apply GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | exact GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | (intros; apply GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.polyDegreeSlashAction_matrix_mul : ∀ (w : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) → slP w (A * B) p = slP w B (slP w A p) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul | exact GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul | (intros; apply GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedThetaQProduct_distribution_relation : ∀ (c m : ℕ) (q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) → ∏ j ∈ Finset.range m, cth c q (t * ee ((j : ℂ) / m)) = cth c (q ^ m) (t ^ m) := by
  first | exact @GlobalTheory.Sieg.prod_cth_mul_ee | exact GlobalTheory.Sieg.prod_cth_mul_ee | (intros; apply GlobalTheory.Sieg.prod_cth_mul_ee <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.PerCoc

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, lcoeff_apply,
    LinearMap.toSpanSingleton_apply]

theorem homogenize_eq_sum (w : ℕ) (p : ℂ[X]) :
    p.homogenize w = ∑ i ∈ Finset.range (w + 1),
      p.coeff i • ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ i * MvPolynomial.X 1 ^ (w - i)) := by
  rw [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← homogenize_monomial hi', ← homogenize_X_pow hi', ← homogenize_smul, smul_X_eq_monomial]

theorem polySlash_eq_aeval (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = MvPolynomial.aeval
      ![C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ), C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)]
      (p.homogenize w) := by

  rw [polySlash_apply, homogenize_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

theorem isHomogeneous_lin (a b : ℂ) :
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul b)

theorem homogenize_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).homogenize w = ∑ i ∈ Finset.range (w + 1), MvPolynomial.C (p.coeff i) *
      ((MvPolynomial.C ((g 0 0 : ℤ) : ℂ) * MvPolynomial.X 0 + MvPolynomial.C ((g 0 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ i *
        (MvPolynomial.C ((g 1 0 : ℤ) : ℂ) * MvPolynomial.X 0 +
          MvPolynomial.C ((g 1 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ (w - i)) := by
  apply homogenize_eq_of_isHomogeneous
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := (((isHomogeneous_lin ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)).pow i).mul
      ((isHomogeneous_lin ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)).pow (w - i))).C_mul (p.coeff i)
    rwa [one_mul, one_mul, Nat.add_sub_of_le hi'] at h
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [polySlash_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, ← C_eq_algebraMap, smul_eq_C_mul]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w h (slP w g p) = slP w (g * h) p := by

  rw [polySlash_eq_aeval w h, homogenize_slP, polySlash_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← C_eq_algebraMap, smul_eq_C_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul]
  congr 3 <;> ring

theorem polySlash_mem_degreeLT (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h1 : ∀ a b : ℂ, (C a * X + C b).natDegree ≤ 1 := fun a b => natDegree_linear_le
  have h2 := natDegree_mul_le_of_le (natDegree_pow_le_of_le i (h1 ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)))
    (natDegree_pow_le_of_le (w - i) (h1 ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)))
  rw [mul_one, mul_one, Nat.add_sub_of_le hi'] at h2
  exact_mod_cast Nat.lt_succ_of_le h2

theorem eichler_I (w : ℕ) (f : ℍ → ℂ) : eichler w f UpperHalfPlane.I = 0 := by
  simp [eichler]

theorem slash_eq_self {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) (γ : Γ) :
    (⇑f) ∣[k] (γ : SL(2, ℤ)) = ⇑f := by
  rw [ModularForm.SL_slash]
  exact f.slash_action_eq' _ ⟨γ, γ.2, rfl⟩

theorem per_eq (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk : 2 ≤ k) (f : ModularForm Γ (k : ℤ)) (γ : Γ) (τ : ℍ) :
    per Γ (k - 2) ⇑f γ =
      slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk ⇑f f.holo' γ
  rw [slash_eq_self] at hc
  rw [per, hc, hc, eichler_I]
  ring

theorem per_mem_Z1_and_eq_slP_eichler_sub : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ),
    per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ =
      slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  intro Γ k hk f
  refine ⟨⟨fun γ => polySlash_mem_degreeLT _ _ _, fun γ δ => ?_⟩, per_eq Γ k hk f⟩
  rw [per_eq Γ k hk f γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I), map_sub, polySlash_polySlash]
  simp only [per, mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_smul]
  ring

end GlobalTheory.HeckeFamilyMatrices.PerCoc
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerIntegral_changeOfVariables_intMatrix_slash : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ (β : Matrix (Fin 2) (Fin 2) ℤ), 0 < β.det → ∀ τ : ℍ, slP (k - 2) β (eichler (k - 2) f (toGL β • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] toGL β) τ + slP (k - 2) β (eichler (k - 2) f (toGL β • UpperHalfPlane.I)) := by
  first | exact @GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul | exact GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul | (intros; apply GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c → (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) → ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.eichler_tail | exact GlobalTheory.HeckeFamilyMatrices.eichler_tail | (intros; apply GlobalTheory.HeckeFamilyMatrices.eichler_tail <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.hasFDerivAt_eichler_sub_conj_wirtinger : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  first | exact @GlobalTheory.EichlerDbar.wirtinger_eichler | exact GlobalTheory.EichlerDbar.wirtinger_eichler | (intros; apply GlobalTheory.EichlerDbar.wirtinger_eichler <;> assumption)
end
