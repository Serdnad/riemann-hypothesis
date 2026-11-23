module

public import Formalism.LandauZeroFreeBounds.Bundle001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle006
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle007
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle008
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle001
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle005
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle003
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma real_character_lfunction_im_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (σ : ℝ) : (DirichletCharacter.LFunction χ σ).im = 0 := by
  have h := realCharConj q χ hχ hχ1 (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.1 h.symm

lemma lfunction_tendsto_one_atTop {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun x : ℝ ↦ DirichletCharacter.LFunction χ x) atTop (𝓝 1) := by
  have ha : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne q) χ]
    exact EReal.coe_lt_top 1
  have ht := LSeries.tendsto_atTop ha
  simp only [Nat.cast_one, map_one] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hx)).symm

theorem real_lfunction_real_on_reals : LRealPos := by
  intro q _ χ hχ hχ1 σ₀ hnz σ hσ
  have him : ∀ t : ℝ, (DirichletCharacter.LFunction χ t).im = 0 := real_character_lfunction_im_eq_zero χ hχ hχ1
  refine ⟨him σ, ?_⟩
  by_contra hneg
  rw [not_lt] at hneg
  have hcont : Continuous fun t : ℝ => (DirichletCharacter.LFunction χ t).re :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp Complex.continuous_ofReal)
  obtain ⟨x, hx1, hx⟩ : ∃ x : ℝ, σ ≤ x ∧ 0 < (DirichletCharacter.LFunction χ x).re := by
    have hev : ∀ᶠ x : ℝ in atTop, 0 < (DirichletCharacter.LFunction χ x).re :=
      ((Complex.continuous_re.tendsto 1).comp (lfunction_tendsto_one_atTop χ)).eventually
        (lt_mem_nhds (by norm_num))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop σ)).exists
    exact ⟨x, hx.2, hx.1⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx1 hcont.continuousOn ⟨hneg, hx.le⟩
  apply hnz c (le_trans hσ hc.1)
  exact Complex.ext (by simpa using hc0) (by simpa using him c)

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem siegel_theorem_of : SiegelOf := by
  intro hP hR hB hL1 hZ hLP hS ε hε
  obtain ⟨C, K, hK0, hKey⟩ := hB
  obtain ⟨CL, hL⟩ := hL1
  set σ₀ : ℝ := max (7 / 8) (1 - ε / (2 * (K + 1))) with hσ₀
  have hK1 : 0 < K + 1 := by linarith
  have h78 : 7 / 8 ≤ σ₀ := le_max_left _ _
  have hσ₀1 : σ₀ < 1 := by
    apply max_lt (by norm_num)
    have : 0 < ε / (2 * (K + 1)) := by positivity
    linarith
  have hKa : ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → K * (1 - σ) ≤ ε / 2 := by
    intro σ hσ hσ1
    have h1 : 1 - ε / (2 * (K + 1)) ≤ σ := le_trans (le_max_right _ _) hσ
    have h2 : 1 - σ ≤ ε / (2 * (K + 1)) := by linarith
    have h3 : 0 ≤ 1 - σ := by linarith
    have h4 : (K + 1) * (ε / (2 * (K + 1))) = ε / 2 := by
      field_simp
    calc K * (1 - σ) ≤ (K + 1) * (1 - σ) := by nlinarith
      _ ≤ (K + 1) * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h2 hK1.le
      _ = ε / 2 := h4
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ σ₀ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ₁ β = 0
  ·
    obtain ⟨q₁, hq₁, χ₁, β, h1sq, h1ne, hβ0, hβ1, hzero⟩ := hex
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne (le_trans h78 hβ0) hβ1
      (hKa β hβ0 hβ1) ?_
    intro q _ χ ψ _ _ _ _
    simp [Fbq, hzero]
  ·
    push_neg at hex
    obtain ⟨q₁, hq₁, χ₁, h1sq, h1ne⟩ := hR
    have hnz : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        ∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0 := by
      intro q _ χ hsq hne σ hσ
      rcases lt_or_ge σ 1 with h | h
      · exact hex q inferInstance χ σ hsq hne hσ h
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using h)
    have hpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        (DirichletCharacter.LFunction χ σ₀).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ₀).re := by
      intro q _ χ hsq hne
      exact hLP q χ hsq hne σ₀ (hnz q χ hsq hne) σ₀ le_rfl
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne h78 hσ₀1 (hKa σ₀ le_rfl hσ₀1) ?_
    intro q _ χ ψ hsq hne hψne hψ
    have hψsq := product_real_characters_sq_eq_one χ₁ χ ψ h1sq hsq hψ
    obtain ⟨hz_im, hz_re⟩ := hZ σ₀ (by linarith) hσ₀1
    obtain ⟨a_im, a_re⟩ := hpos q₁ χ₁ h1sq h1ne
    obtain ⟨b_im, b_re⟩ := hpos q χ hsq hne
    obtain ⟨c_im, c_re⟩ := hpos (q₁ * q) ψ hψsq hψne
    have hre : (Fbq χ₁ χ ψ σ₀).re = (riemannZeta σ₀).re * (DirichletCharacter.LFunction χ₁ σ₀).re *
        (DirichletCharacter.LFunction χ σ₀).re * (DirichletCharacter.LFunction ψ σ₀).re := by
      simp [Fbq, Complex.mul_re, Complex.mul_im, hz_im, a_im, b_im, c_im]
    rw [hre]
    have hp := mul_pos (mul_pos a_re b_re) c_re
    have hn := mul_neg_of_neg_of_pos hz_re hp
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma circle_about_two_geometry {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) :
    1 / 2 ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ 1 / 2 ≤ ‖s - 1‖ := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Complex.abs_re_le_norm (s - 2)
    rw [hs] at h
    have e : (s - 2).re = s.re - 2 := by simp
    rw [e] at h
    linarith [(abs_le.mp h).1]
  · have h := norm_add_le (s - 2) (2 : ℂ)
    rw [sub_add_cancel, hs] at h
    have e : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  · have h := norm_add_le (s - 1) (-1 : ℂ)
    have e : s - 1 + -1 = s - 2 := by ring
    rw [e, hs] at h
    have e1 : ‖(-1 : ℂ)‖ = 1 := by simp
    linarith

lemma zeta_norm_le_on_circle {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) : ‖riemannZeta s‖ ≤ 14 := by
  obtain ⟨hre, hn, h1⟩ := circle_about_two_geometry hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    norm_num at h1
  have hg := Formalism.ZF.growthBound s (by linarith) hs1
  have ha : 1 / ‖s - 1‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hb : 1 / s.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hp : 0 ≤ 1 + 1 / s.re := by
    have : 0 < 1 / s.re := by apply div_pos <;> linarith
    linarith
  have hc : ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * 3 := by
    calc ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * (1 + 1 / s.re) := mul_le_mul_of_nonneg_right hn hp
      _ ≤ 7 / 2 * 3 := by linarith
  linarith

theorem product_lfunction_growth_bound : BqGrowth := by
  obtain ⟨C, hC⟩ := lfunction_polynomial_growth
  refine ⟨14 * (9 / 2 * |C|) ^ 3, 3, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h3 s hs
  obtain ⟨hre, hn, -⟩ := circle_about_two_geometry hs
  have hz := zeta_norm_le_on_circle hs
  have L : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ 9 / 2 * |C| * q := by
    intro q _ χ hχ
    have h := hC q χ hχ s hre
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hCq : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq
    have hp : 0 ≤ |C| * q := by positivity
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖) := h
      _ ≤ |C| * q * (1 + ‖s‖) := mul_le_mul_of_nonneg_right hCq (by positivity)
      _ ≤ |C| * q * (9 / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
      _ = 9 / 2 * |C| * q := by ring
  have e1 := L q₁ χ₁ h1
  have e2 := L q₂ χ₂ h2
  have e3 := L (q₁ * q₂) ψ h3
  have hq1 : (q₁ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right q₁ (Nat.pos_of_ne_zero (NeZero.ne q₂))
  have hq2 : (q₂ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left q₂ (Nat.pos_of_ne_zero (NeZero.ne q₁))
  have ha : 0 ≤ 9 / 2 * |C| := by positivity
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold Fbq
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ₁ s‖ * ‖DirichletCharacter.LFunction χ₂ s‖ *
        ‖DirichletCharacter.LFunction ψ s‖
      ≤ 14 * (9 / 2 * |C| * q₁) * (9 / 2 * |C| * q₂) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by
        gcongr
    _ ≤ 14 * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) *
          (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by gcongr
    _ = 14 * (9 / 2 * |C|) ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 3 := by ring

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_term_twist_moebius_le {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  apply LSeries.norm_term_le
  simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_one₀ h1 (norm_nonneg _) h2

open Formalism.ZF.MoebiusInverseZetaBounds in
theorem inverseBound : LInvBound := by
  intro q _ χ s hs
  have hσ1 : 0 < s.re - 1 := by linarith
  have hshift : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) ≤ s.re / (s.re - 1) := by
    apply Real.tsum_le_of_sum_range_le
    · intro n
      positivity
    · intro m
      rcases m with _ | k
      · simp only [Finset.range_zero, Finset.sum_empty]
        positivity
      · rw [Finset.sum_range_succ']
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hanti : AntitoneOn (fun x : ℝ => x ^ (-s.re)) (Set.Icc (1 : ℝ) (1 + k)) := by
          intro x hx y _ hxy
          exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
        have hsum := hanti.sum_le_integral
        have hint : ∫ x in (1 : ℝ)..(1 + k), x ^ (-s.re) =
            ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) := by
          apply integral_rpow
          refine Or.inr ⟨by linarith, ?_⟩
          rw [Set.uIcc_of_le (by linarith)]
          intro h
          linarith [h.1]
        have hpos : 0 ≤ (1 + k : ℝ) ^ (-s.re + 1) := by positivity
        have hb : ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) ≤ 1 / (s.re - 1) := by
          rw [Real.one_rpow, show -s.re + 1 = -(s.re - 1) by ring, div_neg, ← neg_div]
          have hpos' : 0 ≤ (1 + k : ℝ) ^ (-(s.re - 1)) := by positivity
          gcongr
          linarith
        have e : ∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) =
            ∑ i ∈ Finset.range k, (fun x : ℝ => x ^ (-s.re)) (1 + ((i + 1 : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun i _ => by
            show (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-s.re)
            congr 1 <;> ring
        rw [e]
        have e2 : s.re / (s.re - 1) = 1 / (s.re - 1) + 1 := by
          field_simp
          ring
        simp only [Nat.cast_zero, zero_add, Real.one_rpow]
        rw [hint] at hsum
        linarith
  have hp : -(s.re - 1) - 1 < -1 := by linarith
  have hfun : (fun n : ℕ => ‖term (1 : ℕ → ℂ) s (n + 1)‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) :=
    funext (norm_term_one_succ s)
  have hS1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1, hfun]
    exact summable_shift hp
  have hT1 : ∑' n, ‖term (1 : ℕ → ℂ) s n‖ ≤ s.re / (s.re - 1) := by
    rw [hS1.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add, hfun]
    exact hshift
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hinv : ‖LSeries ↗χ s‖⁻¹ = ‖LSeries (↗χ * ↗μ) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
  rw [hinv]
  have hS2 : Summable fun n => ‖term (↗χ * ↗μ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_term_twist_moebius_le χ s n) hS1
  calc ‖LSeries (↗χ * ↗μ) s‖ = ‖∑' n, term (↗χ * ↗μ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗μ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ :=
      Summable.tsum_le_tsum (fun n => norm_term_twist_moebius_le χ s n) hS2 hS1
    _ ≤ s.re / (s.re - 1) := hT1

lemma negLD_eq_LSeries_mul_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries ↗χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [negLD, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div]

lemma norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  have hSΛ : Summable fun n => ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  have hle : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
    intro n
    calc ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ s n‖ := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ‖term ↗Λ (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
  have hS2 : Summable fun n => ‖term (↗χ * ↗Λ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSΛ
  calc ‖L (↗χ * ↗Λ) s‖ = ‖∑' n, term (↗χ * ↗Λ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := Summable.tsum_le_tsum hle hS2 hSΛ
    _ = Formalism.ZF.lamF s.re := rfl

theorem l_log_deriv_right : LLogDerivRight := by
  obtain ⟨C, hC0, hC⟩ := Formalism.ZF.logDerivBoundRightHalfPlane
  refine ⟨C, hC0, ?_⟩
  intro q _ χ s hs
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs]
  refine le_trans (norm_LSeries_twist_vonMangoldt_le χ hs) ?_
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  rw [Formalism.ZF.lamF_eq_norm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, norm_neg]
  have h := hC (s.re : ℂ) hre
  simpa using h

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem exists_contour_avoiding_real_zero (B : Finset ℝ) (hB : B.card ≤ 1) (L c₁ : ℝ) (hL : 0 < L) (hc₁ : 0 < c₁) :
    ∃ σ₁ : ℝ, (σ₁ = 1 - c₁ / (3 * L) ∨ σ₁ = 1 - c₁ / (4 * L)) ∧
      ∀ β ∈ B, c₁ / (24 * L) ≤ |σ₁ - β| := by
  have hab : (1 - c₁ / (3 * L)) - (1 - c₁ / (4 * L)) = -(2 * (c₁ / (24 * L))) := by
    field_simp
    ring
  have he : 0 < c₁ / (24 * L) := by positivity
  rcases Finset.eq_empty_or_nonempty B with hB0 | ⟨β, hβ⟩
  · exact ⟨_, Or.inl rfl, fun β hβ => by simp [hB0] at hβ⟩
  have hBs : ∀ β' ∈ B, β' = β := fun β' hβ' => Finset.card_le_one.mp hB β' hβ' β hβ
  by_cases h : c₁ / (24 * L) ≤ |(1 - c₁ / (3 * L)) - β|
  · exact ⟨_, Or.inl rfl, fun β' hβ' => by rw [hBs β' hβ']; exact h⟩
  · refine ⟨_, Or.inr rfl, fun β' hβ' => ?_⟩
    rw [hBs β' hβ']
    push_neg at h
    have tri := abs_sub_le (1 - c₁ / (3 * L)) β (1 - c₁ / (4 * L))
    rw [hab, abs_neg, abs_of_pos (by positivity), abs_sub_comm β] at tri
    linarith

theorem perron_contour_decomposition (hP : PerronChi) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y σ₁ σ₀ T : ℝ) (R : ℂ) (hy : 1 ≤ y) (hσ₀ : 1 < σ₀) (hT : 0 ≤ T)
    (hrect : Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T) T = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Schi χ y - R‖ ≤
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I)‖
      + ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ := by
  obtain ⟨hint, hS⟩ := hP q χ y hy σ₀ hσ₀
  have hsplit := integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint
  have hIoc : ∫ t in Set.Ioc (-T) T, Fchi χ y ((σ₀ : ℂ) + t * I) =
      ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  unfold Formalism.ZF.rectInt at hrect
  set Cp := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I) with hCp
  set Bt := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt
  set Tp := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I) with hTp
  set Lf := ∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I) with hLf
  set Rt := ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) with hRt
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hinv : (2 * (Real.pi : ℂ)) * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hI : I * I = -1 := Complex.I_mul_I
  have key : (2 * (Real.pi : ℂ)) * (Schi χ y - R) = Cp + I * (Bt - Tp) + Lf := by
    rw [hS, ← hsplit, hIoc]
    linear_combination (-I) * hrect + (Rt + Cp) * hinv + (Rt - Lf - 2 * Real.pi * R) * hI
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hsub := norm_sub_le Bt Tp
  calc 2 * Real.pi * ‖Schi χ y - R‖ = ‖(2 * (Real.pi : ℂ)) * (Schi χ y - R)‖ := by
        rw [norm_mul, hn]
    _ = ‖Cp + I * (Bt - Tp) + Lf‖ := by rw [key]
    _ ≤ ‖Cp‖ + ‖I * (Bt - Tp)‖ + ‖Lf‖ := norm_add₃_le
    _ ≤ ‖Cp‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith

end Formalism.ZeroFreeDirichlet
end
end
