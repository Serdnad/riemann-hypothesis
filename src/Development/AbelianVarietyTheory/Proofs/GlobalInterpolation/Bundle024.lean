module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle002
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle018
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle019
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.SumPrimeReciprocals
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.Convergence

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.LAtZero

theorem norm_limit_le (F h e : ℂ → ℂ) (P : ℂ → Prop) (Z : Finset ℂ) (m : ℂ → ℕ) (B : ℝ)
    (hh : ContinuousAt h 0) (he : ContinuousAt e 0) (h0 : 0 ∉ Z → m 0 = 0)
    (hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), P s ∧ F s = (m 0 : ℂ) / s + h s)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → P s → ‖F s + e s - ∑ w ∈ Z, (m w : ℂ) / (s - w)‖ ≤ B) :
    ‖h 0 + e 0 - ∑ w ∈ Z.erase 0, (m w : ℂ) / (0 - w)‖ ≤ B := by
  have hc : ContinuousAt (fun s : ℂ => ‖h s + e s - ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w)‖) 0 := by
    refine ((hh.add he).sub ?_).norm
    refine tendsto_finsetSum _ fun w hw => ?_
    refine ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) ?_
    simpa using Finset.ne_of_mem_erase hw
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using (ne_of_gt hs)
  refine le_of_tendsto (hc.tendsto.comp (ht.mono_right nhdsWithin_le_nhds)) ?_
  filter_upwards [ht.eventually hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs hs1
  have h1 := hloc s hs1.1 hs1.2 hs.1
  have h2 : ∑ w ∈ Z, (m w : ℂ) / (s - w) =
      (m 0 : ℂ) / s + ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w) := by
    by_cases hz : (0 : ℂ) ∈ Z
    · rw [← Finset.add_sum_erase _ _ hz, sub_zero]
    · rw [h0 hz, Finset.erase_eq_of_notMem hz]; simp
  rw [hs.2, h2] at h1
  refine le_trans (le_of_eq ?_) h1
  simp only [Function.comp]
  congr 1
  ring

theorem exists_regular_part (f e : ℂ → ℂ) (S : Set ℂ) (B : ℝ) (hS : S.Finite)
    (he : ContinuousAt e 0) (han : AnalyticAt ℂ f 0) (hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = 0)
    (hS0 : f 0 = 0 → 0 ∈ S) (hSz : ∀ w ∈ S, f w = 0)
    (hT : ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| < 1 → f w = 0 → w ∈ S)
    (hbig : ∀ w ∈ S, w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖)
    (hcount : ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℝ) ≤ B)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → f s ≠ 0 →
      ‖deriv f s / f s + e s - ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℂ) / (s - w)‖ ≤ B) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv f s / f s = (analyticOrderNatAt f 0 : ℂ) / s + h s) ∧
      ‖h 0‖ ≤ 2 * B + ‖e 0‖ +
        ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0},
          ((analyticOrderNatAt f ρ : ℕ) : ℝ) / ‖ρ‖ := by
  classical
  obtain ⟨h, hh, hev⟩ := GlobalTheory.logDeriv_eq_order_div_add_analytic f 0 han hne
  simp only [sub_zero] at hev
  refine ⟨h, hh, hev.mono fun s hs => hs.2, ?_⟩
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS] at hcount hloc
  have key := norm_limit_le (fun s => deriv f s / f s) h e (fun s => f s ≠ 0) hS.toFinset
    (analyticOrderNatAt f) B hh.continuousAt he ?_ hev hloc
  swap
  · intro hz
    have : f 0 ≠ 0 := fun h0 => hz (by simpa using hS0 h0)
    rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr this]; rfl
  have hset : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0} =
      ↑(hS.toFinset.filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨hT w a b c d, a, b, c⟩,
      fun ⟨d, a, b, c⟩ => ⟨a, b, c, hSz w d⟩⟩
  rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hsum : ‖∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)‖ ≤
      ∑ w ∈ hS.toFinset, ((analyticOrderNatAt f w : ℝ) +
        if 0 < w.re ∧ w.re < 1 ∧ |w.im| < 1 then (analyticOrderNatAt f w : ℝ) / ‖w‖ else 0) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 _) fun w _ _ => ?_)
    · rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
      split_ifs with hc
      · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      · rw [add_zero]
        refine div_le_self (Nat.cast_nonneg _) ?_
        rcases le_or_gt w.re 0 with h1 | h1
        · exact hbig w (by simpa using Finset.mem_of_mem_erase hw) h1 (Finset.ne_of_mem_erase hw)
        rcases le_or_gt 1 w.re with h2 | h2
        · exact h2.trans (re_le_norm w)
        · have h3 : 1 ≤ |w.im| := not_lt.mp fun h3 => hc ⟨h1, h2, h3⟩
          exact h3.trans (abs_im_le_norm w)
    · split_ifs <;> positivity
  rw [Finset.sum_add_distrib] at hsum
  set X := ∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)
  have : ‖h 0‖ ≤ ‖h 0 + e 0 - X‖ + ‖e 0‖ + ‖X‖ := by
    calc ‖h 0‖ = ‖(h 0 + e 0 - X) - e 0 + X‖ := by congr 1; ring
      _ ≤ ‖(h 0 + e 0 - X) - e 0‖ + ‖X‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  linarith

theorem norm_sub_two_le {w : ℂ} (h1 : 0 ≤ w.re) (h2 : w.re < 1) (h3 : |w.im| < 1) :
    ‖w - 2‖ ≤ 7 / 2 := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  have : |w.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [sub_re, sub_im, re_ofNat, im_ofNat, sub_zero]
  linarith

theorem logDeriv_LFunction_near_zero : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∃ (m : ℕ) (h : ℂ → ℂ), m ≤ 1 ∧ AnalyticAt ℂ h 0 ∧ (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (LFunction χ) s / LFunction χ s = (m : ℂ) / s + h s) ∧ ‖h 0‖ ≤ C * (Real.log (2 * N) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.ZetaWide.main
  refine ⟨2 * C₁ + 2 * C₂ + 2, by positivity, fun N _ χ hχ => ?_⟩
  have han : AnalyticAt ℂ (LFunction χ) 0 := by
    refine DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt) ?_
    exact isOpen_compl_singleton.mem_nhds (by simp)
  have hord : ∀ hL : LFunction χ 0 = 0, analyticOrderNatAt (LFunction χ) 0 = 1 := fun hL =>
    (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ 0 (by simp) hL).2.1
  have hm : analyticOrderNatAt (LFunction χ) 0 ≤ 1 := by
    by_cases hL : LFunction χ 0 = 0
    · exact (hord hL).le
    · rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hL]; simp
  have hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), LFunction χ s = 0 := by
    intro hz
    have h1 := hord hz.self_of_nhds
    rw [analyticOrderNatAt, analyticOrderAt_eq_top.mpr hz] at h1
    simp at h1
  have hbig : ∀ w : ℂ, LFunction χ w = 0 → w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖ := by
    intro w hw hre h0
    obtain ⟨n, rfl⟩ := (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw).1
    rw [norm_neg, Complex.norm_natCast]
    have : n ≠ 0 := by rintro rfl; simp at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hL2 : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by simp)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog : 1 / 2 ≤ Real.log (2 * N) := by
    have h1 : Real.log 2 ≤ Real.log (2 * N) := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hnn : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  by_cases h1 : χ = 1
  · have hq : N = 1 := by
      rw [IsPrimitive, h1, conductor_one] at hχ
      exact hχ.symm
    subst hq
    have hf : LFunction χ = riemannZeta := LFunction_modOne_eq
    rw [hf] at han hm hne hbig hL2 hnn ⊢
    have A := H₂ 2 (by norm_num) (by simp) (by norm_num) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part riemannZeta (fun s => 1 / (s - 1)) _
      (C₂ * Real.log 2) A.1
      (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) (by simp))
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), by simp, h⟩)
      (fun w hw => hw.2.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, by rintro rfl; simp at b, d⟩)
      (fun w hw => hbig w hw.2.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₂ s (by simp; linarith) (by simp; linarith)
          (by exact_mod_cast hs1.ne) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    simp only [Nat.cast_one, mul_one] at hlog ⊢
    have e1 : ‖(1 : ℂ) / (0 - 1)‖ = 1 := by simp
    rw [e1]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]
  · have A := H₁ N χ h1 2 (by norm_num) (by simp) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part (LFunction χ) (fun _ => 0) _
      (C₁ * Real.log (N * 2)) A.1 continuousAt_const
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), h⟩)
      (fun w hw => hw.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, d⟩)
      (fun w hw => hbig w hw.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₁ N χ h1 s (by simp; linarith) (by simp; linarith) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    rw [norm_zero, mul_comm (N : ℝ) 2]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]

end GlobalTheory.LAtZero
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

theorem _root_.GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.LLocal.logDeriv_LFunction_local | exact GlobalTheory.LLocal.logDeriv_LFunction_local | (intros; apply GlobalTheory.LLocal.logDeriv_LFunction_local <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

theorem _root_.GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  first | exact @GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | exact GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | (intros; apply GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.NonPrimeVonMangoldt


open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma log_div_pow_add_two_rpow_three_quarters_le (P : ℝ) (hP : 2 ≤ P) (k : ℕ) :
    Real.log P / (P ^ (k + 2)) ^ (3 / 4 : ℝ) ≤
      4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  have hP0 : 0 < P := by linarith
  have hA : 0 < P ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hP0 _
  have hC : 0 < ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k := by positivity
  have hCB : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k ≤ (P ^ (3 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hP (by norm_num)) k
  have hsplit : (P ^ (k + 2)) ^ (3 / 4 : ℝ) = P ^ (3 / 2 : ℝ) * (P ^ (3 / 4 : ℝ)) ^ k := by
    rw [← Real.rpow_pow_comm hP0.le, pow_add, mul_comm, ← Real.rpow_natCast (P ^ (3 / 4 : ℝ)) 2,
      ← Real.rpow_mul hP0.le]
    norm_num
  have hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show P ^ (1 / 4 : ℝ) / (1 / 4) = 4 * P ^ (1 / 4 : ℝ) by ring]
  have hrhs : 4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k
      = 4 * P ^ (1 / 4 : ℝ) / (P ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k) := by
    rw [show (-(5 / 4 : ℝ)) = 1 / 4 - 3 / 2 by norm_num, Real.rpow_sub hP0,
      Real.rpow_neg (by norm_num), inv_pow]
    field_simp
  rw [hsplit, hrhs]
  exact div_le_div₀ (by positivity) hlog (mul_pos hA hC) (mul_le_mul_of_nonneg_left hCB hA.le)


open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
theorem _root_.GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  set F := (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) with hF
  set g : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 2) with hg_def
  have hg : Function.Injective g := by
    rintro ⟨p, k⟩ ⟨q, m⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 (h : (p : ℕ) ^ ((k + 1) + 1) = (q : ℕ) ^ ((m + 1) + 1))
    exact Prod.ext (Subtype.ext h1) (by simpa using h2)
  have hrange : ∀ n ∉ Set.range g, F n = 0 := by
    intro n hn
    by_cases hp : n.Prime
    · simp [hF, hp]
    by_cases hΛ : Λ n = 0
    · simp [hF, hΛ]
    exfalso
    apply hn
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k = 1 := by omega
      subst this
      exact hp (by simpa using hp')
    exact ⟨(⟨p, hp'⟩, k - 2), by simp only [hg_def]; congr 1; omega⟩
  rw [← hg.summable_iff hrange]
  have hmaj : Summable (fun pk : Nat.Primes × ℕ =>
      (4 * ((pk.1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ pk.2) := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => 4 * ((p : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)))
      (g := fun k : ℕ => ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k) ?_ ?_ ?_ ?_
    · exact (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 4
    · exact summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  refine Summable.of_nonneg_of_le (fun pk => ?_) (fun pk => ?_) hmaj
  · simp only [Function.comp_apply, hF]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  · obtain ⟨⟨p, hp⟩, k⟩ := pk
    have hnp : ¬ (p ^ (k + 2)).Prime := Nat.Prime.not_prime_pow (by omega)
    simp only [Function.comp_apply, hF, hg_def, if_neg hnp]
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Nat.cast_pow]
    exact log_div_pow_add_two_rpow_three_quarters_le _ (by exact_mod_cast hp.two_le) k

end GlobalTheory.Lin.NonPrimeVonMangoldt
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin


open ArithmeticFunction.vonMangoldt (residueClass LFunctionResidueClassAux LFunctionResidueClassAux_real
  eqOn_LFunctionResidueClassAux residueClass_apply_zero continuousOn_LFunctionResidueClassAux
  abscissaOfAbsConv_residueClass_le_one) in
theorem exists_tsum_vonMangoldt_div_rpow_le_div :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      Summable (fun n : ℕ => Λ n / (n : ℝ) ^ (1 + s)) ∧
        ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + s) ≤ C / s := by
  have ha : IsUnit (1 : ZMod 1) := isUnit_one
  have hres : ∀ n : ℕ, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n = Λ n := fun n =>
    Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim (α := ZMod 1) _ _) _
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n / (n : ℝ) ^ x =
        (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re
          + ((Nat.totient 1 : ℕ) : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux_real ha hx,
      ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, ArithmeticFunction.vonMangoldt.residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have hc : ContinuousOn (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ)
      (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (1 : ZMod 1))
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x (hx : x ∈ Set.Icc (1 : ℝ) 2) ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨B, hB⟩ := bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc hc
  refine ⟨|B| + 1, by linarith [abs_nonneg B], fun s hs hs1 => ⟨?_, ?_⟩⟩
  · have : Summable fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n / (n : ℝ) ^ (1 + s) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1 : ZMod 1)).trans_lt <| by
          have : (1 : ℝ) < 1 + s := by linarith
          exact_mod_cast this
    simpa only [hres] using this
  · have h1 := H (x := 1 + s) (by linarith)
    have h2 := hB _ (Set.mem_image_of_mem
      (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (show 1 + s ∈ Set.Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩))
    simp only [hres, Nat.totient_one, Nat.cast_one, inv_one, add_sub_cancel_left] at h1
    rw [h1, add_div]
    have h3 : |B| ≤ |B| / s := by
      rw [le_div_iff₀ hs]
      exact mul_le_of_le_one_right (abs_nonneg B) hs1
    have h4 := le_abs_self B
    linarith

end GlobalTheory.Lin
end

section

open MeasureTheory Topology
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_bruhatFunction_of_closedEmbedding : ∀ (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T'] (j : T' →* T), IsClosedEmbedding j → ∀ (m' : Measure T') [m'.IsHaarMeasure] [m'.IsInvInvariant], ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  first | exact @GlobalTheory.exists_bruhat_function_closedEmbedding | exact GlobalTheory.exists_bruhat_function_closedEmbedding | (intros; apply GlobalTheory.exists_bruhat_function_closedEmbedding <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le : ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M → ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | exact GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | (intros; apply GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le <;> assumption)
end
