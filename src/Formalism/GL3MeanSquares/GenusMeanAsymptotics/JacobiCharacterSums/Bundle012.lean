module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.GL3MeanSquares.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLsA
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

@[expose] public section

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  unfold cN
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

theorem RR_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N :=
  Finset.sum_nonneg fun n _ => hc n

theorem abs_sum_jacobi_le (PP : Finset ℕ) (s : ℕ) :
    |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ (PP.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PP, |(jacobiSym (q : ℤ) s : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy (q : ℤ) s with h | h | h <;> simp [h]
  simpa using Finset.sum_le_sum this

theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← this]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma divSq_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  have h := harmonic_le_one_add_log x
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

lemma divSq_count (x : ℕ) : ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, if Nat.lcm p.1 p.2 ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    have hd : n.divisors = (Icc 1 x).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h, h0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hn.2⟩, h⟩
      · rintro ⟨_, h⟩
        exact ⟨h, by omega⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, sq, ← Nat.cast_mul,
      ← card_product, hd, ← filter_product]
    congr 2
    ext p
    simp [Nat.lcm_dvd_iff]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

lemma divSq_lcm {a b : ℕ} (ha : 1 ≤ a) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have h1 : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have h2 : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
    _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [h1, h2]
    _ = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by ring

lemma divSq_cube (x : ℕ) :
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    with hφ
  set F : ℕ × ℕ × ℕ → ℝ := fun t => ((t.1 : ℝ))⁻¹ * (((t.2.1 : ℝ))⁻¹ * ((t.2.2 : ℝ))⁻¹) with hF
  have hinj : Set.InjOn φ (Icc 1 x ×ˢ Icc 1 x : Finset (ℕ × ℕ)) := by
    intro p _ q _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨hg, h1, h2⟩ := h
    have e1 : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have e3 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e4 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    ext
    · calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := e1.symm
        _ = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := by rw [h1, hg]
        _ = q.1 := e3
    · calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := e2.symm
        _ = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := by rw [h2, hg]
        _ = q.2 := e4
  have hsub : (Icc 1 x ×ˢ Icc 1 x).image φ ⊆ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x) := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    simp only [mem_product, mem_Icc] at hp
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hp
    have hg : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ a1
    simp only [hφ, mem_product, mem_Icc]
    refine ⟨⟨hg, (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)) hg, (Nat.div_le_self _ _).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd b1 (Nat.gcd_dvd_right _ _)) hg, (Nat.div_le_self _ _).trans b2⟩⟩
  calc ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, F (φ p) := by
        refine sum_congr rfl fun p hp => ?_
        simp only [mem_product, mem_Icc] at hp
        rw [divSq_lcm hp.1.1]
        simp only [hF, hφ]
        push_cast
        rw [mul_inv, mul_inv, mul_assoc]
    _ = ∑ t ∈ (Icc 1 x ×ˢ Icc 1 x).image φ, F t := (sum_image hinj).symm
    _ ≤ ∑ t ∈ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x), F t := by
        refine sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => ?_
        simp only [hF]
        positivity
    _ = (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
        simp only [hF]
        rw [sum_product]
        simp only [sum_product, ← mul_sum, ← sum_mul]
        ring

theorem divisor_square_bound : DivSq := by
  intro x hx
  have hlog : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := sum_nonneg fun k _ => by positivity
  calc ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := divSq_count x
    _ ≤ ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, (x : ℝ) * ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        rw [← div_eq_mul_inv]
        exact Nat.cast_div_le
    _ = (x : ℝ) * ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ (x : ℝ) * (1 + Real.log x) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg x)
        exact (divSq_cube x).trans (pow_le_pow_left₀ hH0 (divSq_harm x) 3)

theorem coefficient_block_bound : CoefficientBlockBound := by
  intro Y N U σ hU hσ
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := mco_norm_le Y N hn1
    have h2 : (n : ℝ) ^ (-σ) ≤ (U : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hU0 hUn (by linarith)
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ((U : ℝ) ^ (-σ)) ^ 2 = (U : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      congr 1
      push_cast
      ring
    calc (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
        ≤ ((n.divisors.card : ℝ) * (U : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h3)
            (mul_le_mul h1 h2 h3 (Nat.cast_nonneg _)) 2
      _ = (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
          rw [mul_pow, h4, mul_comm]
  have hsub : Ioc U (2 * U) ⊆ Icc 1 (2 * U) := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  have hD := divisor_square_bound (2 * U) (by omega)
  have hpow : (U : ℝ) ^ (1 - 2 * σ) = (U : ℝ) ^ (-(2 * σ)) * U := by
    rw [show (1 - 2 * σ) = -(2 * σ) + 1 by ring, Real.rpow_add hU0, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Ioc U (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Icc 1 (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hU0.le _)
        exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * (((2 * U : ℕ) : ℝ) * (1 + Real.log ((2 * U : ℕ) : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hU0.le _)
    _ = 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
        rw [hpow]
        push_cast
        ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

def Φe (j : ZMod 2) : ℂ := if j = 0 then -1 else 1

def eps (n : ℕ) : ℂ := Φe (n : ZMod 2)

lemma Φe_sum : ∑ j, Φe j = 0 := by
  show ∑ j : Fin 2, (if j = 0 then (-1 : ℂ) else 1) = 0
  simp [Fin.sum_univ_two]

lemma eps_eq (n : ℕ) : eps n = if n % 2 = 0 then -1 else 1 := by
  unfold eps Φe
  have h : ((n : ZMod 2) = 0) ↔ n % 2 = 0 := by rw [ZMod.natCast_eq_zero_iff]; omega
  by_cases hn : n % 2 = 0
  · rw [if_pos (h.mpr hn), if_pos hn]
  · rw [if_neg (fun h' => hn (h.mp h')), if_neg hn]

lemma Ap_eps (n : ℕ) : Ap eps n = ((n % 2 : ℕ) : ℂ) := by
  induction n with
  | zero => simp [Ap_zero]
  | succ n ih =>
    rw [Ap_succ, ih, eps_eq]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      rw [h, h']
      norm_num
    · have h' : (n + 1) % 2 = 0 := by omega
      rw [h, h']
      norm_num

lemma norm_Ap_eps_le (M : ℕ) : ‖Ap eps M‖ ≤ 1 := by
  rw [Ap_eps]
  rcases Nat.mod_two_eq_zero_or_one M with h | h <;> rw [h] <;> simp

lemma LFunction_eq_G_of_one_lt {s : ℂ} (hs : 1 < s.re) : ZMod.LFunction Φe s = G eps s := by
  rw [ZMod.LFunction_eq_LSeries Φe hs]
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, eps n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries (fun n => Φe n) s)) := by
    have hsum := (ZMod.LSeriesSummable_of_one_lt_re Φe hs).hasSum.tendsto_sum_nat
    have h2 := hsum.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [← Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range _ (LSeries.term_zero _ _)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
    rfl
  exact tendsto_nhds_unique h1 (partial_tendsto_G eps norm_Ap_eps_le (by linarith))

lemma LFunction_eq_G {s : ℂ} (hs : 0 < s.re) : ZMod.LFunction Φe s = G eps s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (ZMod.LFunction Φe) {s : ℂ | 0 < s.re} :=
    (ZMod.differentiable_LFunction_of_sum_zero Φe_sum).differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (G eps) {s : ℂ | 0 < s.re} :=
    (G_differentiableOn eps norm_Ap_eps_le).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : ZMod.LFunction Φe =ᶠ[𝓝 (2 : ℂ)] G eps := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact LFunction_eq_G_of_one_lt hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs

lemma two_cpow_one_sub (s : ℂ) : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]

lemma Φe_eq (j : ZMod 2) :
    Φe j = (1 : DirichletCharacter ℂ 2) j - (if j = 0 then 1 else 0) := by
  by_cases hj : j = 0
  · subst hj
    rw [MulChar.map_nonunit _ not_isUnit_zero]
    simp [Φe]
  · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hj)]
    simp [Φe, hj]

lemma LFunction_Φe {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Φe s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h2 : ZMod.LFunction Φe s =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction, ZMod.LFunction]
    simp_rw [Φe_eq, sub_mul, Finset.sum_sub_distrib, mul_sub, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, HurwitzZeta.hurwitzZeta_zero]
    push_cast
    ring
  have h3 := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs
  rw [DirichletCharacter.LFunctionTrivChar, Nat.Prime.primeFactors Nat.prime_two,
    Finset.prod_singleton] at h3
  rw [h2, h3, two_cpow_one_sub]
  push_cast
  ring

lemma alt_sum (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 (2 * N), eps n * (n : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hA : ∀ g : ℕ → ℂ, (Finset.Icc 1 (2 * (N + 1))).sum g =
        (Finset.Icc 1 (2 * N)).sum g + g (2 * N + 1) + g (2 * N + 2) := by
      intro g
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
    have hB : ∀ g : ℕ → ℂ, (Finset.Icc 1 (N + 1)).sum g = (Finset.Icc 1 N).sum g + g (N + 1) :=
      fun g => Finset.sum_Icc_succ_top (by omega) _
    rw [hA (fun n => (n : ℂ) ^ (-s)), hA (fun n => eps n * (n : ℂ) ^ (-s)),
      hB (fun n => (n : ℂ) ^ (-s))]
    have e1 : eps (2 * N + 1) = 1 := by rw [eps_eq, if_neg (by omega)]
    have e2 : eps (2 * N + 2) = -1 := by rw [eps_eq, if_pos (by omega)]
    have hb : ((2 * N + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
      have h := natCast_mul_natCast_cpow 2 (N + 1) (-s)
      rw [show ((2 * N + 2 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) by push_cast; ring, h]
      norm_num
    rw [e1, e2, hb]
    rw [two_cpow_one_sub] at ih ⊢
    linear_combination ih

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet EtaPartialSums

theorem eta_partial_sums : EtaPartial := by
  intro s hs hs1 N hN
  have hG : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = EtaPartialSums.G eps s := by
    rw [← LFunction_Φe hs1, LFunction_eq_G hs]
  rw [hG, alt_sum]
  refine (norm_G_sub_partial_le eps norm_Ap_eps_le hs (2 * N)).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos _ (by linarith)
    push_cast
    linarith
  have hq : 0 ≤ 1 + ‖s‖ / s.re := by
    have := div_nonneg (norm_nonneg s) hs.le
    linarith
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  calc 1 * (1 + ‖s‖ / s.re) * (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re)
      ≤ 1 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ ≤ 4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have := mul_nonneg hq h4
        nlinarith

theorem principal_zeta_bound : PrincipalZeta := by
  intro M _ s hs hz
  have hs1 : s ≠ 1 := by
    rcases hz.1 with h | h
    · exact absurd rfl h
    · exact h
  have h := hz.2
  rw [← DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1] at h
  rcases mul_eq_zero.mp h with h | h
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h
    obtain ⟨p, hp, hp0⟩ := h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
    have : (p : ℂ) ^ (-s) = 1 := by linear_combination -hp0
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  · exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end
