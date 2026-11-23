module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.GL3MeanSquares.Bundle001
public import Development.AutomorphicArithmetic.MeanSquareBounds.SumMinLeDiv
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem RR_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ (N m₀ : ℕ) (w : ℝ), 1 ≤ w →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ w) → RR (cN y) m₀ N ≤ C * (Real.sqrt y + w * Real.log y) := by
  obtain ⟨C₁, hC₁, hsP⟩ := exists_primePowerSum_le_mul_log
  have hK := dA_KC_pos
  refine ⟨3 * dA_KC + C₁, by positivity, ?_⟩
  intro y hy N m₀ w hw hm
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hf0 : ∀ n, 0 ≤ cN y n := fun n => dA_cN_nonneg hy0 n
  have hsplit : RR (cN y) m₀ N ≤
      (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n) +
      ∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n := by
    unfold RR
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have := hf0 n
    by_cases h1 : IsPrimePow n <;> by_cases h2 : Even (n.factorization n.minFac) <;>
      by_cases h3 : n.minFac ∣ m₀ <;> simp [h1, h2, h3, this]
  have hA : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n)
      ≤ 3 * dA_KC * Real.sqrt y := by
    have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ Even (n.factorization n.minFac))
        ⊆ (Icc 1 N).image (fun m => m ^ 2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hev⟩ := hn
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      rw [Nat.pow_minFac hk.ne', hp.minFac_eq, Nat.factorization_pow_self hp] at hev
      obtain ⟨j, rfl⟩ := hev
      refine Finset.mem_image.2 ⟨p ^ j, ?_, by ring⟩
      have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
      have h2 : p ^ j ≤ p ^ (j + j) := Nat.pow_le_pow_right hp.pos (by omega)
      exact Finset.mem_Icc.2 ⟨h1, h2.trans hnN⟩
    calc _ ≤ ∑ n ∈ (Icc 1 N).image (fun m => m ^ 2), cN y n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
      _ = ∑ m ∈ Icc 1 N, cN y (m ^ 2) :=
          Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)
      _ = ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m * min 1 (y / (m:ℝ) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero, Nat.cast_pow]
      _ ≤ dA_KC * ∑ m ∈ Icc 1 N, min 1 (y / (m:ℝ) ^ 2) := by
          refine dA_vM_major _ (fun n => le_min zero_le_one (div_nonneg hy0 (by positivity))) ?_ N
          intro n hn
          apply min_le_min_left
          apply div_le_div_of_nonneg_left hy0 (pow_pos (Nat.cast_pos.mpr hn) 2)
          have := (Nat.cast_nonneg n : (0:ℝ) ≤ n)
          push_cast
          nlinarith
      _ ≤ dA_KC * (3 * Real.sqrt y) :=
          mul_le_mul_of_nonneg_left (dA_sum_min_sq y (by linarith) N) hK.le
      _ = 3 * dA_KC * Real.sqrt y := by ring
  have hB : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n)
      ≤ C₁ * w * Real.log y := by
    set P := (Icc 1 N).filter (fun p => p.Prime ∧ p ∣ m₀ ∧ (p:ℝ) ≤ w) with hP
    have hmaps : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀),
        n.minFac ∈ P := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hd⟩ := hn
      have hpr : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
      have hle : n.minFac ≤ N := (Nat.minFac_le (by omega)).trans hnN
      simp only [hP, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpr.one_lt.le, hle⟩, hpr, hd, hm _ hpr hd hle⟩
    have hcard : (P.card : ℝ) ≤ w := by
      have hs : P ⊆ Icc 1 ⌊w⌋₊ := by
        intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.1, Nat.le_floor hp.2.2.2⟩
      have h1 := Finset.card_le_card hs
      rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
      calc (P.card : ℝ) ≤ ⌊w⌋₊ := by exact_mod_cast h1
        _ ≤ w := Nat.floor_le (by linarith)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ p ∈ P, C₁ * Real.log y := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine le_trans ?_ (hsP y hy N p)
          unfold sP
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf0 n)
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
      _ = P.card * (C₁ * Real.log y) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ w * (C₁ * Real.log y) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₁.le hlog)
      _ = C₁ * w * Real.log y := by ring
  have hsq : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hwl : 0 ≤ w * Real.log y := mul_nonneg (by linarith) hlog
  calc RR (cN y) m₀ N ≤ _ := hsplit
    _ ≤ 3 * dA_KC * Real.sqrt y + C₁ * w * Real.log y := add_le_add hA hB
    _ ≤ (3 * dA_KC + C₁) * (Real.sqrt y + w * Real.log y) := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * dA_KC) hwl, mul_nonneg hC₁.le hsq]

end QH
end

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem sum_log_primes_le_mul_log_four (Y : ℕ) :
    ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ Y * Real.log 4 := by
  rw [← Real.log_prod]
  · have h1 : ((primorial Y : ℕ) : ℝ) ≤ (4 : ℝ) ^ Y := by exact_mod_cast primorial_le_four_pow Y
    have h2 : ((primorial Y : ℕ) : ℝ) = ∏ p ∈ (range (Y + 1)).filter Nat.Prime, (p : ℝ) := by
      simp [primorial, Nat.cast_prod]
    rw [← h2, ← Real.log_pow]
    have hpos : (0 : ℝ) < (primorial Y : ℕ) := by exact_mod_cast primorial_pos Y
    exact Real.log_le_log hpos h1
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

private theorem sum_sP_sq_large_primes_le (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ 96 * Real.log 4 * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  have hY3 : 3 ≤ Y := Nat.le_floor (by exact_mod_cast hy)
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hYlt : y < (Y : ℝ) + 1 := Nat.lt_floor_add_one y
  have hY3r : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hy0 : 0 < y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hset : ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ Y) = (Ioc Y N).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨by omega, h2⟩, hp⟩, by omega⟩
  rw [hset]
  have hterm : ∀ p ∈ (Ioc Y N).filter Nat.Prime,
      sP (cN y) N p ^ 2 ≤ 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := sP_cN_le_log_div y hy0.le N p hpp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc sP (cN y) N p ^ 2 ≤ (2 * y * Real.log p / p) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
        field_simp
        ring
  have htail := sum_log_sq_div_sq_primes_tail_le N (N - Y) Y (by omega) le_rfl
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogY : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYle
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hq : 4 * Real.log 4 * (Real.log Y + 2 * Real.log 2) / Y ≤ 24 * Real.log 4 * Real.log y / y := by
    rw [div_le_div_iff₀ hY0 hy0]
    have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hE : Real.log Y + 2 * Real.log 2 ≤ 3 * Real.log y := by linarith
    have h1 : (Real.log Y + 2 * Real.log 2) * y ≤ 3 * Real.log y * y :=
      mul_le_mul_of_nonneg_right hE hy0.le
    have h2 : 3 * Real.log y * y ≤ 3 * Real.log y * (2 * Y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 4 * Real.log 4 by positivity)
    nlinarith
  calc ∑ p ∈ (Ioc Y N).filter Nat.Prime, sP (cN y) N p ^ 2
      ≤ ∑ p ∈ (Ioc Y N).filter Nat.Prime, 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := sum_le_sum hterm
    _ = 4 * y ^ 2 * ∑ p ∈ (Ioc Y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 4 * y ^ 2 * (24 * Real.log 4 * Real.log y / y) := by
        gcongr
        exact htail.trans hq
    _ = 96 * Real.log 4 * (y * Real.log y) := by
        field_simp
        ring

private theorem sum_sP_sq_small_primes_le_of_bound (C0 : ℝ) (hC0 : 0 < C0)
    (hb : ∀ (y : ℝ), 3 ≤ y → ∀ (N p : ℕ), sP (cN y) N p ≤ C0 * Real.log y) (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ (4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4) * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  set S := ⌊Real.sqrt y⌋₊ with hSdef
  have hy0 : 0 < y := by linarith
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hsq0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hSle : (S : ℝ) ≤ Real.sqrt y := Nat.floor_le hsq0
  have hSlt : Real.sqrt y < (S : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogsq : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
  have hlsy : Real.log y ≤ 2 * Real.sqrt y := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y by linarith)
    rw [hlogsq] at this
    linarith
  have hsub : ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ Y) ⊆ (range (Y + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  have step1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => sP (cN y) N p ^ 2) (fun p _ _ => sq_nonneg _)
  have hterm : ∀ p ∈ (range (Y + 1)).filter Nat.Prime, sP (cN y) N p ^ 2 ≤
      (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0) + 2 * C0 ^ 2 * Real.log y * Real.log p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := hb y hy N p
    have hsqb : sP (cN y) N p ^ 2 ≤ C0 ^ 2 * Real.log y ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h0 h1 2
    have hx : 0 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by positivity
    split_ifs with hpS
    · linarith
    · have hpS' : (S : ℝ) + 1 ≤ p := by exact_mod_cast (show S + 1 ≤ p by omega)
      have hlt : Real.sqrt y < p := by linarith
      have hlog : Real.log (Real.sqrt y) ≤ Real.log p := Real.log_le_log (by linarith) hlt.le
      rw [hlogsq] at hlog
      have : C0 ^ 2 * Real.log y ^ 2 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by
        have hc : 0 ≤ C0 ^ 2 * Real.log y := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (show Real.log y ≤ 2 * Real.log p by linarith) hc]
      linarith
  have step2 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at step2
  have hite : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0)
      ≤ ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
    rw [← sum_filter]
    have hsub2 : ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S) ⊆ range (S + 1) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      omega
    calc ∑ p ∈ ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S), C0 ^ 2 * Real.log y ^ 2
        ≤ ∑ p ∈ range (S + 1), C0 ^ 2 * Real.log y ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ = ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have htheta := sum_log_primes_le_mul_log_four Y
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hA : ((S : ℝ) + 1) * Real.log y ≤ 4 * y := by
    have : ((S : ℝ) + 1) * Real.log y ≤ (Real.sqrt y + 1) * (2 * Real.sqrt y) :=
      mul_le_mul (by linarith) hlsy hly (by linarith)
    nlinarith
  have hA' : ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) ≤ 4 * C0 ^ 2 * (y * Real.log y) := by
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ C0 ^ 2 * Real.log y by positivity)
    nlinarith
  have hB : 2 * C0 ^ 2 * Real.log y * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
      ≤ 2 * C0 ^ 2 * Real.log 4 * (y * Real.log y) := by
    have h1 : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ y * Real.log 4 :=
      htheta.trans (mul_le_mul_of_nonneg_right hYle hL.le)
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C0 ^ 2 * Real.log y by positivity)
    nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := by linarith

theorem sPsq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N : ℕ,
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN y) N p ^ 2 ≤ C * y * Real.log y := by
  obtain ⟨C0, hC0, hb⟩ := exists_primePowerSum_le_mul_log
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4 + 96 * Real.log 4, by positivity, ?_⟩
  intro y hy N
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊y⌋₊)]
  have h3 := sum_sP_sq_small_primes_le_of_bound C0 hC0 hb y hy N
  have h2 := sum_sP_sq_large_primes_le y hy N
  nlinarith

end QH
end
