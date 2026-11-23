module

public import Formalism.LFunctionBounds.Bundle001
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FX

open Finset

theorem succ_le_max_mul_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / a) * Real.exp (a * k) := by
  have hM1 : (1 : ℝ) ≤ max 1 (1 / a) := le_max_left _ _
  have hMa : 1 ≤ max 1 (1 / a) * a := by
    calc (1 : ℝ) = (1 / a) * a := by field_simp
      _ ≤ max 1 (1 / a) * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc ((k : ℝ) + 1) ≤ max 1 (1 / a) * (1 + a * k) := by nlinarith
    _ ≤ max 1 (1 / a) * Real.exp (a * k) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a * k)]) (by linarith)

theorem succ_le_max_mul_pow (e : ℝ) (he : 0 < e) (p k : ℕ) (hp : 2 ≤ p) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (e * Real.log 2)) * ((p : ℝ) ^ e) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have ha : 0 < e * Real.log 2 := mul_pos he (Real.log_pos (by norm_num))
  refine (succ_le_max_mul_exp _ ha k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc e * Real.log 2 * k ≤ e * Real.log p * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog he.le) hk
    _ = k * (Real.log p * e) := by ring

theorem succ_le_pow_of_two_le (e : ℝ) (p k : ℕ) (hp : 2 ≤ (p : ℝ) ^ e) :
    ((k : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ k := by
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ e := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : ((k : ℝ) + 1) * 2 ≤ ((p : ℝ) ^ e) ^ k * (p : ℝ) ^ e :=
      mul_le_mul ih hp (by norm_num) (by positivity)
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    push_cast
    linarith

theorem rpow_eq_prod_primeFactors (e : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (n : ℝ) ^ e = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx : (0 : ℝ) ≤ p := p.cast_nonneg
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul hx,
    mul_comm ((n.factorization p : ℕ) : ℝ) e, Real.rpow_mul hx, Real.rpow_natCast]

theorem divisor_weight_bound : DivisorBound := by
  intro e he
  set M := max 1 (1 / (e * Real.log 2)) with hM
  set K := ⌈(2 : ℝ) ^ (1 / e)⌉₊ with hK
  refine ⟨M ^ K, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hcard : ((n.divisors.card : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    norm_cast
  rw [hcard, rpow_eq_prod_primeFactors e hn0]
  have hfac : ∀ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) ≤
      (if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hpK
    · exact succ_le_max_mul_pow e he p _ hp2
    · rw [one_mul]
      apply succ_le_pow_of_two_le
      have h1 : (2 : ℝ) ^ (1 / e) ≤ p :=
        (Nat.le_ceil _).trans (by exact_mod_cast (not_lt.mp hpK))
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / e)) ^ e := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ e := Real.rpow_le_rpow (by positivity) h1 he.le
  calc ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, ((if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p)) :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p < K then M else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ M ^ K * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (fun p => p < K)).card ≤ (Finset.range K).card :=
              Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          _ = K := Finset.card_range K

end Formalism.FX
end

section

open Complex Filter Topology

noncomputable section

namespace Formalism.FX


open LFunctionPartialSum in
lemma LFunctionPartialSum.norm_tail_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have K1 : ∀ x : ℝ, 1 ≤ x → ‖(x : ℂ) ^ (-s) - ((x : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hI : Set.uIcc x (x + 1) = Set.Icc x (x + 1) := Set.uIcc_of_le (by linarith)
    have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
      rw [hI]
      intro h
      linarith [h.1]
    have hderiv : ∀ t ∈ Set.uIcc x (x + 1),
        HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hr : -s - 1 ≠ -1 := by
        intro h
        apply hs0
        linear_combination -h
      first
      | exact hasDerivAt_ofReal_cpow_const ht0.ne' (neg_ne_zero.mpr hs0)
      | (have h1 := hasDerivAt_ofReal_cpow_const ht0.ne' hr
         have e : -s - 1 + 1 = -s := by ring
         rw [e] at h1
         exact h1)
    have hint : IntervalIntegrable (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) MeasureTheory.volume x (x + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr ht0))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have e2 : (x : ℂ) ^ (-s) - ((x : ℂ) + 1) ^ (-s) =
        -(∫ t in x..(x + 1), (-s) * (t : ℂ) ^ (-s - 1)) := by
      rw [hFTC]
      push_cast
      ring
    have hr' : -s.re - 1 ≠ -1 := by
      intro h
      linarith
    have hgi : IntervalIntegrable (fun t : ℝ => ‖s‖ * t ^ (-s.re - 1)) MeasureTheory.volume x (x + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne'))
    rw [e2, norm_neg]
    calc ‖∫ t in x..(x + 1), (-s) * (t : ℂ) ^ (-s - 1)‖
        ≤ ∫ t in x..(x + 1), ‖s‖ * t ^ (-s.re - 1) := by
          refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
            (MeasureTheory.ae_of_all _ (fun t ht => ?_)) hgi
          have ht0 : 0 < t := by linarith [ht.1]
          rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp
      _ = ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hr', h0⟩)]
          have e3 : -s.re - 1 + 1 = -s.re := by ring
          rw [e3]
          have hsr : s.re ≠ 0 := hs.ne'
          field_simp
          ring
  have hterm : ∀ i : ℕ, ‖dterm χ s (i + (N + 1))‖ ≤
      B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    have hx : (1 : ℝ) ≤ ((i + (N + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ i + (N + 1) by omega)
    have h1 := K1 _ hx
    rw [Complex.ofReal_natCast] at h1
    have e : (((i + 1 + (N + 1) : ℕ) : ℝ)) = ((i + (N + 1) : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [e]
    unfold dterm
    rw [norm_mul]
    exact mul_le_mul (hB _) h1 (norm_nonneg _) hB0
  have hf0 : ∀ i : ℕ, 0 ≤ B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    refine mul_nonneg hB0 (mul_nonneg hc (sub_nonneg.mpr ?_))
    have hle : (((i + (N + 1) : ℕ) : ℝ)) ≤ (((i + 1 + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show i + (N + 1) ≤ i + 1 + (N + 1) by omega)
    have hpos : (0 : ℝ) < (((i + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 0 < i + (N + 1) by omega)
    first
    | exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    | exact Real.rpow_le_rpow_of_exponent_nonpos hpos hle (by linarith)
    | (rw [Real.rpow_neg hpos.le, Real.rpow_neg (hpos.le.trans hle)]
       exact inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hle hs.le))
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub']
    have hv0 : (((0 + (N + 1) : ℕ) : ℝ)) ^ (-s.re) = ((N : ℝ) + 1) ^ (-s.re) := by
      congr 1
      push_cast
      ring
    rw [hv0]
    have hvn : 0 ≤ (((n + (N + 1) : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_nonneg (mul_nonneg hB0 hc) hvn
    nlinarith
  have hsf := summable_of_sum_range_le hf0 hpart
  have hsn : Summable (fun i : ℕ => ‖dterm χ s (i + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsf
  calc ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ ∑' i, ‖dterm χ s (i + (N + 1))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i : ℕ, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
      first
      | exact Summable.tsum_le_tsum hterm hsn hsf
      | exact tsum_le_tsum hterm hsn hsf
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := Real.tsum_le_of_sum_range_le hf0 hpart

open LFunctionPartialSum in
theorem l_function_partial_sum : LPartialSum := by
  intro q _ χ hχ B hB s hs N hN
  have hB' : ∀ M, ‖Ap χ M‖ ≤ B := hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  rw [LFunction_eq_G χ hχ hB' hs, ← partial_identity χ s N]
  have hsum := summable_dterm χ hB' hs
  have hG : LFunctionPartialSum.G χ s = ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm χ s n + Ap χ N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le χ hB' hs N
  have h2 : ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB' N) (Real.rpow_nonneg (by positivity) _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by linarith) (by linarith)
  have hq : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  have h5 : 0 ≤ ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  calc ‖∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm χ s (i + (N + 1))‖ + ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring
    _ ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (by linarith))
    _ ≤ 2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
          mul_nonneg (mul_nonneg hB0 (by linarith)) h4
        linarith

end Formalism.FX
end
end
