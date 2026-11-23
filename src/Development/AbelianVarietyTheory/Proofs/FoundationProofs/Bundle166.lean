module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_le_of_bounded_two_step_recursion (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ) (hR : 0 ≤ R)
    (h0 : c 0 = 1) (h1 : c 1 = x + y)
    (hrec : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r)
    (hb : ∀ r, ‖c r‖ ≤ C * R ^ r) : ‖x‖ ≤ R := by
  have hd : ∀ r : ℕ, c (r + 1) - y * c r = x ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [h0, h1]
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by ring]
      linear_combination hrec n + x * ih
  have key : ∀ r : ℕ, ‖x‖ ^ (r + 1) ≤ C * (R + ‖y‖) * R ^ r := by
    intro r
    calc ‖x‖ ^ (r + 1) = ‖c (r + 1) - y * c r‖ := by rw [hd r, norm_pow]
      _ ≤ ‖c (r + 1)‖ + ‖y‖ * ‖c r‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * R ^ (r + 1) + ‖y‖ * (C * R ^ r) :=
          add_le_add (hb _) (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
      _ = C * (R + ‖y‖) * R ^ r := by ring
  by_contra hlt
  push_neg at hlt
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hlt
  have hq0 : 0 ≤ R / ‖x‖ := div_nonneg hR hxpos.le
  have hq1 : R / ‖x‖ < 1 := (div_lt_one hxpos).2 hlt
  have ht : Tendsto (fun r : ℕ => C * (R + ‖y‖) * (R / ‖x‖) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * (R + ‖y‖))
  have hle : ∀ r : ℕ, ‖x‖ ≤ C * (R + ‖y‖) * (R / ‖x‖) ^ r := by
    intro r
    have hpos : 0 < ‖x‖ ^ r := pow_pos hxpos r
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, ← pow_succ']
    exact key r
  have : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  linarith

theorem roots_norm_le_of_bounded_two_step_recursion :
    ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y →
      (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) →
      ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  intro x y c C R hR h0 h1 hrec hb
  refine ⟨norm_le_of_bounded_two_step_recursion x y c C R hR h0 h1 hrec hb,
    norm_le_of_bounded_two_step_recursion y x c C R hR h0 (by rw [h1, add_comm]) ?_ hb⟩
  intro r
  rw [hrec r]
  ring

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.SecondDiff

lemma half_le_norm {z w : ℂ} (hw : ‖w - z‖ ≤ ‖z‖ / 2) : ‖z‖ / 2 ≤ ‖w‖ := by
  have h := norm_sub_norm_le z w
  rw [norm_sub_rev] at h
  linarith

lemma ne_zero_of_near {z w : ℂ} (hz : z ≠ 0) (hw : ‖w - z‖ ≤ ‖z‖ / 2) : w ≠ 0 := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := half_le_norm hw
  intro h0
  rw [h0, norm_zero] at h
  linarith

lemma zpow_neg_lip (n : ℕ) {z u v : ℂ} (hz : z ≠ 0)
    (hu : ‖u - z‖ ≤ ‖z‖ / 2) (hv : ‖v - z‖ ≤ ‖z‖ / 2) :
    ‖u ^ (-(n:ℤ)) - v ^ (-(n:ℤ))‖ ≤ n * (2 / ‖z‖) ^ (n + 1) * ‖u - v‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), ‖w - z‖ ≤ ‖z‖ / 2 := by
    intro w hw; simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), HasDerivAt (fun x : ℂ => x ^ (-(n:ℤ)))
      (((-(n:ℤ) : ℤ) : ℂ) * w ^ (-(n:ℤ) - 1)) w :=
    fun w hw => hasDerivAt_zpow _ w (Or.inl (ne_zero_of_near hz (hmem w hw)))
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x : ℂ => x ^ (-(n:ℤ)))
    (s := Metric.closedBall z (‖z‖ / 2)) (x := v) (y := u) (C := n * (2 / ‖z‖) ^ (n + 1))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv]
      have hw' : ‖z‖ / 2 ≤ ‖w‖ := half_le_norm (hmem w hw)
      have hwpos : 0 < ‖w‖ := by linarith
      rw [norm_mul, norm_zpow]
      have e1 : ‖(((-(n:ℤ)) : ℤ) : ℂ)‖ = n := by simp
      have e2 : -(n:ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, zpow_neg, zpow_natCast, ← inv_div, inv_pow]
      gcongr)
    (convex_closedBall z _)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)
  simpa using key

theorem second_diff_inv_pow : ∀ j : ℕ, ∃ C : ℝ, ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
    ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖
      ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2) := by
  intro j
  refine ⟨j * (j + 1) * 2 ^ (j + 2), ?_⟩
  intro z a b hz ha hb
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set g : ℂ → ℂ := fun w => w ^ (-(j:ℤ)) - (w + a) ^ (-(j:ℤ)) with hg
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), ‖w - z‖ ≤ ‖z‖ / 2 ∧ ‖w + a - z‖ ≤ ‖z‖ / 2 := by
    intro w hw
    have h : ‖w - z‖ ≤ ‖z‖ / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    refine ⟨by linarith, ?_⟩
    calc ‖w + a - z‖ = ‖(w - z) + a‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖a‖ := norm_add_le _ _
      _ ≤ ‖z‖ / 2 := by linarith
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), HasDerivAt g
      ((((-(j:ℤ)) : ℤ) : ℂ) * (w ^ (-(j:ℤ) - 1) - (w + a) ^ (-(j:ℤ) - 1))) w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hmem w hw
    have d1 := hasDerivAt_zpow (-(j:ℤ)) w (Or.inl (ne_zero_of_near hz h1))
    have d2 := (hasDerivAt_zpow (-(j:ℤ)) (w + a) (Or.inl (ne_zero_of_near hz h2))).comp_add_const w a
    rw [mul_sub]
    exact d1.sub d2
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
    (s := Metric.closedBall z (‖z‖ / 4)) (x := z) (y := z + b)
    (C := j * ((j + 1 : ℕ) * (2 / ‖z‖) ^ ((j + 1 : ℕ) + 1) * ‖a‖))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv, norm_mul]
      obtain ⟨h1, h2⟩ := hmem w hw
      have e1 : ‖(((-(j:ℤ)) : ℤ) : ℂ)‖ = j := by simp
      have e2 : -(j:ℤ) - 1 = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2]
      have L := zpow_neg_lip (j + 1) hz h1 h2
      have e3 : ‖w - (w + a)‖ = ‖a‖ := by rw [sub_add_cancel_left, norm_neg]
      rw [e3] at L
      gcongr)
    (convex_closedBall z _)
    (by simp [Metric.mem_closedBall, dist_eq_norm]; positivity)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using (by linarith : ‖b‖ ≤ ‖z‖ / 4))
  have eq : (z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹ = -(g (z + b) - g z) := by
    simp only [hg, zpow_neg, zpow_natCast]
    rw [show z + b + a = z + a + b by ring]
    ring
  rw [eq, norm_neg]
  refine key.trans (le_of_eq ?_)
  rw [add_sub_cancel_left, div_pow]
  push_cast
  field_simp

end GlobalTheory.EisM.SecondDiff
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
namespace GlobalTheory.EisM

theorem locineq_log_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    T * ‖∑ i, z i‖ ^ 2 ≤ - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
  have hs : ∀ i j, HasSum (fun n : ℕ => (z i * conj (z j) * T) ^ n / n)
      (-Complex.log (1 - z i * conj (z j) * T)) := fun i j =>
    Complex.hasSum_taylorSeries_neg_log (h i j)
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => hs i j))
  have H2 := ((Complex.hasSum_iff _ _).mp H).1
  have hterm : ∀ n : ℕ, (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)).re
      = T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n := by
    intro n
    have e : (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ))
        = (((T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n : ℝ)) : ℂ) := by
      have e1 : ∀ i j, (z i * conj (z j) * T) ^ n / (n : ℂ)
          = z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n) := by
        intro i j; rw [map_pow]; ring
      simp_rw [e1]
      have e2 : ∑ i, ∑ j, z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n)
          = (∑ i, z i ^ n) * conj (∑ j, z j ^ n) * ((T : ℂ) ^ n / n) := by

        rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
      rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [e, Complex.ofReal_re]
  have hre : (∑ i, ∑ j, -Complex.log (1 - z i * conj (z j) * T)).re
      = - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
    simp [Complex.re_sum, Complex.log_re]
  rw [hre] at H2
  simp_rw [hterm] at H2
  have := le_hasSum H2 1 (fun n _ => by positivity)
  simpa using this

theorem locineq_exp_prod {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    Real.exp (‖∑ i, z i‖ ^ 2 * T) * ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖ ≤ 1 := by
  have hpos : ∀ i j, 0 < ‖1 - z i * conj (z j) * T‖ := by
    intro i j
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun e => ?_)
    have := h i j
    rw [← e, norm_one] at this
    exact lt_irrefl _ this
  have hP : ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖
      = Real.exp (∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos i j)).symm
  rw [hP, ← Real.exp_add, Real.exp_le_one_iff]
  have := locineq_log_sum z T hT h
  linarith

theorem locineq : ∀ (x y : ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 →
    Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖(1 - x * T) * (1 - y * T)‖ ^ 2 *
      ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)) ≤ 1 := by
  intro x y T hT0 hT1 hx hy
  have hxT : ‖x‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg x) (norm_nonneg x))]
  have hyT : ‖y‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg y) (norm_nonneg y))]
  have hxy : ‖x‖ * ‖y‖ * T < 1 := by
    nlinarith [mul_nonneg (sq_nonneg (‖x‖ - ‖y‖)) hT0]
  let z : Fin 3 → ℂ := ![1, x, y]
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
  have h : ∀ i j, ‖z i * conj (z j) * T‖ < 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hnT, Complex.norm_conj, abs_of_nonneg hT0] <;> nlinarith
  have key := locineq_exp_prod z T hT0 h
  have c1 : ‖1 - conj x * T‖ = ‖1 - x * T‖ := by
    rw [← Complex.norm_conj (1 - x * T)]; simp
  have c2 : ‖1 - conj y * T‖ = ‖1 - y * T‖ := by
    rw [← Complex.norm_conj (1 - y * T)]; simp
  have c3 : ‖1 - y * conj x * T‖ = ‖1 - x * conj y * T‖ := by
    rw [← Complex.norm_conj (1 - x * conj y * T)]; simp; ring_nf
  have d0 : ‖1 - (T : ℂ)‖ = 1 - T := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dx : ‖1 - x * conj x * T‖ = 1 - ‖x‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dy : ‖1 - y * conj y * T‖ = 1 - ‖y‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [z, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, mul_one] at key
  rw [c1, c2, c3, d0, dx, dy] at key
  rw [norm_mul]
  calc _ = Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖1 - x * T‖ * ‖1 - y * T‖ *
        (‖1 - x * T‖ * (1 - ‖x‖ ^ 2 * T) * ‖1 - x * conj y * T‖) *
        (‖1 - y * T‖ * ‖1 - x * conj y * T‖ * (1 - ‖y‖ ^ 2 * T))) := by ring
    _ ≤ 1 := key

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DivSq

theorem four_factors {n x y : ℕ} (hx : x ∣ n) (hy : y ∣ n) (hn : n ≠ 0) :
    ∃ a b c e : ℕ, a * b * c * e = n ∧ a * b = x ∧ a * c = y := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simpa using hx)
  obtain ⟨e, he⟩ := Nat.lcm_dvd hx hy
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left x y
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_right x y
  refine ⟨Nat.gcd x y, b, c, e, ?_, hb.symm, hc.symm⟩
  have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx0)
  have h1 := Nat.gcd_mul_lcm x y
  have h2 : Nat.gcd x y * b * c = Nat.lcm x y := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [h1]
    calc Nat.gcd x y * (Nat.gcd x y * b * c) = (Nat.gcd x y * b) * (Nat.gcd x y * c) := by ring
      _ = x * y := by rw [← hb, ← hc]
  rw [h2, ← he]

theorem inv_rpow_natCast_mul (p : ℝ) (a b : ℕ) :
    ((((a * b : ℕ)) : ℝ) ^ p)⁻¹ = ((a : ℝ) ^ p)⁻¹ * ((b : ℝ) ^ p)⁻¹ := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]

theorem sum_range_le_pow (p : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      ≤ (∑ n ∈ Finset.range N, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
  classical
  set I := Finset.range N with hI
  let φ : ℕ × ℕ × ℕ × ℕ → (Σ _ : ℕ, ℕ × ℕ) :=
    fun q => ⟨q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.1 * q.2.1, q.1 * q.2.2.1⟩
  let w : (Σ _ : ℕ, ℕ × ℕ) → ℝ := fun s => ((s.1 : ℝ) ^ p)⁻¹
  have hw : ∀ s, 0 ≤ w s := fun s => by simp only [w]; positivity
  have h1 : ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      = ∑ s ∈ I.sigma (fun n => n.divisors ×ˢ n.divisors), w s := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [w, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have h2 : I.sigma (fun n => n.divisors ×ˢ n.divisors) ⊆ (I ×ˢ I ×ˢ I ×ˢ I).image φ := by
    rintro ⟨n, x, y⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors, hI, Finset.mem_range] at hs
    obtain ⟨hnN, ⟨hx, hn⟩, hy, -⟩ := hs
    obtain ⟨a, b, c, e, rfl, rfl, rfl⟩ := four_factors hx hy hn
    have key : ∀ d, d ∣ a * b * c * e → d ∈ I := fun d hd => by
      rw [hI, Finset.mem_range]
      exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hnN
    refine Finset.mem_image.2 ⟨(a, b, c, e), ?_, rfl⟩
    simp only [Finset.mem_product]
    exact ⟨key _ ⟨b * c * e, by ring⟩, key _ ⟨a * c * e, by ring⟩, key _ ⟨a * b * e, by ring⟩,
      key _ ⟨a * b * c, by ring⟩⟩
  have h3 : ∑ s ∈ (I ×ˢ I ×ˢ I ×ˢ I).image φ, w s ≤ ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) :=
    Finset.sum_image_le_of_nonneg (fun s _ => hw s)
  have h4 : ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
    have : (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) *
      ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹))) := by
      ring
    rw [this]
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [w, φ]
    rw [inv_rpow_natCast_mul, inv_rpow_natCast_mul, inv_rpow_natCast_mul]
    ring
  rw [h1, ← h4]
  exact (Finset.sum_le_sum_of_subset_of_nonneg h2 fun s _ _ => hw s).trans h3

theorem summable_card_divisors_sq_div_rpow :
    ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro s hs
  have hz : Summable fun n : ℕ => ((n : ℝ) ^ (1 + s))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine summable_of_sum_range_le (c := (∑' n : ℕ, ((n : ℝ) ^ (1 + s))⁻¹) ^ 4)
    (fun n => by positivity) fun N => ?_
  refine (sum_range_le_pow (1 + s) N).trans ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => by positivity)
    (hz.sum_le_tsum _ fun n _ => by positivity) 4

end GlobalTheory.DivSq
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem unitRoot_split : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (t D : ℂ),
    ‖ι.symm t‖ = 1 → ‖ι.symm D‖ < 1 →
    ∃ α β : ℂ, α + β = t ∧ α * β = D ∧ ‖ι.symm α‖ = 1 ∧ ‖ι.symm β‖ = ‖ι.symm D‖ := by
  intro l _ ι t D ht hD
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4 * D) (n := 2) (by norm_num)
  have hsum : (t + s) / 2 + (t - s) / 2 = t := by ring
  have hprod : (t + s) / 2 * ((t - s) / 2) = D := by
    have : (t + s) / 2 * ((t - s) / 2) = (t ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have key : ∀ a b : ℂ, a + b = t → a * b = D → 1 ≤ ‖ι.symm a‖ →
      ‖ι.symm a‖ = 1 ∧ ‖ι.symm b‖ = ‖ι.symm D‖ := by
    intro a b hab hmul ha
    have hmulN : ‖ι.symm a‖ * ‖ι.symm b‖ = ‖ι.symm D‖ := by
      rw [← norm_mul, ← map_mul, hmul]
    have hb : ‖ι.symm b‖ < 1 := by
      by_contra h
      push_neg at h
      have : 1 ≤ ‖ι.symm a‖ * ‖ι.symm b‖ := by nlinarith
      linarith
    have hta : ι.symm a = ι.symm t + (-ι.symm b) := by
      rw [← hab, map_add (f := _)]; ring
    have hne : ‖ι.symm t‖ ≠ ‖-ι.symm b‖ := by rw [norm_neg, ht]; exact (ne_of_lt hb).symm
    have ha1 : ‖ι.symm a‖ = 1 := by
      rw [hta, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, ht]
      exact max_eq_left hb.le
    refine ⟨ha1, ?_⟩
    rw [← hmulN, ha1, one_mul]
  have hmax : 1 ≤ max ‖ι.symm ((t + s) / 2)‖ ‖ι.symm ((t - s) / 2)‖ := by
    have := IsUltrametricDist.norm_add_le_max (ι.symm ((t + s) / 2)) (ι.symm ((t - s) / 2))
    rw [← map_add (f := _), hsum, ht] at this
    exact this
  rcases le_max_iff.mp hmax with h | h
  · obtain ⟨h1, h2⟩ := key _ _ hsum hprod h
    exact ⟨_, _, hsum, hprod, h1, h2⟩
  · have hsum' : (t - s) / 2 + (t + s) / 2 = t := by rw [add_comm]; exact hsum
    have hprod' : (t - s) / 2 * ((t + s) / 2) = D := by rw [mul_comm]; exact hprod
    obtain ⟨h1, h2⟩ := key _ _ hsum' hprod' h
    exact ⟨_, _, hsum', hprod', h1, h2⟩

end GlobalTheory
end
