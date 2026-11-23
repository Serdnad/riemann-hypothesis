module

public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Polynomial MeasureTheory Set

noncomputable section

theorem exists_polynomial_antiderivative (p : ℝ[X]) : ∃ q : ℝ[X], derivative q = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [derivative_add, ha, hb]⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / (n + 1)), ?_⟩
    rw [derivative_monomial, Nat.add_sub_cancel]
    congr 1
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

theorem exists_centredPrimitive_poly (F : ℝ[X]) :
    ∃ G : ℝ[X], (∀ c, centredPrimitive F c = G.eval c) ∧
      derivative G = F - C (uniformMean F.eval) ∧ G.eval (-1) = 0 ∧ G.eval 1 = 0 := by
  obtain ⟨q, hq⟩ := exists_polynomial_antiderivative (F - C (uniformMean F.eval))
  have hprim : ∀ c, centredPrimitive F c = q.eval c - q.eval (-1) := by
    intro c
    unfold centredPrimitive
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    · intro x _
      have := q.hasDerivAt x
      rwa [hq, eval_sub, eval_C] at this
    · exact (F.continuous.sub continuous_const).intervalIntegrable _ _
  refine ⟨q - C (q.eval (-1)), fun c => by rw [hprim]; simp, by simp [hq], by simp, ?_⟩
  have h1 := hprim 1
  unfold centredPrimitive at h1
  rw [intervalIntegral.integral_sub (F.continuous.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h1
  simp only [eval_sub, eval_C]
  rw [← h1]
  unfold uniformMean
  simp only [smul_eq_mul]
  ring

theorem exists_eq_sq_sub_one_mul (G : ℝ[X]) (hm : G.eval (-1) = 0) (hp : G.eval 1 = 0) :
    ∃ w : ℝ[X], G = (X ^ 2 - C 1) * w := by
  have h1 : (X - C 1) * (G /ₘ (X - C 1)) = G := mul_divByMonic_eq_iff_isRoot.mpr hp
  have hq : (G /ₘ (X - C 1)).IsRoot (-1) := by
    have h := congrArg (eval (-1)) h1
    rw [eval_mul, hm, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have h2 : (X - C (-1)) * ((G /ₘ (X - C 1)) /ₘ (X - C (-1))) = G /ₘ (X - C 1) :=
    mul_divByMonic_eq_iff_isRoot.mpr hq
  refine ⟨(G /ₘ (X - C 1)) /ₘ (X - C (-1)), ?_⟩
  conv_lhs => rw [← h1, ← h2]
  simp only [map_neg, map_one]
  ring

theorem zonalKernel_of_le {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hyx : y ≤ x) :
    zonalKernel x y = (1 / 2) * Real.log (1 + x) + (1 / 2) * Real.log (1 - y) - Real.log 2 := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 - y := by linarith
  unfold zonalKernel
  rw [max_eq_left hyx, min_eq_right hyx, Real.log_div (mul_pos h1 h2).ne' (by norm_num),
    Real.log_mul h1.ne' h2.ne']
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [this]
  ring

theorem zonalKernel_of_ge {x y : ℝ} (hx : x < 1) (hy : -1 < y) (hxy : x ≤ y) :
    zonalKernel x y = (1 / 2) * Real.log (1 + y) + (1 / 2) * Real.log (1 - x) - Real.log 2 := by
  have h1 : (0 : ℝ) < 1 + y := by linarith
  have h2 : (0 : ℝ) < 1 - x := by linarith
  unfold zonalKernel
  rw [max_eq_right hxy, min_eq_left hxy, Real.log_div (mul_pos h1 h2).ne' (by norm_num),
    Real.log_mul h1.ne' h2.ne']
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [this]
  ring

theorem continuousOn_zonalKernel_mul_eval {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (H : ℝ[X]) :
    ContinuousOn (fun y => zonalKernel x y * H.eval y) (Icc (-1) 1) := by
  apply ContinuousOn.mul _ H.continuous.continuousOn
  unfold zonalKernel
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log (by fun_prop)
  intro y _
  have h1 : 0 < 1 + max x y := by linarith [le_max_left x y, hx.1]
  have h2 : 0 < 1 - min x y := by linarith [min_le_left x y, hx.2]
  exact (div_pos (mul_pos h1 h2) (by norm_num)).ne'

theorem integral_zonalKernel_mul_eval (H w ρ σ : ℝ[X]) (e : ℝ)
    (hw : derivative ((X ^ 2 - C 1) * w) = H - C e)
    (hρ : derivative ρ = -((X + C 1) * w)) (hσ : derivative σ = (C 1 - X) * w)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ y in (-1 : ℝ)..1, zonalKernel x y * H.eval y =
      -e + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hcont := continuousOn_zonalKernel_mul_eval ⟨hx1, hx2⟩ H
  have hint1 : IntervalIntegrable (fun y => zonalKernel x y * H.eval y) volume (-1) x :=
    (hcont.mono (by rw [uIcc_of_le hx1.le]; exact Icc_subset_Icc le_rfl hx2.le)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun y => zonalKernel x y * H.eval y) volume x 1 :=
    (hcont.mono (by rw [uIcc_of_le hx2.le]; exact Icc_subset_Icc hx1.le le_rfl)).intervalIntegrable
  set Γ : ℝ[X] := (X ^ 2 - C 1) * w with hΓ
  have hΓe : ∀ y, Γ.eval y = (y ^ 2 - 1) * w.eval y := fun y => by simp [hΓ]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h1 : ∫ y in (-1 : ℝ)..x, zonalKernel x y * H.eval y =
      (((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - x)) *
          (Γ.eval x + e * (1 + x)) + (1 / 2) * (ρ.eval x - e * x - 2 * e * Real.log (1 - x))) -
      (((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - -1)) *
          (Γ.eval (-1) + e * (1 + -1)) +
        (1 / 2) * (ρ.eval (-1) - e * (-1) - 2 * e * Real.log (1 - -1))) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y =>
      ((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - y)) *
          (Γ.eval y + e * (1 + y)) + (1 / 2) * (ρ.eval y - e * y - 2 * e * Real.log (1 - y)))
      ?_ hint1
    intro y hy
    rw [uIcc_of_le hx1.le] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy3 : 0 < 1 - y := by linarith
    have hL : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - y)) y := by
      exact ((hasDerivAt_id y).const_sub 1).log hy3.ne'
    have hk : HasDerivAt (fun y => (1 / 2) * Real.log (1 + x) - Real.log 2 +
        (1 / 2) * Real.log (1 - y)) ((1 / 2) * (-1 / (1 - y))) y :=
      (hL.const_mul (1 / 2)).const_add _
    have hP : HasDerivAt (fun y => Γ.eval y + e * (1 + y)) (Γ.derivative.eval y + e * 1) y :=
      (Γ.hasDerivAt y).add (((hasDerivAt_id y).const_add 1).const_mul e)
    have hQ : HasDerivAt (fun y => (1 / 2) * (ρ.eval y - e * y - 2 * e * Real.log (1 - y)))
        ((1 / 2) * (ρ.derivative.eval y - e * 1 - 2 * e * (-1 / (1 - y)))) y :=
      (((ρ.hasDerivAt y).sub ((hasDerivAt_id y).const_mul e)).sub (hL.const_mul (2 * e))).const_mul
        (1 / 2)
    refine ((hk.mul hP).add hQ).congr_deriv ?_
    rw [zonalKernel_of_le hx1 (by linarith) hy2, hw, hρ]
    simp only [eval_sub, eval_neg, eval_mul, eval_add, eval_C, eval_X, hΓe]
    field_simp
    ring
  have h2 : ∫ y in x..1, zonalKernel x y * H.eval y =
      (-(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + 1)) *
          (-Γ.eval 1 + e * (1 - 1))) +
        (1 / 2) * (σ.eval 1 + 2 * e * Real.log (1 + 1) - e * 1)) -
      (-(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + x)) *
          (-Γ.eval x + e * (1 - x))) +
        (1 / 2) * (σ.eval x + 2 * e * Real.log (1 + x) - e * x)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y =>
      -(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + y)) *
          (-Γ.eval y + e * (1 - y))) + (1 / 2) * (σ.eval y + 2 * e * Real.log (1 + y) - e * y))
      ?_ hint2
    intro y hy
    rw [uIcc_of_le hx2.le] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy3 : 0 < 1 + y := by linarith
    have hL : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y := by
      exact ((hasDerivAt_id y).const_add 1).log hy3.ne'
    have hk : HasDerivAt (fun y => (1 / 2) * Real.log (1 - x) - Real.log 2 +
        (1 / 2) * Real.log (1 + y)) ((1 / 2) * (1 / (1 + y))) y :=
      (hL.const_mul (1 / 2)).const_add _
    have hP : HasDerivAt (fun y => -Γ.eval y + e * (1 - y)) (-Γ.derivative.eval y + e * (-1)) y :=
      (Γ.hasDerivAt y).neg.add (((hasDerivAt_id y).const_sub 1).const_mul e)
    have hQ : HasDerivAt (fun y => (1 / 2) * (σ.eval y + 2 * e * Real.log (1 + y) - e * y))
        ((1 / 2) * (σ.derivative.eval y + 2 * e * (1 / (1 + y)) - e * 1)) y :=
      (((σ.hasDerivAt y).add (hL.const_mul (2 * e))).sub ((hasDerivAt_id y).const_mul e)).const_mul
        (1 / 2)
    refine ((hk.mul hP).neg.add hQ).congr_deriv ?_
    rw [zonalKernel_of_ge hx2 (by linarith) hy1, hw, hσ]
    simp only [eval_sub, eval_mul, eval_C, eval_X, hΓe]
    field_simp
    ring
  rw [h1, h2]
  simp only [hΓe]
  norm_num
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

def kernelSum {S : Type*} [CommRing S] (a b : S) (k : ℕ) : S :=
  ∑ j ∈ range k, (a ^ (2 * j + 1) * b ^ (2 * k - 1 - 2 * j) - a ^ (2 * j) * b ^ (2 * k - 2 * j))

section kernelSum

variable {S : Type*} [CommRing S]

theorem kernelSum_zero (a b : S) : kernelSum a b 0 = 0 := by
  simp [kernelSum]

theorem kernelSum_succ (a b : S) (k : ℕ) :
    kernelSum a b (k + 1) =
      b ^ 2 * kernelSum a b k + (a ^ (2 * k + 1) * b - a ^ (2 * k) * b ^ 2) := by
  unfold kernelSum
  rw [sum_range_succ, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj : j < k := mem_range.mp hj
    rw [show 2 * (k + 1) - 1 - 2 * j = (2 * k - 1 - 2 * j) + 2 by omega,
      show 2 * (k + 1) - 2 * j = (2 * k - 2 * j) + 2 by omega, pow_add, pow_add]
    ring
  · rw [show 2 * (k + 1) - 1 - 2 * k = 1 by omega, show 2 * (k + 1) - 2 * k = 2 by omega, pow_one]

theorem add_mul_kernelSum (a b : S) (k : ℕ) :
    (a + b) * kernelSum a b k = b * (a ^ (2 * k) - b ^ (2 * k)) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    linear_combination b ^ 2 * ih

theorem map_kernelSum {T : Type*} [CommRing T] (φ : S →+* T) (a b : S) (k : ℕ) :
    φ (kernelSum a b k) = kernelSum (φ a) (φ b) k := by

  simp [kernelSum, map_sum, map_sub, map_mul, map_pow]

theorem kernelSum_one_one (k : ℕ) : kernelSum (1 : S) 1 k = 0 := by
  simp [kernelSum]

theorem neg_one_pow_two_mul (k : ℕ) : (-1 : S) ^ (2 * k) = 1 := by
  rw [pow_mul]
  simp

theorem kernelSum_neg_one_neg_one (k : ℕ) : kernelSum (-1 : S) (-1) k = 0 := by
  induction k with
  | zero => exact kernelSum_zero _ _
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    ring

theorem kernelSum_one_neg_one (k : ℕ) : kernelSum (1 : S) (-1) k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih]
    push_cast
    ring

theorem kernelSum_neg_one_one (k : ℕ) : kernelSum (-1 : S) 1 k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    push_cast
    ring

end kernelSum

theorem gKernel_eq_kernelSum (R : Type*) [CommRing R] (k : ℕ) :
    gKernel R k = kernelSum (X 0 : MvPolynomial (Fin 2) R) (X 1) k := rfl

theorem eval_gKernel {R : Type*} [CommRing R] (k : ℕ) (a b : R) :
    eval ![a, b] (gKernel R k) = kernelSum a b k := by
  rw [gKernel_eq_kernelSum, map_kernelSum]
  simp

theorem gKernel_isHomogeneous (R : Type*) [CommRing R] (k : ℕ) :
    (gKernel R k).IsHomogeneous (2 * k) := by
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj : j < k := mem_range.mp hj
  refine IsHomogeneous.sub ?_ ?_
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j + 1)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 1 - 2 * j))
    rwa [show 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k by omega] at h
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 2 * j))
    rwa [show 2 * j + (2 * k - 2 * j) = 2 * k by omega] at h

theorem GKernelIdentity.proof : GKernelIdentity.Statement := by
  intro R _ k
  refine ⟨?_, gKernel_isHomogeneous R k, ?_, ?_, ?_, ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gKernel_eq_kernelSum, add_mul_kernelSum]
  · rw [eval_gKernel, kernelSum_one_one]
  · rw [eval_gKernel, kernelSum_neg_one_neg_one]
  · rw [eval_gKernel, kernelSum_one_neg_one]
  · rw [eval_gKernel, kernelSum_neg_one_one]
  · have h := add_mul_kernelSum c (-1 : R) k
    rw [eval_gKernel, mul_comm]
    rw [neg_pow, pow_mul] at h
    rw [show c + -1 = c - 1 by ring] at h
    rw [h, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (-1 : R) c k
    rw [eval_gKernel, mul_comm, show c - 1 = -1 + c by ring, h, pow_mul, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (1 : R) c k
    rw [eval_gKernel, mul_comm, h]
    simp
  · have h := add_mul_kernelSum c (1 : R) k
    rw [eval_gKernel, mul_comm, h]
    simp

end GroundTheory.Heights₂.Heights.FlagBundles
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def SphereLongitudeCoordinates.Statement : Prop :=
  sphereMeasure.map (fun n : Sphere2 => (n : E3)) =
    (ENNReal.ofReal (4 * Real.pi))⁻¹ •
      (volume.restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ioc 0 (2 * Real.pi))).map
        (fun p : ℝ × ℝ => spherePoint p.1 p.2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def ZonalKernelPairing.Statement : Prop :=
  ∀ F H : Polynomial ℝ,
    (1 / 4) * ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂ =
      -(1 / 2) * uniformMean F.eval * uniformMean H.eval -
        (1 / 4) * ∫ c in (-1 : ℝ)..1, centredPrimitive F c * centredPrimitive H c / (1 - c ^ 2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

def ZonalHeightReduction.Statement : Prop :=
  ∀ F H : Polynomial ℝ,
    Integrable (fun p : Sphere2 × Sphere2 =>
      kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2)) pairMeasure ∧
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2)
        ∂pairMeasure =
      (1 / 4) * ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂

end

end GroundTheory.Heights₂.Heights.FlagBundles
end
