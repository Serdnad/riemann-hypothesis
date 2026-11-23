module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.Analysis.Asymptotics.Arith
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasFDerivAt_of_comp_immersion : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (Φ : E → F) (ψ : E → E) (x : E) (A D : E →L[ℝ] F), HasStrictFDerivAt Φ A (ψ x) → Function.Injective A → ContinuousAt ψ x → HasFDerivAt (fun y => Φ (ψ y)) D x → ∃ P : E →L[ℝ] E, HasFDerivAt ψ P x ∧ A.comp P = D := by
  intro E F _ _ _ _ _ _ Φ ψ x A D hA hinj hψ hD

  obtain ⟨g, hg⟩ := (A : E →ₗ[ℝ] F).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let L : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hLA : ∀ v, L (A v) = v := fun v => by
    have h := LinearMap.congr_fun hg v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe] at h
    first
      | exact h
      | simpa [L] using h
      | (rw [show (L : F → E) = g from LinearMap.coe_toContinuousLinearMap' g]; exact h)

  have hr : (fun y => Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) =o[nhds x] (fun y => ψ y - ψ x) :=
    hA.hasFDerivAt.isLittleO.comp_tendsto hψ
  have hs : (fun y => Φ (ψ y) - Φ (ψ x) - D (y - x)) =o[nhds x] (fun y => y - x) :=
    hD.isLittleO
  have hLr : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x))) =o[nhds x] (fun y => ψ y - ψ x) :=
    (L.isBigO_comp _ _).trans_isLittleO hr

  have hu : (fun y => ψ y - ψ x) =O[nhds x] (fun y => y - x) := by
    have h1 := hLr.right_isBigO_add
    have hsum : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) + (ψ y - ψ x))
        = fun y => L (Φ (ψ y) - Φ (ψ x)) := by
      funext y
      simp only [map_sub, hLA]
      abel
    rw [hsum] at h1
    exact h1.trans ((L.isBigO_comp _ _).trans hD.isBigO_sub)

  have hP : HasFDerivAt ψ (L.comp D) x := by
    rw [hasFDerivAt_iff_isLittleO]
    have hdiff : (fun y => L (Φ (ψ y) - Φ (ψ x) - D (y - x)) - L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)))
        = fun y => ψ y - ψ x - (L.comp D) (y - x) := by
      funext y
      simp only [map_sub, hLA, ContinuousLinearMap.comp_apply]
      abel
    rw [← hdiff]
    exact ((L.isBigO_comp _ _).trans_isLittleO hs).sub (hLr.trans_isBigO hu)
  refine ⟨L.comp D, hP, ?_⟩
  exact (hA.hasFDerivAt.comp x hP).unique hD

end GlobalTheory
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem integral_one_sub_two_mul_pow (n : ℕ) :
    ∫ s in (0 : ℝ)..1, (1 - 2 * s) ^ n = (1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1)) := by
  have h := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => x ^ n) (two_ne_zero' ℝ) 1
  simp only [mul_one, mul_zero, sub_zero] at h
  rw [h, integral_pow, smul_eq_mul]
  have e : (1 : ℝ) - 2 = -1 := by norm_num
  rw [e, one_pow]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem exp_smul_eq_tsum (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X : A) (t : ℝ) :
    NormedSpace.exp (t • X) = ∑' n : ℕ, t ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n) := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine tsum_congr fun n => ?_
  rw [smul_pow, smul_smul, smul_smul, mul_comm]

private theorem norm_one_sub_neg_one_pow_div_le_one (n : ℕ) :
    ‖(1 - (-1 : ℝ) ^ (n + 1)) / (2 * ((n : ℝ) + 1))‖ ≤ 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_le]
  rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h]
  · norm_num
  · rw [show (1 : ℝ) - -1 = 2 by norm_num, div_mul_eq_div_div, div_self (two_ne_zero' ℝ)]
    have h0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨by linarith, (div_le_one hn).2 ?_⟩
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith

theorem integral_exp_one_sub_two_mul_smul (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X : A) :
    ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • X)
      = ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • X ^ (2 * k) := by
  have hc : Summable fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • X ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  simp_rw [exp_smul_eq_tsum]
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ n : ℕ, Integrable (fun s : ℝ => (1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun n =>
    (Continuous.intervalIntegrable (by fun_prop) 0 1).1
  have hbound : ∀ n : ℕ, ∫ s in Set.Ioc (0 : ℝ) 1, ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖
      ≤ ‖((n.factorial : ℝ)⁻¹) • X ^ n‖ := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := ‖((n.factorial : ℝ)⁻¹) • X ^ n‖)
      (f := fun s : ℝ => ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖) (fun s hs => by
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [norm_norm, norm_smul, norm_pow]
        refine mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hs.1, hs.2])
    rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hsum : Summable fun n : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) 1, ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound hc
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hterm : ∀ n : ℕ, ∫ s in Set.Ioc (0 : ℝ) 1, (1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)
      = ((1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1))) • (((n.factorial : ℝ)⁻¹) • X ^ n) := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_smul_const,
      integral_one_sub_two_mul_pow]
  rw [tsum_congr hterm]
  set g : ℕ → A := fun n => ((1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1))) •
    (((n.factorial : ℝ)⁻¹) • X ^ n) with hgdef
  have hg : Summable g := Summable.of_norm_bounded hc fun n => by
    rw [hgdef, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_neg_one_pow_div_le_one n)
  have he : Summable fun k : ℕ => g (2 * k) :=
    hg.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable fun k : ℕ => g (2 * k + 1) :=
    hg.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  rw [← tsum_even_add_odd he ho]
  have hodd : ∀ k : ℕ, g (2 * k + 1) = 0 := by
    intro k
    rw [hgdef]
    simp only
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  have heven : ∀ k : ℕ, g (2 * k) = (((2 * k + 1).factorial : ℝ)⁻¹) • X ^ (2 * k) := by
    intro k
    rw [hgdef]
    simp only
    rw [pow_succ, pow_mul, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  simp_rw [hodd, heven, tsum_zero, add_zero]

end GlobalTheory.PolarU
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal : ∀ (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G), Measurable e → mK Kᶜ = 0 → (∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) → lam ≠ 0 → (∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤) → (∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧ ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) → ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f → ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  first | exact @GlobalTheory.Twist.lintegral_haar_eq_transversal | exact GlobalTheory.Twist.lintegral_haar_eq_transversal | (intros; apply GlobalTheory.Twist.lintegral_haar_eq_transversal <;> assumption)
end
