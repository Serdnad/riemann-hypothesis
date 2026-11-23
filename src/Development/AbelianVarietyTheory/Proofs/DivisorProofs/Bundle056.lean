module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

section

open Set Filter Topology MeasureTheory

namespace GlobalTheory.RadialIntegral

lemma hasDerivAt_prim (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by
  have hp : 0 < a + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add a)
  have h2 := ((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)
  refine h2.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma tendsto_prim (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1
  simpa using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg

lemma radial (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹ := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp

theorem lintegral_inv_pow_add_norm_sq (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹)
      = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have h0 : 0 < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul h0.le]
  rw [h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]
  simp only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end GlobalTheory.RadialIntegral
end

section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

private theorem choose_succ_mul_succ_eq_mul_choose (c n : ℕ) :
    (((c + (n + 1)).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((c : ℝ) + n + 1) * (((c + n).choose n : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (c + n) n
  have h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n := by
    rw [show c + (n + 1) = c + n + 1 by ring]
    linarith
  exact_mod_cast h'

theorem choose_add_le_pow_mul_choose_add (a b : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (a : ℝ) ≤ b + y * (b + 1)) (n : ℕ) :
    (((a + n).choose n : ℕ) : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA := choose_succ_mul_succ_eq_mul_choose a n
    have hB := choose_succ_mul_succ_eq_mul_choose b n
    have hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hCb : (0 : ℝ) ≤ (((b + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1) := by
      nlinarith [mul_nonneg hy hn]
    have hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have hpow : (0 : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) :=
      mul_nonneg (pow_nonneg (by linarith) n) hCb
    rw [← mul_le_mul_iff_of_pos_right hpos]
    rw [hA, mul_assoc, hB]
    calc ((a : ℝ) + n + 1) * (((a + n).choose n : ℕ) : ℝ)
        ≤ ((1 + y) * ((b : ℝ) + n + 1)) * ((1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)) :=
          mul_le_mul hlin ih hCa hfac
      _ = (1 + y) ^ (n + 1) * (((b : ℝ) + n + 1) * (((b + n).choose n : ℕ) : ℝ)) := by ring

theorem exp_le_one_add_of_le_tenth (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10) :
    Real.exp x ≤ 1 + 53 / 50 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.mp hb).2
  rw [abs_of_nonneg h0] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have hx2 : x ^ 2 ≤ x / 10 := by nlinarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith
  nlinarith

theorem choose_rank_ratio_le :
    ∀ (D T a : ℕ) (ρ : ℝ), 2 ≤ D → 20 * D ≤ T → 0 ≤ ρ → ρ ≤ 1 / 4 → (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ 1 / 10 → (((a + D).choose D : ℕ) : ℝ) ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) := by
  intro D T a ρ hD hT hρ0 hρ1 ha hε
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hT' : (20 : ℝ) * D ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hbD : (T - 1 - D) + D = T - 1 := by omega
  have hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D := by
    have h3 : (T - 1 - D) + D + 1 = T := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast at h
    linarith
  have hρ' : 0 < 1 - ρ := by linarith
  have hTD : 0 < (T : ℝ) - D := by linarith
  have hden : 0 < (1 - ρ) * ((T : ℝ) - D) := mul_pos hρ' hTD
  have hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T := by nlinarith [mul_nonneg hρ0 hTpos.le]
  have hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := div_nonneg hnum0 hden.le
  have hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)
      = (2 * D + 5 + ρ * T) / (1 - ρ) := by
    rw [hbR]
    field_simp
    ring
  have hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ)
      + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) := by
    rw [hyb, hbR]
    have key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ) := by
      rw [div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']
      nlinarith [mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]
    linarith
  have h1 := choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D
  rw [hbD] at h1
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))
      = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by ring
  have hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by
    rw [← hDy]; exact mul_nonneg (Nat.cast_nonneg _) hy0
  have hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) := by
    rw [← hDy, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D
  have hexp := exp_le_one_add_of_le_tenth _ hε0 hε
  have hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]
  have hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) := mul_nonneg (Nat.cast_nonneg _) hnum0
  have h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))
      ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) :=
    div_le_div_of_nonneg_left hnum (by positivity) hu
  have e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)
      = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ) := by
    field_simp
  have e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hTpos.le
  have e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T) := by ring
  have hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T := by positivity
  have hdr : (0 : ℝ) ≤ (D : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
  have hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ) := by
    rw [e3]
    nlinarith
  calc (((a + D).choose D : ℕ) : ℝ)
      ≤ (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D * (((T - 1).choose D : ℕ) : ℝ) := h1
    _ ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hfin hC

end GlobalTheory
end

section

namespace GlobalTheory.IterativeScalingBound

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (2 + (w - 1)) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖2 + (w - 1)‖ := by
    have t := norm_sub_le (2 + (w - 1)) (w - 1)
    have e2 : (2 + (w - 1)) - (w - 1) = (2 : ℂ) := by ring
    rw [e2] at t
    have : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have h0 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  nlinarith

theorem main : ∀ (z : ℂ), (∀ (k : ℕ), ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have key : ∀ k : ℕ, (3/2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have e : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2 := by rw [pow_succ 2 n, pow_mul]
      rw [e, pow_succ (3/2 : ℝ) n]
      calc (3/2 : ℝ) ^ n * (3/2) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ 2 ^ n - 1‖ := by gcongr
        _ ≤ _ := step _ (h n)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key k
  have h2 := h k
  have h3 : 1 / 2 < (3/2 : ℝ) ^ k * ‖z - 1‖ := by rwa [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterativeScalingBound
end

section

namespace GlobalTheory.HilbFam

theorem exists_radius_moebius_perturbation :
    ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  intro τ c t hτ
  have h1 : ContinuousAt (fun z : ℂ => ‖1 + z * c‖) 0 := by fun_prop
  have h2' : ContinuousAt (fun z : ℂ => τ + t * z / (1 + z * c)) 0 := by
    refine continuousAt_const.add (ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp))
  have h2 : ContinuousAt (fun z : ℂ => (τ + t * z / (1 + z * c)).im) 0 :=
    Complex.continuous_im.continuousAt.comp h2'
  have e1 : ∀ᶠ z in nhds (0 : ℂ), (1 / 2 : ℝ) < ‖1 + z * c‖ :=
    h1.eventually (lt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ z in nhds (0 : ℂ), τ.im / 2 < (τ + t * z / (1 + z * c)).im :=
    h2.eventually (lt_mem_nhds (by simp; linarith))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨r, hr, fun z hz => ?_⟩
  have := h (y := z) (by simpa using hz)
  exact ⟨this.1.le, this.2.le⟩

end GlobalTheory.HilbFam
end

section

namespace GlobalTheory

theorem norm_inv_le_pow_card_of_norm_prod_eq_one :
    ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) →
      ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  intro B M hM hB hprod b hb
  have aux : ∀ C : Multiset ℂˣ, (∀ c ∈ C, ‖(c : ℂ)‖ ≤ M) →
      ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ ≤ M ^ C.card := by
    intro C
    induction C using Multiset.induction_on with
    | empty => intro _; simp
    | cons a C ih =>
      intro hC
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul,
        mul_comm (M ^ _)]
      exact mul_le_mul (hC a (Multiset.mem_cons_self a C))
        (ih fun c hc => hC c (Multiset.mem_cons_of_mem hc)) (norm_nonneg _) (by linarith)
  obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hb
  have hC : ∀ c ∈ C, ‖(c : ℂ)‖ ≤ M := fun c hc => hB c (Multiset.mem_cons_of_mem hc)
  rw [Multiset.map_cons, Multiset.prod_cons, norm_mul] at hprod
  have hinv : ‖((b⁻¹ : ℂˣ) : ℂ)‖ = ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv, Multiset.card_cons]
  exact (aux C hC).trans (pow_le_pow_right₀ hM (Nat.le_succ _))

end GlobalTheory
end

section

namespace GlobalTheory

theorem unitary_cocycle_coboundary_of_trivial_on_stabilisers :
    ∀ {X G : Type} [Group G] (mv : X → G → X) (z : X → G → ℂ), (∀ x, mv x 1 = x) →
      (∀ x g g', mv x (g * g') = mv (mv x g) g') → (∀ x g, ‖z x g‖ = 1) →
      (∀ x g g', z x (g * g') = z x g * z (mv x g) g') → (∀ x g, mv x g = x → z x g = 1) →
      ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ x g, c x * z x g = c (mv x g) := by
  intro X G _ mv z h1 hmul hn hz hs
  have key : ∀ b h h', mv b h = mv b h' → z b h = z b h' := by
    intro b h h' e
    have e1 : mv b (h * h'⁻¹) = b := by
      rw [hmul, e, ← hmul, mul_inv_cancel, h1]
    have e2 := hz b (h * h'⁻¹) h'
    rw [hs b _ e1, e1, one_mul, inv_mul_cancel_right] at e2
    exact e2
  let s : Setoid X :=
    { r := fun x y => ∃ g, mv x g = y
      iseqv :=
        { refl := fun x => ⟨1, h1 x⟩
          symm := by
            rintro x y ⟨g, rfl⟩
            exact ⟨g⁻¹, by rw [← hmul, mul_inv_cancel, h1]⟩
          trans := by
            rintro x y w ⟨g, rfl⟩ ⟨g', rfl⟩
            exact ⟨g * g', hmul _ _ _⟩ } }
  let b : X → X := fun x => (Quotient.mk s x).out
  have hb : ∀ x, ∃ g, mv (b x) g = x := fun x => Quotient.mk_out (s := s) x
  have hbe : ∀ x g, b (mv x g) = b x := by
    intro x g
    have : Quotient.mk s (mv x g) = Quotient.mk s x :=
      (Quotient.sound (s := s) (⟨g, rfl⟩ : ∃ g', mv x g' = mv x g)).symm
    simp only [b, this]
  choose γ hγ using hb
  refine ⟨fun x => z (b x) (γ x), fun x => hn _ _, fun x g => ?_⟩
  have e := hz (b x) (γ x) g
  rw [hγ] at e
  have e' := hγ (mv x g)
  show z (b x) (γ x) * z x g = z (b (mv x g)) (γ (mv x g))
  rw [hbe] at e' ⊢
  rw [← e]
  apply key
  rw [hmul, hγ, e']

end GlobalTheory
end

section

open scoped Matrix

namespace GlobalTheory

theorem ldl_gram_apply {r : ℕ} (ε : Fin r → ℝ) (b : Matrix (Fin r) (Fin r) ℂ) (a c : Fin r) :
    (bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
      = ∑ j, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

theorem upperTriangular_near_diag_of_gram_near (r : ℕ) (ε : Fin r → ℝ)
    (b : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hδ : 0 ≤ δ)
    (hrδ : (r : ℝ) * δ ≤ 1 / 100) (htri : ∀ a c : Fin r, c < a → b a c = 0)
    (hG : ∀ a c : Fin r, ‖(bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
      - Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) a c‖ ≤ 3 * δ) :
    (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) ∧ ∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ := by
  have hD : ∀ j, ‖((ε j : ℝ) : ℂ)‖ = 1 := fun j => by rcases hε j with h | h <;> simp [h]
  have key : ∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ ∧ ∀ c, a < c → ‖b a c‖ ≤ 6 * δ := by
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fin.pos a).ne')
    have hδ1 : δ ≤ 1 / 100 := by nlinarith

    have hR : ∀ c, a ≤ c → ‖∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)‖
        ≤ 36 / 100 * δ := by
      intro c hac
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ j ∈ Finset.univ.erase a,
          ‖b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)‖ ≤ 36 * δ ^ 2 := by
        intro j hj
        have hja : j ≠ a := Finset.ne_of_mem_erase hj
        rw [norm_mul, norm_mul, hD, Complex.norm_conj, mul_one]
        rcases lt_or_gt_of_ne hja with hlt | hgt
        · have h1 := (ih j hlt).2 a hlt
          have h2 := (ih j hlt).2 c (lt_of_lt_of_le hlt hac)
          have := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
          nlinarith
        · rw [htri j a hgt]; simp; positivity
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      have hc : ((Finset.univ.erase a).card : ℝ) ≤ r := by
        have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin r))) (a := a)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      have : ((Finset.univ.erase a).card : ℝ) * (36 * δ ^ 2) ≤ r * (36 * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      nlinarith
    have hsplit : ∀ c, (bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
        = b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)
          + ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c) := by
      intro c
      rw [ldl_gram_apply]
      exact (Finset.add_sum_erase Finset.univ
        (fun j => b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)) (Finset.mem_univ a)).symm

    have hdiag : |‖b a a‖ ^ 2 - 1| ≤ 3 * δ + 36 / 100 * δ := by
      have h0 := hG a a
      rw [hsplit, Matrix.diagonal_apply_eq] at h0
      have hR0 := hR a le_rfl
      have hx : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)
          = ((ε a : ℝ) : ℂ) * (((‖b a a‖ ^ 2 - 1 : ℝ)) : ℂ) := by
        rw [mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hn : ‖b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)‖
          = |‖b a a‖ ^ 2 - 1| := by
        rw [hx, norm_mul, hD, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [← hn]
      set R := ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j a)
      have : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)
          = (b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) + R - ((ε a : ℝ) : ℂ)) - R := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add h0 hR0)
    refine ⟨by linarith, fun c hac => ?_⟩
    have h0 := hG a c
    rw [hsplit, Matrix.diagonal_apply_ne _ (ne_of_lt hac), sub_zero] at h0
    have hR0 := hR c hac.le
    have hprod : ‖b a a‖ * ‖b a c‖ ≤ 3 * δ + 36 / 100 * δ := by
      have e : ‖b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)‖ = ‖b a a‖ * ‖b a c‖ := by
        rw [norm_mul, norm_mul, hD, Complex.norm_conj, mul_one]
      rw [← e]
      set R := ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)
      have : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)
          = (b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c) + R) - R := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add h0 hR0)
    have hsq : 9 / 10 ≤ ‖b a a‖ := by
      have h1 := (abs_le.mp hdiag).1
      nlinarith [norm_nonneg (b a a)]
    have hy := norm_nonneg (b a c)
    nlinarith
  exact ⟨fun a => (key a).1, fun a c h => (key a).2 c h⟩

end GlobalTheory
end
