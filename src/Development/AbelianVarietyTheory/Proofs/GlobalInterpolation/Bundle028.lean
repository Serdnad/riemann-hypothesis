module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle023
public import Formalism.GL3MeanSquares.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeCountRelativeErrorOfPsiRelativeError
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDualBasisOfUnimodularLatticeAtPrime
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Normed.Group.Tannery
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem rayCountTheta_fibre_count {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq1 : ∀ v, 1 ≤ q v) (hq : ∀ v, Q v = q v)
    (y : ℝ) (hy : 1 ≤ y) (hfin : {v | Q v ≤ y}.Finite) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) = (({v | Q v ≤ y}.ncard : ℕ) : ℝ) := by
  have hmaps : ∀ v ∈ hfin.toFinset, q v ∈ Finset.Icc 1 ⌊y⌋₊ := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hq] at hv
    exact Finset.mem_Icc.mpr ⟨hq1 v, Nat.le_floor hv⟩
  have hfib : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊,
      {v | Q v = (n : ℕ)}.ncard = (hfin.toFinset.filter fun v => q v = n).card := by
    intro n hn
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, hq, Nat.cast_inj]
    constructor
    · rintro rfl
      exact ⟨le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le (by linarith)), rfl⟩
    · exact fun h => h.2
  rw [show (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (((hfin.toFinset.filter fun v => q v = n).card : ℕ) : ℝ) from
    Finset.sum_congr rfl fun n hn => by rw [hfib n hn]]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hmaps, ← Set.ncard_coe_finset,
    Set.Finite.coe_toFinset]

theorem rayCountTheta_fibre_tsum {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq : ∀ v, Q v = q v) (t : ℝ)
    (hs : Summable fun v => Real.exp (-(t * Q v))) :
    ∑' n : ℕ, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n)) = ∑' v, Real.exp (-(t * Q v)) := by
  have hf := hs.hasSum.tsum_fiberwise q
  rw [← hf.tsum_eq]
  congr 1
  funext n
  have hset : {v | Q v = (n : ℕ)} = q ⁻¹' {n} := by
    ext v
    simp [hq]
  calc (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n))
      = ∑' _ : q ⁻¹' {n}, Real.exp (-(t * n)) := by
        rw [tsum_const, hset, Nat.card_coe_set_eq, nsmul_eq_mul]
    _ = ∑' b : q ⁻¹' {n}, Real.exp (-(t * Q b)) := by
        congr 1
        funext b
        rw [hq b, show q b = n from b.2]

theorem rayCountTheta : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) * y| ≤ 10 * Real.sqrt y) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) / t| ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := by
  intro K _ _ d M x hd hd4 hd100 hx hK hM D g
  obtain ⟨α, γ, l, θ₁, θ₂, hα, hγ, hαγ, hQ, ha⟩ := GlobalTheory.T.rayClassIdealCount_eq_ncard_shiftedBinaryForm K d M x hd hd4 hd100 hx hK hM D g
  choose q hq1 hq using hQ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hC : Real.pi / Real.sqrt (α * γ) = 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) := by
    have hs : Real.sqrt (α * γ) = Real.sqrt d * (M : ℝ) ^ 2 / 2 := by
      rw [hαγ, show (d : ℝ) * (M : ℝ) ^ 4 / 4 = (Real.sqrt d * (M : ℝ) ^ 2 / 2) ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt hd0.le]; ring]
      exact Real.sqrt_sq (by positivity)
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    rw [hs]
    field_simp
  refine ⟨fun y hy => ?_, fun t ht0 ht1 => ?_⟩
  · have h94 := GlobalTheory.T.abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt α γ l θ₁ θ₂ y hα hγ hy
    have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n =
        (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ y}.ncard : ℕ) : ℝ) := by
      simp only [ha]
      exact rayCountTheta_fibre_count (qForm α γ l θ₁ θ₂) q hq1 hq y hy h94.1
    rw [hsum, ← hC]
    exact h94.2
  · have h96 := GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le α γ l θ₁ θ₂ t (by linarith) (by linarith) ht0
    have htsum : ∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) =
        ∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) := by
      simp only [ha]
      exact rayCountTheta_fibre_tsum (qForm α γ l θ₁ θ₂) q hq t h96.1
    rw [htsum, ← hC]
    refine le_trans h96.2 ?_
    have hA : α ≤ α * γ := by nlinarith
    have hG : γ ≤ α * γ := by nlinarith
    have hP1 : 1 ≤ α * γ := by nlinarith
    have hsq : 1 ≤ Real.sqrt (α * γ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hP1
    have hsq0 : 0 < Real.sqrt (α * γ) := by linarith
    have hCπ : Real.pi / Real.sqrt (α * γ) ≤ Real.pi := div_le_self Real.pi_pos.le hsq
    have hC0 : 0 ≤ Real.pi / Real.sqrt (α * γ) := by positivity
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have key : 3 * Real.pi * (α * γ) ^ 2 ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 := by
      rw [hαγ]
      have h1 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 10 := pow_le_pow_right₀ hd1 (by norm_num)
      have h2 : (M : ℝ) ^ 8 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ hM1 (by norm_num)
      have hX : 0 ≤ (d : ℝ) ^ 10 * (M : ℝ) ^ 20 := by positivity
      calc 3 * Real.pi * ((d : ℝ) * (M : ℝ) ^ 4 / 4) ^ 2
          = (3 * Real.pi / 16) * ((d : ℝ) ^ 2 * (M : ℝ) ^ 8) := by ring
        _ ≤ 1 * ((d : ℝ) ^ 10 * (M : ℝ) ^ 20) :=
          mul_le_mul (by linarith [Real.pi_le_four]) (mul_le_mul h1 h2 (by positivity) (by positivity))
            (by positivity) (by norm_num)
        _ ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 := by
          rw [show (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 = 4 ^ 10 * ((d : ℝ) ^ 10 * (M : ℝ) ^ 20) by ring]
          linarith
    have hpoly : α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2 ≤ 3 * (α * γ) ^ 2 := by
      have e1 : α ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ (by linarith) hA 2
      have e2 : γ ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ (by linarith) hG 2
      have ht2 : t ^ 2 ≤ 1 := by nlinarith
      have e3 : α ^ 2 * γ ^ 2 * t ^ 2 ≤ (α * γ) ^ 2 := by
        calc α ^ 2 * γ ^ 2 * t ^ 2 = (α * γ) ^ 2 * t ^ 2 := by ring
          _ ≤ (α * γ) ^ 2 * 1 := mul_le_mul_of_nonneg_left ht2 (by positivity)
          _ = (α * γ) ^ 2 := by ring
      linarith
    calc Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2)
        = Real.pi / Real.sqrt (α * γ) * t * (α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2) := by
          field_simp
      _ ≤ Real.pi * t * (3 * (α * γ) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCπ ht0.le) hpoly (by positivity) (by positivity)
      _ = 3 * Real.pi * (α * γ) ^ 2 * t := by ring
      _ ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := mul_le_mul_of_nonneg_right key ht0.le

end GlobalTheory.Hk
end

section

open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

theorem tendsto_finCoeff_sum_jacobiTheta₂ : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im →
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
      GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ)
      Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  intro τ z hτ
  set t := cexp (π * I * τ) ^ 2 with ht
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_exp_pi_I_lt_one τ hτ
  have ht1 : ‖t‖ < 1 := by
    rw [ht, norm_pow]
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  obtain ⟨hlim, C, hC⟩ := GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded t ht1
  have hsum : Summable (fun j : ℤ => C * ‖jacobiTheta₂_term j z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).2 hτ).norm.mul_left C
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (n : ℕ) (j : ℤ) => finCoeff t n j * jacobiTheta₂_term j z τ)
    (g := fun j => jacobiTheta₂_term j z τ * (qPochInf t)⁻¹) hsum
    (fun j => by
      have := (hlim j).mul_const (jacobiTheta₂_term j z τ)
      simpa [mul_comm] using this)
    (Filter.Eventually.of_forall fun n j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n j) (norm_nonneg _))
  rw [tsum_mul_right] at hT
  refine hT.congr (fun n => ?_)
  apply tsum_eq_sum
  intro j hj
  have : ¬ j.natAbs ≤ n := by
    intro h
    apply hj
    rw [Finset.mem_Icc]
    omega
  simp [finCoeff, this]

end GlobalTheory.JacobiTriple
end

section

open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

theorem finTriple_sum_odd (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem finTriple_term (s x : ℂ) (hs : s ≠ 0) (hx : x ≠ 0) (n k : ℕ) (hk : k ≤ 2 * n) :
    (x⁻¹ ^ n * s ^ (n ^ 2)) *
        (qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * (x * s ^ ((1 : ℤ) - 2 * n)) ^ k) =
      finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
  have hc : finCoeff (s ^ 2) n ((k : ℤ) - n) = qBinom (s ^ 2) (2 * n) k := by
    unfold finCoeff
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [hc]
  have hkk : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases k with _ | k
    · simp
    · push_cast [Nat.add_sub_cancel]; ring
  have he : ((k : ℤ) - n) ^ 2 = ((n ^ 2 + k * (k - 1) : ℕ) : ℤ) + (1 - 2 * n) * k := by
    rw [Nat.cast_add, hkk]; push_cast; ring
  have hxz : x ^ ((k : ℤ) - n) = x ^ k * x⁻¹ ^ n := by
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow]
  rw [hxz, he, zpow_add₀ hs, zpow_natCast, zpow_mul, zpow_natCast, pow_add, mul_pow]
  ring

theorem finTriple (s x : ℂ) (hs : s ≠ 0) (hs1 : ‖s‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  set X := x * s ^ ((1 : ℤ) - 2 * n) with hX
  have ha : ∀ k ∈ Finset.range n, 1 + x * s ^ (2 * k + 1) = 1 + X * s ^ (2 * (n + k)) := by
    intro k _
    rw [hX, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs]
    congr 3
    push_cast; ring
  have hb : ∀ k ∈ Finset.range n, 1 + x⁻¹ * s ^ (2 * k + 1) =
      (x⁻¹ * s ^ (2 * k + 1)) * (1 + X * s ^ (2 * (n - 1 - k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e : ((2 * k + 1 : ℕ) : ℤ) + (1 - 2 * n) + ((2 * (n - 1 - k) : ℕ) : ℤ) = 0 := by omega
    have hab : x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k))) = 1 := by
      calc x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k)))
          = (x⁻¹ * x) * (s ^ ((2 * k + 1 : ℕ) : ℤ) * s ^ ((1 : ℤ) - 2 * n) *
              s ^ ((2 * (n - 1 - k) : ℕ) : ℤ)) := by
            rw [hX, zpow_natCast, zpow_natCast]; ring
        _ = 1 := by
            rw [inv_mul_cancel₀ hx, ← zpow_add₀ hs, ← zpow_add₀ hs, e, zpow_zero, one_mul]
    linear_combination -hab
  have hr : ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n - 1 - k))) =
      ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k)) :=
    Finset.prod_range_reflect (fun k => 1 + X * s ^ (2 * k)) n
  have hC : ∏ k ∈ Finset.range n, (x⁻¹ * s ^ (2 * k + 1)) = x⁻¹ ^ n * s ^ (n ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, finTriple_sum_odd]
  have hsplit : ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) =
      (∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))) *
        ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n + k))) := by
    rw [two_mul, Finset.prod_range_add]
  rw [Finset.prod_mul_distrib, Finset.prod_congr rfl ha, Finset.prod_congr rfl hb,
    Finset.prod_mul_distrib, hr, hC]
  calc _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) := by
        rw [hsplit]; ring
    _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∑ k ∈ Finset.range (2 * n + 1),
          qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * X ^ k := by
        rw [GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom s X hs1 (2 * n)]
    _ = ∑ k ∈ Finset.range (2 * n + 1),
          finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        exact finTriple_term s x hs hx n k (by omega)
    _ = _ := by
        refine Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - n) (fun j : ℤ => (j + n).toNat)
          ?_ ?_ ?_ ?_ ?_
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_range] at ha
          simp only [Finset.mem_coe, Finset.mem_Icc]; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          simp only [Finset.mem_coe, Finset.mem_range]; omega
        · intro a _; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          omega
        · intro a _; rfl

end GlobalTheory.JacobiTriple
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_sqrt_sub_one_le (x : ℝ) : |Real.sqrt (1 - x) - 1| ≤ |x| := by
  rcases le_or_gt (1 - x) 0 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    have : |(0:ℝ) - 1| = 1 := by norm_num
    rw [this]
    exact le_trans (by linarith) (le_abs_self x)
  · have h1 := Real.sq_sqrt h.le
    have h2 := Real.sqrt_nonneg (1 - x)
    set a := Real.sqrt (1 - x)
    have h3 : x = (1 - a) * (1 + a) := by linarith
    rw [h3, abs_mul, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 + a)]
    have := abs_nonneg (1 - a)
    nlinarith

theorem abs_qf_le {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ (∑ i, ‖z i‖) ^ 2 := by
  rw [qf_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (le_of_eq ?_) (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (z i)))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖z i‖)]
  rcases sg_eq i with h | h <;> simp [h]

theorem norm_exp_eq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp

theorem abs_sin_eq (x : ℝ) (h : |x| ≤ Real.pi) : |Real.sin x| = Real.sin |x| := by
  rcases le_total 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 h)
  · rw [abs_of_nonpos h0] at h ⊢
    rw [← abs_neg, ← Real.sin_neg]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h)

theorem exp_bounds (θ : ℝ) (h : |θ| ≤ Real.pi) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| ∧
    |θ| ≤ 2 * ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ∧
    (|θ| ≤ 2 → |θ| - |θ| ^ 3 / 16 ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖) := by
  have hp := Real.pi_pos
  have h0 := abs_nonneg θ
  have e1 : |θ / 2| = |θ| / 2 := by rw [abs_div]; norm_num
  rw [norm_exp_eq, abs_sin_eq _ (by rw [e1]; linarith), e1]
  set T := |θ|
  refine ⟨?_, ?_, fun h2 => ?_⟩
  · have := Real.sin_le (x := T / 2) (by linarith)
    linarith
  · have h1 := Real.mul_le_sin (x := T / 2) (by linarith) (by linarith)
    have h2 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) hp]
      have := Real.pi_le_four
      linarith
    nlinarith
  · rcases h0.eq_or_lt with h3 | h3
    · rw [← h3]; simp
    · have := Real.sin_gt_sub_cube (x := T / 2) (by linarith)
      nlinarith [pow_nonneg h0 3]

theorem polar_compare (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ)
    (ht : 1 < t) : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q',
      u.1 ∈ Set.Ioo (-Real.pi) Real.pi →
      (tanGauge u < t⁻¹ * r → ptGauge e (polarPt e u) < r) ∧
      (ptGauge e (polarPt e u) < r → tanGauge u < t * r) := by
  have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hti0 : 0 < t⁻¹ := inv_pos.2 (by linarith)
  have hd : (0 : ℝ) < min (1 / 2) (min ((t - 1) / 3) (1 - t⁻¹)) := by
    refine lt_min (by norm_num) (lt_min ?_ ?_) <;> linarith
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr u hu
  obtain ⟨hr0, hr1⟩ := hr
  rw [lt_min_iff, lt_min_iff] at hr1
  obtain ⟨hr1, hr2, hr3⟩ := hr1
  obtain ⟨b1, b2, b3⟩ := exp_bounds u.1 (abs_le.2 ⟨hu.1.le, hu.2.le⟩)
  have hq := abs_qf_le u.2
  have ha : |Real.sqrt (1 - sg (e none) * qf u.2) - 1| ≤ (∑ i, ‖u.2 i‖) ^ 2 := by
    refine (abs_sqrt_sub_one_le _).trans (le_trans (le_of_eq ?_) hq)
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> simp [h]
  have hN : |‖polarPt e u (e none) - 1‖ - ‖Complex.exp ((u.1 : ℂ) * Complex.I) - 1‖|
      ≤ (∑ i, ‖u.2 i‖) ^ 2 := by
    refine (abs_norm_sub_norm_le _ _).trans (le_trans (le_of_eq ?_) ha)
    rw [polarPt_none]
    set a := Real.sqrt (1 - sg (e none) * qf u.2)
    have : (a : ℂ) * Complex.exp ((u.1 : ℂ) * Complex.I) - 1 -
        (Complex.exp ((u.1 : ℂ) * Complex.I) - 1) =
        ((a - 1 : ℝ) : ℂ) * Complex.exp ((u.1 : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hS : 0 ≤ ∑ i, ‖u.2 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN0 := norm_nonneg (polarPt e u (e none) - 1)
  have hT := abs_nonneg u.1
  unfold tanGauge ptGauge
  simp only [polarPt_some]
  obtain ⟨n1, n2⟩ := abs_le.1 hN
  generalize ‖polarPt e u (e none) - 1‖ = N at *
  generalize ‖Complex.exp ((u.1 : ℂ) * Complex.I) - 1‖ = E at *
  generalize ∑ i, ‖u.2 i‖ = S at *
  generalize |u.1| = T at *
  constructor
  · intro h
    have h1 : t⁻¹ * r < r := by nlinarith
    have h2 : S ≤ r := by linarith
    have h3 : S ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hS h2 2
    nlinarith
  · intro h
    have h2 : S ≤ r := by linarith
    have h3 : S ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hS h2 2
    have h4 : r ^ 2 ≤ r := by nlinarith
    have h5 : T ≤ 4 * r := by linarith
    have h6 := b3 (by linarith)
    have h7 : T ^ 3 ≤ (4 * r) ^ 3 := pow_le_pow_left₀ hT h5 3
    have h8 : r ^ 3 ≤ r ^ 2 / 2 := by nlinarith [sq_nonneg r]
    have h9 : 3 * r ^ 2 ≤ (t - 1) * r := by nlinarith
    nlinarith

end GlobalTheory.PolarCompare
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.primeCount_relative_error_of_psi_relative_error : ∀ c₂ c₃ C cS : ℝ, 0 < c₂ → 0 < c₃ → 0 < C → 0 < cS → ∃ c₂' c₃' C' : ℝ, 0 < c₂' ∧ 0 < c₃' ∧ 0 < C' ∧ ∀ (B φ β : ℝ) (θ : ℤ) (P : ℕ → Prop), 3 ≤ B → 1 ≤ φ → φ ≤ B → (θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ cS / B ^ 3 ≤ 1 - β)) → (∀ u : ℝ, B ^ c₂ ≤ u → |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β))) → ∀ X : ℝ, B ^ c₂' ≤ X → |φ * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤ C' * (Real.exp (-c₃' * Real.log X / Real.log B) + Real.exp (-Real.sqrt (c₃' * Real.log X))) * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
  first | exact @GlobalTheory.Lin.pi_rel_of_psi_rel | exact GlobalTheory.Lin.pi_rel_of_psi_rel | (intros; apply GlobalTheory.Lin.pi_rel_of_psi_rel <;> assumption)
end

section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime : ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → S.NNBasis q b → ∃ (s : ℕ) (c : Fin r → Fin g → ℂ), Nat.Coprime s q ∧ (∀ j, c j ∈ S.La) ∧ (∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s : ℂ) else 0) ∧ ∀ x ∈ S.La, (s : ℂ) • x = ∑ j, beta S.d S.Hm x (b j) • c j := by
  first | exact @GlobalTheory.MomDual.dual_basis | exact GlobalTheory.MomDual.dual_basis | (intros; apply GlobalTheory.MomDual.dual_basis <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients : ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧ ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  first | exact @GlobalTheory.powerSum_second_main | exact GlobalTheory.powerSum_second_main | (intros; apply GlobalTheory.powerSum_second_main <;> assumption)
end
