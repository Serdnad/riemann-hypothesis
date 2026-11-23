module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle008
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle003
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle007
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle016
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle010
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RectShiftChi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006

@[expose] public section

section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem zero_density_box : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox :=
  final_bound_of_assembly (coefficient_square_bound Formalism.FX.divisor_weight_bound) (zero_detection mollifier_identity)
    (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem hH_eq_harmonic' (k : ℕ) : hH k = ((harmonic k : ℚ) : ℝ) := by
  unfold hH
  rw [harmonic_eq_sum_Icc,
    show Finset.Ioc 0 k = Finset.Icc 1 k by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
  push_cast
  rfl

theorem term_bound (N U b : ℕ) (hb : 1 ≤ b) (hbU : b ≤ U) (hUN : U * U ≤ N) :
    |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)| ≤ 2 * b / N := by
  have hbpos : 0 < b := by omega
  have hbb : b * b ≤ N := le_trans (Nat.mul_le_mul hbU hbU) hUN
  have hk1 : 1 ≤ N / b := by
    rw [Nat.le_div_iff_mul_le hbpos]
    nlinarith
  have hdm := Nat.div_add_mod N b
  have hml := Nat.mod_lt N hbpos
  have hkb : N / b * b ≤ N := Nat.div_mul_le_self N b
  have hNlt : N < (N / b + 1) * b := by nlinarith
  have hk0 : N / b ≠ 0 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by nlinarith)
  have hkR : (1 : ℝ) ≤ ((N / b : ℕ) : ℝ) := by exact_mod_cast hk1
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hkbR : ((N / b : ℕ) : ℝ) * b ≤ N := by exact_mod_cast hkb
  have hNltR : (N : ℝ) < (((N / b : ℕ) : ℝ) + 1) * b := by exact_mod_cast hNlt
  have hHk : hH (N / b) = ((harmonic (N / b) : ℚ) : ℝ) := hH_eq_harmonic' (N / b)
  have hA1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (N / b)
  have hA2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (N / b)
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, hk0, if_false] at hA1 hA2
  rw [← hHk] at hA1 hA2
  set K : ℝ := ((N / b : ℕ) : ℝ) with hK
  have hlog1 : Real.log (K + 1) - Real.log K ≤ 1 / K := by
    rw [← Real.log_div (by positivity) (by positivity), add_div, div_self (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / K by positivity)
    linarith
  have hlogB1 : Real.log K + Real.log b - Real.log N ≤ 0 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    linarith [Real.log_le_log (by positivity) hkbR]
  have hlogB2 : -(1 / K) ≤ Real.log K + Real.log b - Real.log N := by
    have h1 : Real.log N < Real.log ((K + 1) * b) := Real.log_lt_log hN0 hNltR
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hfin : 1 / K ≤ 2 * b / N := by
    rw [le_div_iff₀ hN0, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

theorem cF_main (hχ : χ ≠ 1) (N U : ℕ) (hU : 1 ≤ U) (hUN : U * U ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U)‖ ≤
      2 * U / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by
  have hUle : U ≤ N := le_trans (Nat.le_mul_of_pos_left U (by omega)) hUN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  rw [cF_split χ N U hUle]
  have hX : (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U) =
      ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) *
        (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ) := by
    unfold cS cT
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  rw [hX]
  have hre : ∀ A B C : ℂ, A + B - C = (A - C) + B := fun A B C => by ring
  rw [hre, ← Finset.sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ Ioc 0 U, ‖χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) - χ (b : ZMod q) / (b : ℂ) *
          (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ)‖
        ≤ ∑ b ∈ Ioc 0 U, 2 / (N : ℝ) := by
          apply Finset.sum_le_sum
          intro b hb
          rw [Finset.mem_Ioc] at hb
          have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.1
          rw [← mul_sub, norm_mul, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast]
          have h1 := term_bound N U b hb.1 hb.2 hUN
          have h2 : ‖χ (b : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          calc ‖χ (b : ZMod q)‖ / b * |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)|
              ≤ 1 / b * (2 * b / N) := by gcongr
            _ = 2 / N := by field_simp
      _ = 2 * U / N := by simp; ring
  · have htail : ∀ a ∈ Ioc 0 N, ‖∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖ ≤ 8 * ((q : ℝ) + 1) / U := by
      intro a ha
      by_cases hM : N / a ≤ U
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        positivity
      · push_neg at hM
        have hsplit : ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) = cS χ (N / a) - cS χ U := by
          unfold cS
          rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hM.le]
          ring
        rw [hsplit]
        have h1 := cS_approx χ hχ U hU
        have h2 := cS_approx χ hχ (N / a) (by omega)
        have hMR : (U : ℝ) ≤ ((N / a : ℕ) : ℝ) := by exact_mod_cast hM.le
        have h3 : 4 * ((q : ℝ) + 1) / ((N / a : ℕ) : ℝ) ≤ 4 * ((q : ℝ) + 1) / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hMR
        calc ‖cS χ (N / a) - cS χ U‖ = ‖(DirichletCharacter.LFunction χ 1 - cS χ U) -
              (DirichletCharacter.LFunction χ 1 - cS χ (N / a))‖ := by
              congr 1
              ring
          _ ≤ ‖DirichletCharacter.LFunction χ 1 - cS χ U‖ +
              ‖DirichletCharacter.LFunction χ 1 - cS χ (N / a)‖ := norm_sub_le _ _
          _ ≤ 4 * ((q : ℝ) + 1) / U + 4 * ((q : ℝ) + 1) / U := add_le_add h1 (h2.trans h3)
          _ = 8 * ((q : ℝ) + 1) / U := by ring
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Ioc 0 N, ‖((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖
        ≤ ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (8 * ((q : ℝ) + 1) / U) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (htail a ha) (by positivity)
      _ = hH N * (8 * ((q : ℝ) + 1) / U) := by rw [hH, Finset.sum_mul]
      _ ≤ (1 + Real.log N) * (8 * ((q : ℝ) + 1) / U) := by
          have hh : hH N ≤ 1 + Real.log N := by
            rw [hH_eq_harmonic']
            exact harmonic_le_one_add_log N
          exact mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by ring

theorem cF_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N))‖ ≤
      26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by
  have hU : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
  have hUN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hlt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hUR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hU
  have hs0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNR
  have hsq : √(N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
    have h := Real.sqrt_lt_sqrt (by positivity)
      (show (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) by exact_mod_cast hlt)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hsq2 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    have h := Real.sqrt_le_sqrt (show ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) ≤ N by exact_mod_cast hUN)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hc : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by linarith
  have h1 := cF_main χ hχ N (Nat.sqrt N) hU hUN
  have h2 := cS_approx χ hχ (Nat.sqrt N) hU
  have hdec : cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N)) =
      (cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) - cT χ (Nat.sqrt N))) +
        ((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1) := by
    ring
  rw [hdec]
  have hw : 1 / (Nat.sqrt N : ℝ) ≤ 2 * (1 / √(N : ℝ)) := by
    have h := one_div_le_one_div_of_le hs0 (show √(N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) by linarith)
    calc 1 / (Nat.sqrt N : ℝ) = 2 * (1 / (2 * (Nat.sqrt N : ℝ))) := by field_simp
      _ ≤ 2 * (1 / √(N : ℝ)) := by linarith
  have hv : (Nat.sqrt N : ℝ) / N ≤ 1 / √(N : ℝ) := by
    calc (Nat.sqrt N : ℝ) / N = (Nat.sqrt N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by
          rw [Real.mul_self_sqrt hNR.le]
      _ ≤ √(N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by gcongr
      _ = 1 / √(N : ℝ) := by field_simp
  calc _ ≤ ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) -
          cT χ (Nat.sqrt N))‖ + ‖((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1)‖ := norm_add_le _ _
    _ ≤ (2 * (Nat.sqrt N : ℝ) / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / (Nat.sqrt N : ℝ)) +
          (Real.log N + Real.eulerMascheroniConstant) * (4 * ((q : ℝ) + 1) / (Nat.sqrt N : ℝ)) := by
        refine add_le_add h1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left h2 hc
    _ = 2 * ((Nat.sqrt N : ℝ) / N) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (1 / (Nat.sqrt N : ℝ)) := by
        ring
    _ ≤ 2 * (1 / √(N : ℝ)) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (2 * (1 / √(N : ℝ))) := by
        gcongr
    _ ≤ 26 * ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) := by
        have hZ : 0 ≤ 1 / √(N : ℝ) := by positivity
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        have a3 : ((q : ℝ) + 1) * (1 / √(N : ℝ)) * Real.eulerMascheroniConstant ≤
            ((q : ℝ) + 1) * (1 / √(N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hγ1 (by positivity)
        have a4 : 1 * (1 / √(N : ℝ)) ≤ ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hZ
        nlinarith
    _ = 26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_geom (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]

lemma dhl_core (hCau : DHCauchy) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 150 * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          150 * (Real.log K + 2) * Real.log X * 25 ^ k := by
  have hB1 : 1 ≤ K * X ^ 2 := by nlinarith
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2)
    (by norm_num) hB1 hf.differentiableOn hf0
    (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))
  have hlog := dhl_log K X hK hX
  have hlog0 : 0 ≤ Real.log (K * X ^ 2) := Real.log_nonneg hB1
  refine ⟨Z, m, ?_, hm, ?_, ?_⟩
  · intro ρ
    rw [hZ ρ, Metric.mem_closedBall, dist_eq]
    norm_num
  · refine hsum.trans ?_
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro k s hs hfs
    have := hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs
    refine this.trans ?_
    have e : (72 * Real.log (K * X ^ 2) / (12 / 25) * (12 / (12 / 25)) ^ k : ℝ)
        = 150 * Real.log (K * X ^ 2) * 25 ^ k := by
      norm_num; ring
    rw [e]
    have : (0 : ℝ) < 25 ^ k := by positivity
    nlinarith

lemma dhl_z0re (t : ℝ) : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
  simp

lemma dhl_inv (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) :
    1 ≤ 26 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
  have h := inverseBound M ψ ((26 / 25 : ℂ) + t * I) (by rw [dhl_z0re]; norm_num)
  rw [dhl_z0re] at h
  have hne : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ
      (Or.inr (by intro h; have := congrArg Complex.re h; rw [dhl_z0re] at this; norm_num at this))
      (by rw [dhl_z0re]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := norm_pos_iff.mpr hne
  rw [inv_le_comm₀ hpos (by norm_num)] at h
  norm_num at h
  linarith

def DHLocalAt (C : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) : Prop :=
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

lemma dhl_X (M : ℕ) (t : ℝ) (hM : 3 ≤ M) : 3 ≤ (M : ℝ) * (|t| + 2) := by
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [abs_nonneg t]

lemma dhl_nontriv (hCau : DHCauchy) (C0 K : ℝ)
    (hC0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C0 * q * (1 + ‖s‖))
    (hK1 : 1 ≤ K) (hK : 52 * C0 ≤ K) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1)
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M ψ t := by
  have hX := dhl_X M t hM
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hinv := dhl_inv M ψ t
  have hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hinv; norm_num at hinv
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := dhl_core hCau (DirichletCharacter.LFunction ψ) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by
      intro z hz
      obtain ⟨hre, hn⟩ := dhl_geom t z hz
      have h1 := hC0 M ψ hψ z hre
      have hz0 := norm_nonneg z
      have ht := abs_nonneg t
      calc ‖DirichletCharacter.LFunction ψ z‖ ≤ C0 * M * (1 + ‖z‖) := h1
        _ ≤ (K / 52) * M * (1 + ‖z‖) := by
            have : C0 ≤ K / 52 := by linarith
            gcongr
        _ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr
        _ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring
        _ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
            have hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2 := by nlinarith
            have : (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by linarith
            gcongr)
  refine ⟨Z, m, ?_, hm, ?_, hsum, ?_⟩
  · intro ρ
    rw [hZ ρ]
    exact and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)
  · intro ρ hρ
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon)
      ((hZ ρ).mp hρ).2
  · intro k s hs1 hs
    have h := hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)
    rw [if_neg hψ, sub_zero]
    exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_shift_alg (S R V0 V1 E a b : ℂ) (hS : S = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    (2 * Real.pi : ℂ) * (S - R) = E + I * (a - b) + V1 := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hS, mul_sub, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  linear_combination (-I) * hrect + (V0 - V1 - 2 * Real.pi * R) * Complex.I_sq

theorem tail_shift_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ₁ T : ℝ)
    (hy : 1 ≤ y) (hσ₁ : 0 < σ₁) (hσ₁' : σ₁ < 1) (hT : 0 < T)
    (hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T → DirichletCharacter.LFunction χ w ≠ 0) :
    (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y) =
      (∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      + I * ((∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (T : ℂ) * I))
      + ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y ((σ₁ : ℂ) + (u : ℂ) * I) := by
  obtain ⟨hint, hS⟩ := Formalism.ZeroFreeDirichlet.perron_formula_character N χ y hy 2 (by norm_num)
  have hrect := Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character N χ hχ y (by linarith) σ₁ 2 T ∅ hσ₁ hσ₁' (by norm_num) hT
    (by simp) (fun w h1 h2 h3 hL => absurd hL (hzf w h1 h2 h3)) (by simp)
  simp only [Finset.sum_empty, sub_zero] at hrect
  unfold Formalism.ZF.rectInt at hrect
  rw [← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint,
    ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)] at hS
  exact tail_shift_alg _ _ _ _ _ _ _ hS hrect

end Formalism.HermitianLattices.Ext.BoxTail
end
end
