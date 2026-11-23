module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle024
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
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem re_lt_one_of_isLZero {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} {s : ℂ}
    (h : IsLZero χ s) : s.re < 1 := by
  by_contra hc
  push Not at hc
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h.1 hc h.2

theorem log_density_bound : Formalism.HermitianLattices.Ext.PrimesInProgressions.LogDensityM := by
  classical
  obtain ⟨C0, q0, h0⟩ := zero_count_first
  obtain ⟨C1, q1, h1⟩ := zero_count_second
  refine ⟨24, 10, |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ), ?_⟩
  intro M _ T σ S hM hT hσ hS hsp
  suffices key : (S.card : ℝ) ≤ (|C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ)) *
      ((M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ (10 : ℕ)) by
    have hpow : Real.log (M * T) ^ (10 : ℝ) = Real.log (M * T) ^ (10 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [hpow, mul_assoc]
    exact key
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX : (6 : ℝ) ≤ M * T := by nlinarith
  have hX0 : (0 : ℝ) < M * T := by linarith
  have hL : (1 : ℝ) ≤ Real.log (M * T) := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hL10 : (1 : ℝ) ≤ Real.log (M * T) ^ 10 := one_le_pow₀ hL
  have hq0 : (0 : ℝ) ≤ ((max q0 q1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hCnn : 0 ≤ |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ) := by positivity
  have htriv : (S.card : ℝ) ≤ 3 * (M * T) := by
    have h := trivial_bound M T S (by linarith) (fun p hp => (hS p hp).2.1) hsp
    have hMnn : (0 : ℝ) ≤ M := by linarith
    nlinarith
  rcases S.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hCnn (mul_nonneg (Real.rpow_nonneg hX0.le _) (by positivity))
  have hσ1 : σ ≤ 1 := by
    have h1' := re_lt_one_of_isLZero (hS p0 hp0).2.2
    linarith [(hS p0 hp0).1]
  have hR1 : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := Real.one_le_rpow (by linarith) (by linarith)
  have hP : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by nlinarith
  have hXP : σ < 3 / 4 → (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by
    intro hs
    have hXe : (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := by
      calc (M * T : ℝ) = (M * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    nlinarith
  have h0' := fun S hσ' hq => h0 M T σ S hM hT hσ' hq
  have h1' := fun S hσ' hq => h1 M T σ S hM hT hσ' hq
  simp only [mul_assoc] at h0' h1'
  set P := (M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 with hPdef
  have hP0 : (0 : ℝ) ≤ P := by linarith
  set q : ℝ := ((max q0 q1 : ℕ) : ℝ) with hqdef
  have hexp : (|C0| + |C1| + 3 + 3 * q) * P = |C0| * P + |C1| * P + 3 * P + 3 * q * P := by ring
  rw [hexp]
  have eC0 := mul_le_mul_of_nonneg_right (le_abs_self C0) hP0
  have eC1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hP0
  have a0 : 0 ≤ |C0| * P := mul_nonneg (abs_nonneg _) hP0
  have a1 : 0 ≤ |C1| * P := mul_nonneg (abs_nonneg _) hP0
  have aq : q ≤ q * P := by nlinarith
  by_cases hq : max q0 q1 ≤ qd M T
  · by_cases hσ34 : 3 / 4 ≤ σ
    · have hA0 := h0' (S.filter (fun p => p.1 = 1)) hσ34 (le_trans (le_max_left _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2⟩)
        (by
          intro p hp p' hp' hne
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm))
      have hA1 := h1' (S.filter (fun p => ¬ p.1 = 1)) hσ34 (le_trans (le_max_right _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2.2⟩)
        (by
          intro p hp p' hp' hne heq
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne heq)
      have hcast : (S.card : ℝ) = ((S.filter (fun p => p.1 = 1)).card : ℝ) +
          ((S.filter (fun p => ¬ p.1 = 1)).card : ℝ) := by
        rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
      linarith
    · push_neg at hσ34
      have := hXP hσ34
      linarith
  · push_neg at hq
    have hXq : (M * T : ℝ) < q := by
      refine lt_of_le_of_lt (Nat.le_ceil _) ?_
      rw [hqdef]
      unfold qd at hq
      exact_mod_cast hq
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem glue_aux {S A B y η E E' F : ℝ} (h : S ≤ A * y * η * E) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (hE : 0 ≤ E) (hEE : E ≤ E') (hF : 0 ≤ F) (hAB : A ≤ B) (hB : 0 ≤ B) :
    S ≤ B * y * η * (E' + F) := by
  have h1 : A * y * η * E ≤ B * y * η * E := by
    have : 0 ≤ y * η * E := by positivity
    nlinarith
  have h2 : B * y * η * E ≤ B * y * η * (E' + F) := by
    have : 0 ≤ B * y * η := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith

theorem glue_ranges : GlueOf := by
  rintro ⟨cA, c, A, hcA, hc, hA⟩ hB
  obtain ⟨c', A', C₀, hc', hB'⟩ := hB cA hcA
  refine ⟨min c c', max A 0 + max A' 0, C₀, lt_min hc hc', ?_⟩
  intro M _ h8 y hy hC
  have hM : 2 ≤ M := by
    have : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have := Nat.le_of_dvd this h8
    omega
  have hη : 0 ≤ etaOf M := (etaOf_pos M hM).le
  have hy0 : 0 ≤ y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hA0' : 0 ≤ max A' 0 := le_max_right _ _
  by_cases hr : Real.log M ≤ cA * Real.sqrt (Real.log y)
  · have h := hA M h8 y hy hr
    rw [add_comm (Real.exp _)]
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have : min c c' * Real.sqrt (Real.log y) ≤ c * Real.sqrt (Real.log y) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      linarith
    · have := le_max_left A 0
      linarith
  · have h := hB' M h8 y hy hC (not_le.mp hr)
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have h1 : min c c' * Real.log y ≤ c' * Real.log y :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hL
      have h2 : min c c' * Real.log y / Real.log M ≤ c' * Real.log y / Real.log M :=
        div_le_div_of_nonneg_right h1 hlM.le
      linarith
    · have := le_max_left A' 0
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
