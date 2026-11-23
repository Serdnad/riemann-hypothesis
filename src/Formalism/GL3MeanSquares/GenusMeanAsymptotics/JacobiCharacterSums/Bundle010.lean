module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.GL3MeanSquares.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqOrth
public import Mathlib.Algebra.Order.Field.GeomSum
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.Primorial

@[expose] public section

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

def clsB (m₀ s a₀ : ℕ) : Finset ℕ :=
  (range (m₀ * s)).filter (fun b => b % m₀ = a₀ % m₀ ∧ b.Coprime s)

def smallCnt (X : ℝ) (M b : ℕ) : ℕ :=
  (((Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).filter (fun p => p % M = b)).card

theorem sum_jacobiSym_eq_sum_residueClass (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) :
    ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) =
      ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ) := by
  have hM : 0 < m₀ * s := Nat.mul_pos hm hs
  have : NeZero s := ⟨hs.ne'⟩
  have hcongr : ∀ q : ℕ, (jacobiSym (q : ℤ) s : ℝ) = (jacobiSym ((q % (m₀ * s) : ℕ) : ℤ) s : ℝ) := by
    intro q
    have h : q ≡ q % (m₀ * s) [MOD s] :=
      Nat.ModEq.of_dvd (dvd_mul_left s m₀) (Nat.mod_modEq q (m₀ * s)).symm
    rw [jacobi_congr h]
  have hzero : ∀ q ∈ PPset m₀ a₀ X, q % (m₀ * s) ∉ clsB m₀ s a₀ →
      (jacobiSym (q : ℤ) s : ℝ) = 0 := by
    intro q hq hnot
    have hqm : q % m₀ = a₀ % m₀ := (Finset.mem_filter.mp hq).2.2.1
    have hnc : ¬ q.Coprime s := by
      intro hc
      apply hnot
      simp only [clsB, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hM, by rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), hqm], ?_⟩
      have hg := (Nat.ModEq.of_dvd (dvd_mul_left s m₀) (Nat.mod_modEq q (m₀ * s))).gcd_eq
      rw [Nat.Coprime, hg]
      exact hc
    have h0 : jacobiSym (q : ℤ) s = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hnc
    rw [h0]
    simp
  symm
  calc ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)
      = ∑ b ∈ clsB m₀ s a₀, ∑ q ∈ PPset m₀ a₀ X,
          if q % (m₀ * s) = b then (jacobiSym (q : ℤ) s : ℝ) else 0 := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hqb := (Finset.mem_filter.mp hq).2
        rw [hcongr q, hqb]
        simp
    _ = ∑ q ∈ PPset m₀ a₀ X, ∑ b ∈ clsB m₀ s a₀,
          if q % (m₀ * s) = b then (jacobiSym (q : ℤ) s : ℝ) else 0 := Finset.sum_comm
    _ = ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.sum_ite_eq]
        by_cases h : q % (m₀ * s) ∈ clsB m₀ s a₀
        · rw [if_pos h]
        · rw [if_neg h, hzero q hq h]

theorem cnt_add_small (m₀ s a₀ : ℕ) (X : ℝ) (b : ℕ) (hb : b ∈ clsB m₀ s a₀) :
    ((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card + smallCnt X (m₀ * s) b = piAP X (m₀ * s) b := by
  obtain ⟨hbr, hbm, -⟩ : b < m₀ * s ∧ b % m₀ = a₀ % m₀ ∧ b.Coprime s := by
    simpa [clsB] using hb
  have hbM : b % (m₀ * s) = b := Nat.mod_eq_of_lt hbr
  have hmod : ∀ p : ℕ, p % (m₀ * s) = b → p % m₀ = a₀ % m₀ := fun p h => by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_right m₀ s), h, hbm]
  have key := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p % (m₀ * s) = b))
    (fun p : ℕ => X ^ (1 / 2 : ℝ) < (p : ℝ))
  unfold piAP
  rw [hbM, ← key]
  congr 1
  · congr 1
    ext p
    simp only [PPset, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, hmod p h5, h4⟩, h5⟩
  · unfold smallCnt
    congr 1
    ext p
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, h4⟩, h5⟩

private theorem sum_card_filter_mod_le_card (T B : Finset ℕ) (M : ℕ) :
    ∑ b ∈ B, (T.filter (fun p => p % M = b)).card ≤ T.card := by
  calc ∑ b ∈ B, (T.filter (fun p => p % M = b)).card
      = ∑ b ∈ B, ∑ p ∈ T, if p % M = b then 1 else 0 := by simp only [Finset.card_filter]
    _ = ∑ p ∈ T, ∑ b ∈ B, if p % M = b then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ T, if p % M ∈ B then 1 else 0 := by simp only [Finset.sum_ite_eq]
    _ ≤ ∑ p ∈ T, 1 := Finset.sum_le_sum (fun p _ => by split_ifs <;> simp)
    _ = T.card := by simp

theorem sum_small_le (m₀ s a₀ : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∑ b ∈ clsB m₀ s a₀, (smallCnt X (m₀ * s) b : ℝ)) ≤ X ^ (1 / 2 : ℝ) := by
  have h1 : ∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b ≤
      ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card :=
    sum_card_filter_mod_le_card _ _ _
  have h2 : ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card ≤ ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    calc _ ≤ (Finset.Icc (1 : ℕ) ⌊X ^ (1 / 2 : ℝ)⌋₊).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.1, Nat.le_floor hp.2.2⟩
      _ = ⌊X ^ (1 / 2 : ℝ)⌋₊ := by simp
  have h3 : (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX _)
  have h4 : ((∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b : ℕ) : ℝ) ≤ (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast h1.trans h2
  push_cast at h4
  linarith

theorem sum_cnt_le (m₀ s a₀ : ℕ) (X : ℝ) :
    (∑ b ∈ clsB m₀ s a₀, (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)) ≤
      ((PPset m₀ a₀ X).card : ℝ) := by
  exact_mod_cast sum_card_filter_mod_le_card (PPset m₀ a₀ X) (clsB m₀ s a₀) (m₀ * s)

theorem abs_jac_le (a : ℤ) (s : ℕ) : |(jacobiSym a s : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a s with h | h | h <;> simp [h]

theorem main_le_two_pi {P m k : ℝ} (hP : 0 ≤ P) (hk : |k| ≤ 1 / 2) (h : |P - m| ≤ k * m) :
    |m| ≤ 2 * P ∧ |P - m| ≤ 2 * |k| * P := by
  have h0 : k * m ≤ |k| * |m| := by rw [← abs_mul]; exact le_abs_self _
  have h1 : |k| * |m| ≤ 1 / 2 * |m| := mul_le_mul_of_nonneg_right hk (abs_nonneg m)
  have h2 : |m| - |P| ≤ |m - P| := abs_sub_abs_le_abs_sub m P
  rw [abs_sub_comm, abs_of_nonneg hP] at h2
  have hm : |m| ≤ 2 * P := by linarith
  refine ⟨hm, ?_⟩
  have h3 : |k| * |m| ≤ |k| * (2 * P) := mul_le_mul_of_nonneg_left hm (abs_nonneg k)
  linarith

private theorem twist_decomposition_bound_of_sum_bounds (C : Finset ℕ) (J N S main : ℕ → ℝ) (k A B : ℝ)
    (hJ : ∀ b, |J b| ≤ 1) (hS0 : ∀ b, 0 ≤ S b)
    (hNb : ∀ b ∈ C, |N b + S b - main b| ≤ 2 * |k| * (N b + S b))
    (hMb : ∀ b ∈ C, |main b| ≤ 2 * (N b + S b))
    (hN : ∑ b ∈ C, N b ≤ A) (hS : ∑ b ∈ C, S b ≤ B) :
    |∑ b ∈ C, J b * N b - ∑ b ∈ C, J b * main b| ≤ 2 * |k| * (A + B) + B ∧
      ∑ b ∈ C, |main b| ≤ 2 * (A + B) := by
  have hk := abs_nonneg k
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have step : ∀ b ∈ C, |J b * N b - J b * main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) := by
      intro b hb
      rw [← mul_sub, abs_mul]
      have h' := abs_le.mp (hNb b hb)
      have e : |N b - main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) :=
        abs_le.mpr ⟨by linarith [h'.1, hS0 b], by linarith [h'.2, hS0 b]⟩
      calc |J b| * |N b - main b| ≤ 1 * |N b - main b| :=
            mul_le_mul_of_nonneg_right (hJ b) (abs_nonneg _)
        _ = |N b - main b| := one_mul _
        _ ≤ _ := e
    refine (Finset.sum_le_sum step).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hA := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * |k|)
    have hB := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 2 * |k|)
    linarith
  · calc ∑ b ∈ C, |main b| ≤ ∑ b ∈ C, 2 * (N b + S b) := Finset.sum_le_sum hMb
      _ = 2 * (∑ b ∈ C, N b + ∑ b ∈ C, S b) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (A + B) := by linarith

theorem twist_decomp (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) (hX : 0 ≤ X)
    (main : ℕ → ℝ) (k : ℝ) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - main b| ≤ k * main b) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) -
        ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * main b| ≤
      2 * |k| * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) ∧
    ∑ b ∈ clsB m₀ s a₀, |main b| ≤ 2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) := by
  have hmain := twist_decomposition_bound_of_sum_bounds (clsB m₀ s a₀) (fun b => (jacobiSym (b : ℤ) s : ℝ))
    (fun b => (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ))
    (fun b => (smallCnt X (m₀ * s) b : ℝ)) main k ((PPset m₀ a₀ X).card : ℝ) (X ^ (1 / 2 : ℝ))
    (fun b => abs_jac_le _ _) (fun b => Nat.cast_nonneg _)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).2
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).1
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (sum_cnt_le m₀ s a₀ X) (sum_small_le m₀ s a₀ X hX)
  rw [sum_jacobiSym_eq_sum_residueClass m₀ s a₀ X hm hs]
  exact hmain

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      2 * Real.log 4 * Real.log (2 * y) / y := by
  have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
  have hL0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hy2pos : 0 < (y:ℝ) ^ 2 := by positivity
  have hterm : ∀ p ∈ (Ioc y (2 * y)).filter Nat.Prime,
      Real.log p ^ 2 / (p : ℝ) ^ 2 ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
    have hp1 : (y:ℝ) < p := by exact_mod_cast h1
    have hp2 : (p:ℝ) ≤ 2 * y := by exact_mod_cast h2
    have hppos : (0:ℝ) < p := by linarith
    have hp2pos : 0 < (p:ℝ) ^ 2 := by positivity
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hlle : Real.log p ≤ Real.log (2 * y) := Real.log_le_log hppos hp2
    have hyp : (y:ℝ) ^ 2 ≤ (p:ℝ) ^ 2 := by nlinarith
    have hnum : 0 ≤ Real.log (2 * y) * Real.log p := mul_nonneg hL0 hlp
    calc Real.log p ^ 2 / (p:ℝ) ^ 2 = Real.log p * Real.log p / (p:ℝ) ^ 2 := by ring
      _ ≤ Real.log (2 * y) * Real.log p / (p:ℝ) ^ 2 := by
          gcongr ?_ * _ / _
      _ ≤ Real.log (2 * y) * Real.log p / (y:ℝ) ^ 2 := by
          gcongr _ / ?_
      _ = Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by ring
  have hsum : ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ≤ 2 * y * Real.log 4 := by
    have hsub : (Ioc y (2 * y)).filter Nat.Prime ⊆ (Finset.range (2 * y + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.range (2 * y + 1)).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Real.log (primorial (2 * y)) := by
          rw [primorial, Nat.cast_prod, Real.log_prod]
          intro p hp
          rw [Finset.mem_filter] at hp
          exact_mod_cast hp.2.ne_zero
      _ ≤ Real.log (4 ^ (2 * y)) := by
          apply Real.log_le_log
          · exact_mod_cast primorial_pos (2 * y)
          · exact_mod_cast primorial_le_four_pow (2 * y)
      _ = 2 * y * Real.log 4 := by
          rw [Real.log_pow]
          push_cast
          ring
  calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p :=
        Finset.sum_le_sum hterm
    _ = Real.log (2 * y) / (y:ℝ) ^ 2 * ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * (2 * y * Real.log 4) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hL0 (sq_nonneg _))
    _ = 2 * Real.log 4 * Real.log (2 * y) / y := by
        field_simp

theorem sum_log_sq_div_sq_primes_tail_le (N : ℕ) : ∀ d y : ℕ, 1 ≤ y → N - y ≤ d →
    ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
  intro d
  induction d with
  | zero =>
    intro y hy hd
    have hN : N ≤ y := by omega
    rw [Finset.Ioc_eq_empty_of_le hN, Finset.filter_empty, Finset.sum_empty]
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4) (by linarith)) (by positivity)
  | succ d ih =>
    intro y hy hd
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hy0 : (0:ℝ) < y := by linarith
    have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) hy0'
    have hblock := sum_log_sq_div_sq_primes_dyadic_le y hy
    by_cases hN : N ≤ 2 * y
    · have hsub : (Ioc y N).filter Nat.Prime ⊆ (Ioc y (2 * y)).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hN)
      calc ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ 2 * Real.log 4 * Real.log (2 * y) / y := hblock
        _ ≤ 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            gcongr ?_ / _
            rw [hlog2y]
            nlinarith [mul_nonneg hl4 hly, mul_nonneg hl4 hl2]
    · push_neg at hN
      have hsplit : (Ioc y N).filter Nat.Prime =
          (Ioc y (2 * y)).filter Nat.Prime ∪ (Ioc (2 * y) N).filter Nat.Prime := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) hN.le]
      have hdisj : Disjoint ((Ioc y (2 * y)).filter Nat.Prime) ((Ioc (2 * y) N).filter Nat.Prime) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_Ioc] at ha hb
        omega
      have ht := ih (2 * y) (by omega) (by omega)
      rw [hsplit, Finset.sum_union hdisj]
      calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 +
            ∑ p ∈ (Ioc (2 * y) N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ 2 * Real.log 4 * Real.log (2 * y) / y +
            4 * Real.log 4 * (Real.log ((2 * y : ℕ) : ℝ) + 2 * Real.log 2) / ((2 * y : ℕ) : ℝ) :=
            add_le_add hblock ht
        _ = 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            push_cast
            rw [hlog2y]
            field_simp <;> ring

theorem sP_cN_nonneg (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ sP (cN x) N p := by
  unfold sP cN
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

theorem sP_cN_le_log_div (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) (hp : p.Prime) :
    sP (cN x) N p ≤ 2 * x * Real.log p / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp2
  have hppos : (0:ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set r : ℝ := 1 / (p:ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hppos]; linarith
  have hrh : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hpR
  have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Icc 1 N).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpp, hmf⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p = q := by
      have h1 : p ∣ q ^ k := by rw [← hmf]; exact Nat.minFac_dvd _
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
    subst hpq
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    have hlt := Nat.lt_pow_self (by omega : 1 < p) (n := k)
    exact le_of_lt (lt_of_lt_of_le hlt hnN)
  have h1 : sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      Real.log p * (x / n) := by
    unfold sP
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_filter] at hn
    unfold cN
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn.2.1, hn.2.2]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
  calc sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
        Real.log p * (x / n) := h1
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * (x / n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => mul_nonneg hlog (div_nonneg hx (Nat.cast_nonneg n)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * x * r ^ k := by
        rw [Finset.sum_image (Nat.pow_right_injective hp2).injOn]
        apply Finset.sum_congr rfl
        intro k _
        show Real.log p * (x / ((p ^ k : ℕ) : ℝ)) = Real.log p * x * r ^ k
        rw [hr, Nat.cast_pow, one_div, inv_pow]
        ring
    _ ≤ ∑ k ∈ Ico 1 (N + 1), Real.log p * x * r ^ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_Ico]
          omega
        · intro k _ _
          exact mul_nonneg (mul_nonneg hlog hx) (pow_nonneg hr0 k)
    _ = Real.log p * x * ∑ k ∈ Ico 1 (N + 1), r ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.log p * x * (r ^ 1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (mul_nonneg hlog hx)
    _ ≤ Real.log p * x * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog hx)
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith
    _ = 2 * x * Real.log p / p := by rw [hr]; ring

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
