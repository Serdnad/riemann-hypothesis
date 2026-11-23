module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle023

@[expose] public section

section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap :
    ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), IsIntAf (algebraMap ℚ (AfP p) q) → ∃ (r : ℕ) (z : ℤ), (p : ℚ) ^ r * q = z := by
  intro p hp q hq
  have hp' : p.Prime := hp.out
  obtain ⟨r, m, hmp, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp'.one_lt.ne'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hden
      exact absurd hden q.den_nz
    · exact h
  have hmc : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp').mpr hmp).symm
  have hint : IsIntAf (algebraMap ℚ (AfP p) q * (p : AfP p) ^ r) := by
    intro v
    rw [map_mul, map_pow, map_natCast]
    exact mul_mem (hq v) (pow_mem (natCast_mem _ p) r)
  have hnum : ((q.num : ℤ) : ℚ) = (m : ℚ) * (q * (p : ℚ) ^ r) := by
    rw [← Rat.mul_den_eq_num]
    have : (q.den : ℚ) = (p : ℚ) ^ r * m := by exact_mod_cast hden
    rw [this]
    ring
  have hdvd : (m : ℤ) ∣ q.num := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p m hm0 hmc q.num _ hint
    rw [hnum, map_mul, map_mul, map_pow, map_natCast, map_natCast]
  have h1 : m ∣ q.num.natAbs := Int.natCast_dvd.mp hdvd
  have h2 : m ∣ q.den := ⟨p ^ r, by rw [hden, mul_comm]⟩
  have hm1 : m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 q.reduced) h2
  refine ⟨r, q.num, ?_⟩
  rw [← Rat.mul_den_eq_num]
  have : (q.den : ℚ) = (p : ℚ) ^ r := by
    rw [hden, hm1, mul_one]
    push_cast
    rfl
  rw [this, mul_comm]
end

section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.integral_unit_congr_coprime_int_mod :
    ∀ (p : ℕ) [Fact p.Prime] (ε : (AfP p)ˣ), IsIntAf (ε : AfP p) → IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p) → ∀ n : ℕ, 0 < n → n.Coprime p → ∃ (ν : ℤ) (b : AfP p), IsIntAf b ∧ (ε : AfP p) = (ν : AfP p) + (n : AfP p) * b ∧ IsCoprime ν (n : ℤ) := by
  intro p _ ε hε hε' n hn hnp
  obtain ⟨ν, b, hb, hνb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε
  obtain ⟨μ, b', hb', hμb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε'
  refine ⟨ν, b, hb, hνb, ?_⟩
  have hint : IsIntAf ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    intro v
    simp only [map_add (f := _), map_mul, map_intCast, map_natCast]
    exact add_mem (add_mem (mul_mem (intCast_mem _ ν) (hb' v)) (mul_mem (intCast_mem _ μ) (hb v)))
      (mul_mem (mul_mem (natCast_mem _ n) (hb v)) (hb' v))
  have hprod : (1 : AfP p) = (ν : AfP p) * μ +
      n * ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    have : (ε : AfP p) * ((ε⁻¹ : (AfP p)ˣ) : AfP p) = 1 := Units.mul_inv ε
    rw [← this, hνb, hμb]
    ring
  have hdvd : (n : ℤ) ∣ 1 - ν * μ := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ _ hint
    rw [map_intCast, Int.cast_sub, Int.cast_one, Int.cast_mul]
    linear_combination hprod
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨μ, k, by linear_combination -hk⟩
end
