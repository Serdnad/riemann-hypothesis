module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle003
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.step :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (w : Module.End ℤ_[l] X), GenBy l R X → InPow 2 (w - 1) →
      cokLen (w ^ l - 1) ≤ cokLen (w - 1) + R := by
  intro l _ X _ _ R w hG hw
  haveI : Module.Finite ℤ_[l] X := by
    obtain ⟨π, hπ⟩ := hG
    exact Module.Finite.of_surjective π hπ
  have h1 := (UpperTheory.V.Base.lenComp ℤ_[l] X (∑ i ∈ Finset.range l, w ^ i) (w - 1)).2
  rw [geom_sum_mul] at h1
  have h2 := cokLen_le_of_range_le (phi l X w hw)
  have h3 := cokL l X R hG
  calc cokLen (w ^ l - 1) ≤ cokLen (∑ i ∈ Finset.range l, w ^ i) + cokLen (w - 1) := h1
    _ ≤ R + cokLen (w - 1) := add_le_add_left (h2.trans h3) _
    _ = cokLen (w - 1) + R := add_comm _ _
end

section

open UpperTheory.V UpperTheory.V.PropA

private theorem padic_units_distance_le_max (l : ℕ) [Fact l.Prime] (a b : ℤ_[l]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (z : PadicAlgCl l) :
    ‖a - b‖ ≤ max ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l]) * z - 1‖
      ‖algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l]) * z - 1‖ := by
  set A := algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])
  set B := algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l])
  have hA : ‖A‖ = 1 := by
    simp only [A, PadicAlgCl.norm_extends, ← PadicInt.norm_def, ha]
  have hAB : ‖A - B‖ = ‖a - b‖ := by
    simp only [A, B, ← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, ← PadicInt.norm_def]
  have hdiff : A * z - 1 - (B * z - 1) = (A - B) * z := by ring
  have hmax : ‖A * z - 1 - (B * z - 1)‖ ≤ max ‖A * z - 1‖ ‖B * z - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max (A * z - 1) (-(B * z - 1))
    rwa [norm_neg, ← sub_eq_add_neg] at this
  rcases le_or_gt 1 ‖z‖ with hz | hz
  · calc ‖a - b‖ ≤ ‖a - b‖ * ‖z‖ := le_mul_of_one_le_right (norm_nonneg _) hz
      _ = ‖A * z - 1 - (B * z - 1)‖ := by rw [hdiff, norm_mul, hAB]
      _ ≤ _ := hmax
  · have hAz : ‖A * z‖ < 1 := by rw [norm_mul, hA, one_mul]; exact hz
    have h1 : (1 : ℝ) ≤ ‖A * z - 1‖ := by
      have := IsUltrametricDist.norm_add_le_max (A * z) (-(A * z - 1))
      rw [norm_neg, show A * z + -(A * z - 1) = 1 by ring, norm_one] at this
      rcases le_max_iff.mp this with h | h
      · exact absurd h (not_le.mpr hAz)
      · exact h
    calc ‖a - b‖ ≤ 1 := PadicInt.norm_le_one _
      _ ≤ ‖A * z - 1‖ := h1
      _ ≤ _ := le_max_left _ _

theorem UpperTheory.V.PropA.ball :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ∀ (j : ℕ) (z : PadicAlgCl l), ∃ s : ℤ_[l], ∀ e : ℕ,
      ((l : ℝ) ^ (j + c))⁻¹ * ‖s - e‖ ≤ ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ := by
  intro l _ u c hc j z
  obtain ⟨hu, -, hdist⟩ := lteNorm l u c hc
  have hK : (0 : ℝ) < (l : ℝ) ^ (j + c) := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  set r : ℕ → ℝ := fun e =>
    (l : ℝ) ^ (j + c) * ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ with hr
  have hunit : ∀ e : ℕ, ‖((u ^ l ^ j) ^ e : ℤ_[l])‖ = 1 := by
    intro e
    rw [← pow_mul, norm_pow, hu, one_pow]
  obtain ⟨s, hs⟩ := helly l (fun e : ℕ => (e : ℤ_[l])) r (by
    intro a b
    have key := padic_units_distance_le_max l _ _ (hunit a) (hunit b) z
    have h := hdist j a b
    have : ‖(a : ℤ_[l]) - b‖ = (l : ℝ) ^ (j + c) * ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    simp only [this, hr]
    rw [← mul_max_of_nonneg _ _ hK.le]
    exact mul_le_mul_of_nonneg_left key hK.le)
  refine ⟨s, fun e => ?_⟩
  have := hs e
  simp only [hr] at this
  rw [inv_mul_le_iff₀ hK]
  exact this
end
