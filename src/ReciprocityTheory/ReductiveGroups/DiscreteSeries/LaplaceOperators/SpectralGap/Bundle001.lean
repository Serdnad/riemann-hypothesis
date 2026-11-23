module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Bundle001
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

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NonvanishingHypotheses (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) ∧
    Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b ∧ Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b ∧
    Formalism.MainNotions.CayleySignature.LowGapGe h r b ∧
    GapLap (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h

def DSUnivStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, GapLap ε lam h →
  ∀ (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    Formalism.MainNotions.S.IsDS ε lam σ₁ → Formalism.MainNotions.S.IsDS ε lam σ₂ →
  ∀ w₁ : H₁, Formalism.MainNotions.S.IsLowUnit ε lam σ₁ w₁ →
    ∃ w₂ : H₂, Formalism.MainNotions.S.IsLowUnit ε lam σ₂ w₂ ∧
      ∀ g ∈ Formalism.MainNotions.S.UJset ε, ⟪w₂, σ₂ g w₂⟫_ℂ = ⟪w₁, σ₁ g w₁⟫_ℂ

def GapBigLapStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), Formalism.MainNotions.CayleySignature.RealPlaceNumericalSetting k r z c u v b → ∃ h : ℝ, NonvanishingHypotheses k r z c u v b h

def CayleyIndepStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (P₀ P : Mat k r), Formalism.MainNotions.S.IsCayleyU k r ε P₀ → Formalism.MainNotions.S.IsCayleyU k r ε P →
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ (P₀⁻¹ * g * P₀)) →
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ (P⁻¹ * g * P)) ∧
      Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P⁻¹ * g * P)) = Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P₀⁻¹ * g * P₀))

def BAtTargetStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ), NonvanishingHypotheses k r z c u v b h →
    BesselAll (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) u

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS
open scoped Matrix InnerProductSpace

theorem bridge_inv_mul (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : P⁻¹ * P = 1 := by
  have hu : IsUnit P := hP.1.1
  exact Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hu)

theorem bridge_conj (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * g * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε ∧ P⁻¹ * (P * g * P⁻¹) * P = g := by
  have hPi : P⁻¹ * P = 1 := bridge_inv_mul k r ε P hP
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have e1 : Pᴴ * P = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  have e2 : P * Pᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  refine ⟨?_, ?_⟩
  · show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
    rw [hinv]
    calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
        = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
          rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [e2]; simp
  · calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp [Matrix.mul_assoc]
      _ = g := by rw [hPi]; simp

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
