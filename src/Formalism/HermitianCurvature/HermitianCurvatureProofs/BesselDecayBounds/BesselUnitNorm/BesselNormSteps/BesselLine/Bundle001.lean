module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.Bundle001

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

theorem fdegH_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μG : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {d : ℝ}
    (hS : 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w : H} (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, h⟩ := hS
  obtain ⟨_, heq⟩ := h w w w w
  have h1 : ∀ x : Mt k r, ⟪w, σ (Matrix.of x) w⟫_ℂ * star ⟪w, σ (Matrix.of x) w⟫_ℂ =
      ((‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    have h3 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [← h1]
      rw [heq, inner_self_eq_norm_sq_to_K, Complex.ofReal_div, Complex.ofReal_pow]
      ring_nf
      try exact mul_comm _ _
    exact_mod_cast h3
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  show ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = d
  rw [hR]
  field_simp

end PI.WBL.FSW
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conj_mem_UJ {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hJ := hP.1.2
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * _ * (P * g * P⁻¹) = _
  have e1 : (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) =
      (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg', ← hJ]
  calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hinv']; simp

theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) (g : Mx k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [hinv]; simp

theorem ds_rep {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
      (∀ a ∈ UH (Hpk k r), ∀ v : H, ‖σ a v‖ = ‖v‖) ∧
      ∀ v : H, ContinuousOn (fun g => σ g v) (UH (Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, -⟩ := hDS
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hinv] using h1
  · intro a ha b hb
    have h := hmul _ (conj_mem_UJ hP ha) _ (conj_mem_UJ hP hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (a * b) * P⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    simp only [e, conj_back hP] at h
    exact h
  · intro a ha v
    have h := hnorm _ (conj_mem_UJ hP ha) v
    simp only [conj_back hP] at h
    exact h
  · intro v
    have hc : Continuous (fun g : Mx k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h := (hcont v).comp hc.continuousOn (fun g hg => conj_mem_UJ hP hg)
    refine h.congr (fun g _ => ?_)
    show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
    rw [conj_back hP]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end PI.WBL.FSW
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

section Generic

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def beF (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w v : H) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def be (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) : Wp →L[ℂ] Wp :=
  ∫ p, beF z c π σ w v p ∂(μW.prod μN)

end Generic

end PI.WBL
end
end
