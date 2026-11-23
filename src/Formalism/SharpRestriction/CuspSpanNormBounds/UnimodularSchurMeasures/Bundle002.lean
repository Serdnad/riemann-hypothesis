module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions Formalism.BasicNotions.TH

theorem halfInt_of_integrality (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hu : Formalism.QuantumDeterminants.IsHCParam u) (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) : HalfIntegralDifference k r u v b := by
  intro i s
  obtain ⟨m1, e1⟩ := hu.2 i
  obtain ⟨m2, e2⟩ := hl.2 s
  refine ⟨m1 - m2 - r - 1, ?_⟩
  push_cast at e1 e2 ⊢
  linarith

end Formalism.MainNotions.LeviCoordinates

end
end

section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ}

theorem unitary_group_mul_mem {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem cayley_conj_mem_diagonal_model {ε : Fin (2 * r + k + 1) → Bool} {P a : Mat k r} (hP : IsCayleyU k r ε P)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ UJset ε ∧ P⁻¹ * (P * a * P⁻¹) * P = a := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  constructor
  · show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hH, ha']
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2]; simp
  · calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp

theorem discrete_series_map_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {a b : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hrep := hDS.2.2.1.1.2 _ (cayley_conj_mem_diagonal_model hP ha).1 _ (cayley_conj_mem_diagonal_model hP hb).1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have e1 : P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = a * b := by
    calc P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = a * b := by rw [h1]; simp
  simp only [e1, (cayley_conj_mem_diagonal_model hP ha).2, (cayley_conj_mem_diagonal_model hP hb).2] at hrep
  exact hrep

end Grp

structure BData : Type 1 where
  k : ℕ
  r : ℕ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  v : Fin (k - 1) → ℝ
  b : Fin (2 * r + 2) → ℝ
  H : Type
  [hN : NormedAddCommGroup H]
  [hI : InnerProductSpace ℂ H]
  [hC : CompleteSpace H]
  σ : Mat k r → (H →L[ℂ] H)
  Vp : Type
  [vN : NormedAddCommGroup Vp]
  [vI : InnerProductSpace ℂ Vp]
  [vF : FiniteDimensional ℂ Vp]
  π : Mat k r → (Vp →L[ℂ] Vp)
  w : H
  μG : Measure (Formalism.QuantumDeterminants.Mt k r)
  μS : Measure (Formalism.QuantumDeterminants.Mt k r)
  ν : Measure (Formalism.QuantumDeterminants.Mt k r)

attribute [instance] BData.hN BData.hI BData.hC BData.vN BData.vI BData.vF

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates

end
end

section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem discrete_series_unitary_rep {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : CayleySignature.Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      σ (x * y) = (σ x).comp (σ y)) ∧ ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ v, ‖σ x v‖ = ‖v‖ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, -, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hback : ∀ x : CayleySignature.Mat k r, P⁻¹ * (P * x * P⁻¹) * P = x := fun x => by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPi, Matrix.one_mul, Matrix.mul_one]
  have hmem : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
    show (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) = Formalism.REAL.Jm ε
    have e1 : (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) =
        (P⁻¹)ᴴ * (xᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * x) * P⁻¹ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, hPJ, hx', ← hPJ]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPi']; simp
  refine ⟨?_, fun x hx y hy => ?_, fun x hx v => ?_⟩
  · have : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hPi] at this
  · have := hmul _ (hmem x hx) _ (hmem y hy)
    simp only [hback] at this
    have e : P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = x * y := by
      calc P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = (P⁻¹ * P) * x * (P⁻¹ * P) * y * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = x * y := by rw [hPi]; simp
    rwa [e] at this
  · have := hiso _ (hmem x hx) v
    simp only [hback] at this
    exact this

section Pos

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (σ : CayleySignature.Mat k r → (H →L[ℂ] H))
  (hmul : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (x * y) = (σ x).comp (σ y))
  (hone : σ 1 = 1)

include hmul in
theorem smooth_vectors_translate {ai : CayleySignature.Mat k r} (hai : ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) : σ ai v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨Uo, F, hO, hmem, hF, hEq⟩ := hv (g₀ * ai) (mat_mul_mem_UH_Hpk hg₀ hai)
  let L : CayleySignature.Mat k r →L[ℝ] CayleySignature.Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ ai)
  have hL : ∀ g, L g = g * ai := fun g => rfl
  refine ⟨L ⁻¹' Uo, fun g => F (L g), hO.preimage L.continuous, hmem, ?_, fun g hg hin => ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun g hg => hg)
  · have h1 : σ (g * ai) v = F (g * ai) := hEq (g * ai) hg (mat_mul_mem_UH_Hpk hin hai)
    show σ g (σ ai v) = F (L g)
    rw [hL, ← h1, hmul g hin ai hai]; rfl


end Pos

end Formalism.MainNotions.LeviCoordinates

end
end
