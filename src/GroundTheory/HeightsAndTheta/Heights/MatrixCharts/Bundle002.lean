module

public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def leadMinor {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  (Matrix.of fun a b : Fin i =>
    if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0).det

def periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Fin (g + g) → Fin g → ℂ :=
  Fin.append (fun k => Pi.single k 1) (fun k => τ *ᵥ Pi.single k 1)

def periodGram {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin (g + g)) (Fin (g + g)) ℝ :=
  Matrix.of fun i j => hermPair (τ.map Complex.im)⁻¹ (periodBasis τ i) (periodBasis τ j)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def InvEntryBound.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c →
    (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ j l, |Y⁻¹ j l| ≤ c⁻¹

def InvEntryDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ)
    (Y : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (c b : ℝ), 0 < c →
    (Y p - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef →
    (∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p ∧ ‖fderiv ℝ (fun q => Y q j l) p‖ ≤ b) →
    ∀ j l, DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p ∧
      ‖fderiv ℝ (fun q => (Y q)⁻¹ j l) p‖ ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b

def MatrixDetDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (H : E → Matrix (Fin k) (Fin k) ℂ) (p : E) (A B : ℝ),
    (∀ j l, DifferentiableAt ℝ (fun q => H q j l) p ∧ ‖H p j l‖ ≤ A ∧
      ‖fderiv ℝ (fun q => H q j l) p‖ ≤ B) →
    DifferentiableAt ℝ (fun q => (H q).det) p ∧
      ‖fderiv ℝ (fun q => (H q).det) p‖ ≤ (k.factorial : ℝ) * k * A ^ (k - 1) * B

def GramEntryDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g k : ℕ)
    (F : E → Matrix (Fin g) (Fin k) ℂ) (Z : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (a e e' : ℝ),
    (∀ j l, DifferentiableAt ℝ (fun q => F q j l) p ∧ ‖F p j l‖ ≤ a ∧
      ‖fderiv ℝ (fun q => F q j l) p‖ ≤ a) →
    (∀ j l, DifferentiableAt ℝ (fun q => Z q j l) p ∧ |Z p j l| ≤ e ∧
      ‖fderiv ℝ (fun q => Z q j l) p‖ ≤ e') →
    ∀ j l, DifferentiableAt ℝ (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) p ∧
      ‖((F p)ᴴ * (Z p).map (fun x : ℝ => (x : ℂ)) * F p) j l‖ ≤ (g : ℝ) ^ 2 * a ^ 2 * e ∧
      ‖fderiv ℝ (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) p‖ ≤
        (g : ℝ) ^ 2 * (2 * a ^ 2 * e + a ^ 2 * e')

def LogDetGramDeriv.Statement : Prop :=
  ∀ g k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Matrix (Fin g) (Fin k) ℂ) (Y : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (a b c μ : ℝ),
    0 < c → 0 < μ → 0 ≤ a → 0 ≤ b →
    (∀ j l, DifferentiableAt ℝ (fun q => F q j l) p ∧ ‖F p j l‖ ≤ a ∧
      ‖fderiv ℝ (fun q => F q j l) p‖ ≤ a) →
    (∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p ∧ ‖fderiv ℝ (fun q => Y q j l) p‖ ≤ b) →
    (Y p - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef →
    μ ≤ ((F p)ᴴ * (Y p)⁻¹.map (fun x : ℝ => (x : ℂ)) * F p).det.re →
    DifferentiableAt ℝ (fun q => logDetGram (Y q) (F q)) p ∧
      ‖fderiv ℝ (fun q => logDetGram (Y q) (F q)) p‖ ≤
        K * (1 + a) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + b) / μ

def AnalyticDerivBound.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (U K : Set E),
    IsOpen U → AnalyticOnNhd ℂ f U → IsCompact K → K ⊆ U →
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K, DifferentiableAt ℝ f x ∧ ‖f x‖ ≤ A ∧ ‖fderiv ℝ f x‖ ≤ A

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MCBounds
open scoped ComplexOrder

noncomputable section

theorem MCBounds.map_sub_smul_one {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (A - s • (1 : Matrix (Fin g) (Fin g) ℝ)).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) - (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  ext j k
  by_cases h : j = k <;> simp [h]

theorem MCBounds.conj_sub_smul_one {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (Z - s • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = Fᴴ * Z * F - s • (Fᴴ * F) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem MCBounds.re_det_ofReal_smul {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights
end
