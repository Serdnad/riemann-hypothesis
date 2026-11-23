module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.Published

def FormalDegreeCompactDual : Prop :=
  ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
      (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ (umat g) w)‖ ^ 2 ∂((sc N ε : ENNReal) • Formalism.REAL.muG ε) =
          (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b : Fin N => a < b), |lam a - lam b|) /
            ∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b : Fin N => a < b),
              (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

theorem formalDegreeCompactDual_iff : FormalDegreeCompactDual ↔ GlobalTheory.Mem.Vol.FormalDegreeFormula₂ := Iff.rfl

end GlobalTheory.Published
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesUpqExists : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
    (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)),
      CompleteSpace H ∧ Nontrivial H ∧
      IsURepOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      IsIrredOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      (∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (muG ε)) ∧
      (∃ S : Submodule ℂ H, IsKTypeOf ε σ (lam + rhoN ε - rhoC ε) S) ∧
      ∀ (μ : Fin N → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
        nsq (lam + rhoN ε - rhoC ε + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε)

theorem discreteSeriesUpqExists_iff : DiscreteSeriesUpqExists ↔ GlobalTheory.Mem.Vol.DiscreteSeriesExist := Iff.rfl

theorem discreteSeriesUpqExists_iff_dsExists : DiscreteSeriesUpqExists ↔ GlobalTheory.Dec.DSExists := Iff.rfl

end GlobalTheory.Published
end
end
