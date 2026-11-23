module

import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.HilbertLowestWeightOfInputs
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepFormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HloweqTransfer
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt

@[expose] public section

section

noncomputable section

open Finset

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_cone_of_stable_mollifier : StepStable → StepMoll → StepWtSpan → StepCone := by
  apply CompanionTheory.RgDs.Hilb.hilbert_cone_of_stable_mollifier <;> assumption

end PositivityTheory.RgDs.Hilb
end
end

section

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem weight_space_le_hilbert {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : V1 ε Ψ ≤ Hlam ε Ψ T.w := by
  rintro _ ⟨v, hv, rfl⟩
  exact UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) (datumV ε Ψ T.w) v hv

theorem hilb_of (h1 : StepStable) (h2 : StepDatum) (h0 : StepSig) (h3 : StepMoll) (h4 : StepWtSpan)
    (h5 : StepStable → StepMoll → StepWtSpan → StepCone)
    (h6 : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq)
    (h7 : StepDatum → StepIrred) (h8 : StepDatum → StepFormulaF) (h10 : StepSig → StepSqInt)
    (h9 : StepVogan) : Hilb := by
  apply CompanionTheory.RgDs.Hilb.hilb_of <;> assumption

end PositivityTheory.RgDs.Hilb
end
end

section

noncomputable section

open Finset

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hloweq_transfer {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (A : L2 ε →ₗ[ℂ] L2 ε)
    (hAK : ∀ k ∈ Kset ε, ∀ x, A (rreg ε k x) = rreg ε k (A x)) {S : Submodule ℂ (L2 ε)}
    (hinj : ∀ w ∈ S, A w = 0 → w = 0) (hS : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) Λ S) :
    Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) Λ (S.map A) :=
  _root_.UpperTheory.Reformulated.B.Re4.hloweq_transfer A hAK hinj hS

theorem hloweq_brIdx {n : ℕ} (c : Fin n → Fin n → ℕ) :
    brIdxSum (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) =
      ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
  unfold brIdxSum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := brIdxSum_root a b
  unfold brIdxSum at this
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem hloweq_eq_of_cone {n : ℕ} {ε : Fin n → Bool} {ν Λ : Fin n → ℝ} (h1 : InCone Λ ν)
    (h2 : Formalism.MainNotions.S.CDom ε ν Λ) : ν = Λ := by
  apply CompanionTheory.RgDs.Hilb.hloweq_eq_of_cone <;> assumption

theorem hilbert_lowest_weight_of_inputs : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq := by
  apply CompanionTheory.RgDs.Hilb.hilbert_lowest_weight_of_inputs <;> assumption

end PositivityTheory.RgDs.Hilb
end
end
