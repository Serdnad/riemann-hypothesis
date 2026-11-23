module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle006
public import Mathlib.Tactic.Continuity
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle002
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle030
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem _root_.GlobalTheory.T.weight_map_injective : ∀ (Ψ : Type) (N : ℕ), Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem _root_.GlobalTheory.T.symmetric_form_polynomial_coeff : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ), (∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) → ∀ (w₀ : Fin n → σ) (m : σ →₀ ℕ), (∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) → AddMonoidAlgebra.coeff (PB.formPoly n a) m * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul <;> assumption)
end
