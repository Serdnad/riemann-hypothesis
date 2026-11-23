module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialRemainderBound
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightTestBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettings
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.test_polynomial_remainder_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → 4 * Fintype.card Ψ * N ^ 2 ≤ B₀ → IsDecomp (testPoly j) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B₀ τ k (Q τ k)| ≤ 1.6 * (((dimX Ψ N j : ℝ) + 1) * testDeg Ψ N j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.testRest_bound | exact GlobalTheory.CompanionTheory.Ar.Top.testRest_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.testRest_bound <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.flag_height_test_bound : GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (j : ℕ), 1 ≤ j → j < N → HhTestBound j (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl | exact GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.slope_lower_base_settings : GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ), T.Proportional → 3 * (N - T.j) + 1 ≤ N → (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c, T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) → T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings | exact GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings <;> assumption)
end
