module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheorem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle069
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

@[expose] public section

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.crofton_formula_open_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.flag_comparison_theorem : GlobalTheory.CompanionTheory.Ar.GR.FlagStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | exact GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds <;> assumption)
end

section

theorem _root_.GlobalTheory.T.flag_model_join_left :
    GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main
end

section


theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trivial_polarized_abelian_point_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | exact GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero <;> assumption)
end
