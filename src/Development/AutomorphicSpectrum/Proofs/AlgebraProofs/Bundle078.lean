module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PurePeriodLocalBasisExists
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle077
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | exact GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.pure_period_local_basis_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)) (p q : ℕ) (ℓ : Nat.Primes), IsPeriod D ty P₀ → IsTypeFn H p q ty → p + q = D.p + D.q → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (x : Fin p ⊕ Fin q → D.La), IsLocBasis (𝓞 E) ℓ x ∧ IsPure hP x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period | exact GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period <;> assumption)
end

section

open MvPolynomial NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Short ReciprocityTheory.ChartRestriction.G.T0

theorem _root_.GlobalTheory.T.mahler_section_statement_holds : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | exact GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.mahlerSection <;> assumption)
end

section


theorem _root_.GlobalTheory.T.vertical_divisors_commute : GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommute.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute | exact GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute | (intros; apply GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.etale_over_integers_localization : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k], ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away | exact GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away | (intros; apply GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.etale_polynomial_base_change_iff : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int | exact GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int | (intros; apply GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int <;> assumption)
end
