module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCover
public import ReciprocityTheory.DualLattices.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

theorem _root_.GlobalTheory.T.glue_quotient_charts_cover : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts | exact GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.lattice_length_mono_strict : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq | exact GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem exists_nat_mul_mem_chartLatNm_of_isIntegral_rat :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) [CharZero Ω] (d : ℕ) (a : K → ℤ) (s : Ω), (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))) → ∃ N₀ : ℕ, 0 < N₀ ∧ (N₀ : Ω) * s ∈ chartLatNm y a 1 :=
  @MultiProjectiveCoordinates.exists_integer_multiple_in_lattice

end GlobalTheory.CompanionTheory.Ar.Small
end
