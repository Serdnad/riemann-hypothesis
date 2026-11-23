module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle147
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle041
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiCurveIn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLatticeEigenCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointMultiplicityCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle148
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle151
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.powFns_of_abelian_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsReduced X0 → IsLocallyNoetherian X0 → (∀ z : X0, (∀ z' : X0, z' ⤳ z → z' = z) → z ∈ abLocus t.G) → PowFns t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian | exact GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian | (intros; apply GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isDeg_coordDeg : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) :=
  PositivityTheory.HtPt.Ci.isdeg_coord

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.CompanionTheory.Relay.curve_through_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  first | exact @PositivityTheory.HtPt.Ci.curve_in_cpt | exact PositivityTheory.HtPt.Ci.curve_in_cpt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.det_lattice_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat | exact GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.abelian_part_lattice_eigen_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (Vl : Lat 𝔐.ξ 𝔐.Li) (m : ℕ) (U : Submodule Ω 𝔐.Li) (s : Fin m → 𝔐.Li) (sL : Fin m → V), Vl.IsVB m U → Vl.IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → IsValues 𝔐 z P MV s sL → LinearIndependent L sL → ∃ (T : FinitePlace L → Matrix (Fin m) (Fin m) L) (T' : FinitePlace L → Matrix (Fin m) (Fin m) Ω) (b' : FinitePlace L → Fin m → 𝔐.Li), (∀ v, Vl.IsFrameAt (b' v) ⟨z (primeOf v), 𝔐.all _⟩) ∧ (∀ v k, b' v k = ∑ k', T' v k' k • s k') ∧ (∀ v i j, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' v i j) (T v i j)) ∧ (∀ v, (T v).det ≠ 0) ∧ {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite ∧ ∀ x, x ∈ 𝔐.FibLat Vl z P MV ↔ x ∈ Submodule.span L (Set.range sL) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • sL j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame.fin_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame.fin_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame.fin_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.frame_point_multiplicity_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (θ : R →+* (Localization.AtPrime q)) (σ₁ σ₂ : E →+* ℂ) (n₁ n₂ : ℕ) (h₁ : D.mult σ₁ = n₁) (h₂ : D.mult σ₂ = n₂) (e₁ : Fin n₁ → (epsAt x ⟶ Y.t.G)) (e₂ : Fin n₂ → (epsAt x ⟶ Y.t.G)) (C₁ : Matrix (Fin n₁) (Fin n₁) (Localization.AtPrime q)) (C₂ : Matrix (Fin n₂) (Fin n₂) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂ i) V) → ∃ (g : S) (θ' : R →+* (Localization.Away g)) (C₁' : Matrix (Fin n₁) (Fin n₁) (Localization.Away g)) (C₂' : Matrix (Fin n₂) (Fin n₂) (Localization.Away g)), g ∉ q ∧ spMap θ' ≫ x = spMap (algebraMap S (Localization.Away g)) ≫ zPt z ≫ Y.j ∧ IsUnit C₁'.det ∧ IsUnit C₂'.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁' i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂' i) V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames | exact GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.period_gram_comparison_bound : ∀ (n a₀ g r a : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) → (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) → ∃ ε c C : ℝ, 0 < ε ∧ ε ≤ ρ ∧ 0 < c ∧ 0 < C ∧ ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 → HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 → ((HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.complete_dvr_pullback_semiabelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr))) (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (b : t'.G.left ⟶ tX.G.left), IsGrpPullback t'.G tX.G (FinRd.Roots.gen T zV) b → (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) → ∃ Ψ : G.G.left ⟶ tX.G.left, IsGrpPullback G.G tX.G zV Ψ ∧ m2.φ ≫ Ψ = b ∧ ∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_extended_identification | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_extended_identification | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_extended_identification <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Ratio

variable {X Y F Y' Z : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

theorem gm_pull_g (N : LB X) (f : F ⟶ X) (ψ : Z ⟶ F) (z : Z) (a b : N.ι) (ha : f (ψ z) ∈ N.U a)
    (hb : f (ψ z) ∈ N.U b) :
    gm ψ z ((N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b)) ((N.pull f).g (fun _ => a) (fun _ => b)) =
      gm (ψ ≫ f) z _ (N.g a b) := by
  have hp : ψ z ∈ (N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b) := ⟨mem_pull.2 ha, mem_pull.2 hb⟩
  show gm ψ z _ (∏ _k : PUnit, (res _ (pullU f _ (N.g a b))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res ψ z _ hp _).trans (gm_pull ψ f z (N.U a ⊓ N.U b) ⟨ha, hb⟩ _)

theorem gm_w_trans {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen) (ψ : Z ⟶ F) (z : Z) {a a' : L.ι} {b b' : M.ι}
    (ha : f (ψ z) ∈ L.U a) (ha' : f (ψ z) ∈ L.U a') (hb : g (ψ z) ∈ M.U b) (hb' : g (ψ z) ∈ M.U b') :
    gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a)) (w.s (fun _ => b, fun _ => a)) =
      gm (ψ ≫ g) z _ (M.g b b') * (gm (ψ ≫ f) z _ (L.g a a'))⁻¹ *
        gm ψ z ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) (w.s (fun _ => b', fun _ => a')) := by
  have hm : ψ z ∈ (M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) :=
    ⟨⟨mem_pull.2 hb, mem_pull.2 ha⟩, mem_pull.2 hb', mem_pull.2 ha'⟩
  have e := congrArg (gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')))) (hw (fun _ => b, fun _ => a) (fun _ => b', fun _ => a'))
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res ψ z _ hm _))))
  show gm ψ z _ (res _ ((M.pull g).g (fun _ => b) (fun _ => b')) * (res _ ((L.pull f).g (fun _ => a) (fun _ => a')))⁻¹) = _
  rw [map_mul, map_inv, gm_res ψ z _ hm, gm_res ψ z _ hm, gm_pull_g M g ψ z b b' hb hb', gm_pull_g L f ψ z a a' ha ha']

variable {K : Type} [Fintype K]

def rW (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y) (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) : Y'.Opens :=
  LB.wchart L (fun k => φ k ≫ f) p ⊓ LB.wchart M (fun k => φ k ≫ g) q

theorem rW_le (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) (k : K) :
    rW L M f g φ p q ≤ φ k ⁻¹ᵁ ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) :=
  fun _ hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩

def rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (p : K → L.ι) (q : K → M.ι) : Γ(Y', rW L M f g φ p q)ˣ :=
  res inf_le_left (c.s p) *
    (∏ k, res (rW_le φ p q k) (pullU (φ k) _ (w.s (fun _ => q k, fun _ => p k))) ^ ε k) *
    (res inf_le_right (b.s q))⁻¹

def rVal (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z (LB.wchart L (fun k => φ k ≫ f) p) (c.s p) *
    (∏ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) ^ ε k) *
    (gm r z (LB.wchart M (fun k => φ k ≫ g) q) (b.s q))⁻¹

theorem gm_rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) (hz : r z ∈ rW L M f g φ p q) :
    gm r z _ (rLoc w φ ε c b p q) = rVal w φ ε c b r z p q := by
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) ?_))
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hz _))))
  exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
    ((gm_res r z _ hz _).trans (gm_pull r (φ k) z _ (rW_le φ p q k hz) _))))

theorem comm_group_ratio_cancel {A : Type} [CommGroup A] (tl tm c' w' b' tm' tl' : A) (h1 : tl = tl') (h2 : tm = tm') :
    (tl * c') * (tm' * tl'⁻¹ * w') * (tm * b')⁻¹ = c' * w' * b'⁻¹ := by
  subst h1 h2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem rVal_indep {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → M.ι}
    (hz : r z ∈ rW L M f g φ p q) (hz' : r z ∈ rW L M f g φ p' q') :
    rVal w φ ε c b r z p q = rVal w φ ε c b r z p' q' := by
  have e : ∀ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) =
      gm ((r ≫ φ k) ≫ g) z _ (M.g (q k) (q' k)) * (gm ((r ≫ φ k) ≫ f) z _ (L.g (p k) (p' k)))⁻¹ *
        gm (r ≫ φ k) z ((M.pull g).U (fun _ => q' k) ⊓ (L.pull f).U (fun _ => p' k)) (w.s (fun _ => q' k, fun _ => p' k)) :=
    fun k => gm_w_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hz.1 k) (Set.mem_iInter.1 hz'.1 k)
      (Set.mem_iInter.1 hz.2 k) (Set.mem_iInter.1 hz'.2 k)
  unfold rVal
  rw [gen_trans hc r z hz.1 hz'.1, gen_trans hb r z hz.2 hz'.2, Finset.prod_congr rfl fun k _ => by rw [e k]]
  simp only [mul_zpow, Finset.prod_mul_distrib, inv_zpow, Finset.prod_inv_distrib]
  refine comm_group_ratio_cancel _ _ _ _ _ _ _ ?_ ?_
  · simp only [trF, Category.assoc]
  · simp only [trF, Category.assoc]

theorem exists_unit_ratio_of_generators (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) : ∃ u : Γ(Y', ⊤)ˣ, Tr w φ _ _ ε c b u := by
  obtain ⟨u, hu⟩ := glue_unit (X := Y') ⊤ (fun i : (K → L.ι) × (K → M.ι) => rW L M f g φ i.1 i.2) (fun _ => le_top)
    (fun y _ => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
      choose I' hI' using fun χ : Y' ⟶ Y => exists_chart hM (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun k => I (φ k ≫ f), fun k => I' (φ k ≫ g)),
        Set.mem_iInter.2 fun k => hI _, Set.mem_iInter.2 fun k => hI' _⟩)
    (fun i => rLoc w φ ε c b i.1 i.2)
    (fun i j y hy => by
      rw [gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.1, gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.2]
      exact rVal_indep hw φ ε hc hb (𝟙 Y') y hy.1 hy.2)
  refine ⟨u, fun Z r z JL JM hJL hJM => ?_⟩
  have hz : r z ∈ rW L M f g φ (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => JM ((r ≫ φ k) ≫ g)) :=
    ⟨Set.mem_iInter.2 fun k => hJL _, Set.mem_iInter.2 fun k => hJM _⟩
  have e := gm_rLoc w φ ε c b r z _ _ hz
  rw [← hu (_, _), gm_res r z _ hz] at e
  rw [val_of c r z JL (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => by rw [Category.assoc]),
    val_of b r z JM (fun k => JM ((r ≫ φ k) ≫ g)) (fun k => by rw [Category.assoc])]
  exact mul_inv_eq_iff_eq_mul.1 e.symm

theorem exists_ratio_iso : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB →
    ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen →
    ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  intro X Y F L M f g hL hM w hw Y' K _ φ φL φM ε c b h₁ h₂ hc hb
  obtain rfl : (fun k => φ k ≫ f) = φL := funext h₁
  obtain rfl : (fun k => φ k ≫ g) = φM := funext h₂
  exact exists_unit_ratio_of_generators hL hM hw φ ε hc hb

end Ratio

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

theorem linearIndependent_span_of_toMatrix {S M C A : Type} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype C] [DecidableEq C] [Fintype A] [DecidableEq A] (e : Basis C S M) (w : A → M)
    (Q : Matrix A C S) (h₁ : e.toMatrix w * Q = 1) (h₂ : Q * e.toMatrix w = 1) :
    LinearIndependent S w ∧ Submodule.span S (Set.range w) = ⊤ := by
  let L : (A → S) ≃ₗ[S] (C → S) := LinearEquiv.ofLinearMap (Matrix.toLin' (e.toMatrix w)) (Matrix.toLin' Q)
    (by rw [← Matrix.toLin'_mul, h₁, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h₂, Matrix.toLin'_one])
  let b : Basis A S M := (Pi.basisFun S A).map (L ≪≫ₗ e.equivFun.symm)
  have hb : ⇑b = w := by
    funext i
    apply e.equivFun.injective
    ext a
    simp [b, L, Basis.toMatrix_apply, Matrix.toLin'_apply]
  exact ⟨hb ▸ b.linearIndependent, hb ▸ b.span_eq⟩

def pairBasis (R : Type) [CommRing R] (d : ℕ) : Basis (Fin d ⊕ Fin d) R ((Fin d → R) × (Fin d → R)) :=
  (Pi.basisFun R (Fin d)).prod (Pi.basisFun R (Fin d))

theorem pairBasis_repr_vmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (y : (Fin d → R) × (Fin d → R)) (a : Fin d ⊕ Fin d) :
    (pairBasis S d).repr (vmap f y) a = f ((pairBasis R d).repr y a) := by
  cases a <;> simp [pairBasis, vmap]

theorem linearIndependent_span_vmap {R S A : Type} [CommRing R] [CommRing S] [Fintype A] (f : R →+* S) {d : ℕ}
    (v : A → (Fin d → R) × (Fin d → R)) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent S (fun i => vmap f (v i)) ∧
      Submodule.span S (Set.range fun i => vmap f (v i)) = ⊤ := by
  classical
  let b : Basis A R ((Fin d → R) × (Fin d → R)) := Basis.mk hli hsp.ge
  have hb : ⇑b = v := Basis.coe_mk hli hsp.ge
  have hP : (pairBasis S d).toMatrix (fun i => vmap f (v i)) = ((pairBasis R d).toMatrix v).map f := by
    ext a i
    simp [Basis.toMatrix_apply, pairBasis_repr_vmap]
  have h₁ : (pairBasis R d).toMatrix v * b.toMatrix (pairBasis R d) = 1 := by
    rw [← hb]; exact Basis.toMatrix_mul_toMatrix_flip _ _
  have h₂ : b.toMatrix (pairBasis R d) * (pairBasis R d).toMatrix v = 1 := by
    rw [← hb]; exact Basis.toMatrix_mul_toMatrix_flip _ _
  refine linearIndependent_span_of_toMatrix (pairBasis S d) _ ((b.toMatrix (pairBasis R d)).map f) ?_ ?_
  · rw [hP, ← Matrix.map_mul, h₁, Matrix.map_one _ f.map_zero f.map_one]
  · rw [hP, ← Matrix.map_mul, h₂, Matrix.map_one _ f.map_zero f.map_one]

theorem isHBasis_map : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R]
    [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x →
      IsHBasis B₂ (fun j => vmap f (x j)) := by
  intro E _ _ _ R S _ _ _ f d r B B₂ x h hx
  have key := linearIndependent_span_vmap f _ hx.1 hx.2
  have he : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B₂ (RingOfIntegers.basis E q.2) (vmap f (x q.1))) =
      fun q => vmap f (rhoH B (RingOfIntegers.basis E q.2) (x q.1)) :=
    funext fun q => (vmap_rhoH h _ _).symm
  unfold IsHBasis
  rw [he]
  exact key

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre

section

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {e : B → ℕ}
    (hg : IsMultiHomog g e) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  have hT : (∏ k, (X k : MvPolynomial B Ω) ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  rw [mCoordIdeal, RingHom.mem_ker]
  show mConeMap y g = 0 ↔ _
  rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hg, mul_eq_zero, or_iff_right hT, C_eq_zero]

variable (v : Place (ZMod p) K) (w : (Σ k, J k) → K) (c : ∀ k, J k)

def ratio (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))
    (q : Σ k, J k) : v.ring :=
  ⟨w q / w ⟨q.1, c q.1⟩, by
    rw [← v.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hle q.1 q.2) zero_le'⟩

variable {v w c}
variable (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))

include hc in
theorem prod_ne_zero (e : B → ℕ) : (∏ k, w ⟨k, c k⟩ ^ e k) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem coe_aeval_ratio {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval (ratio v w c hc hle) g : v.ring) : K) = aeval w g * (∏ k, w ⟨k, c k⟩ ^ e k)⁻¹ := by
  rw [← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g e hg]
  exact MvPolynomial.comp_aeval_apply (φ := (algebraMap v.ring K).toIntAlgHom) _ g

theorem aeval_residue (g : MRing J) :
    aeval (fun q => residue v.ring (ratio v w c hc hle q)) g =
      residue v.ring (aeval (ratio v w c hc hle) g) :=
  (MvPolynomial.comp_aeval_apply (φ := (residue v.ring).toIntAlgHom) _ g).symm

theorem valuation_prod (e : B → ℕ) :
    v.valuation (∏ k, w ⟨k, c k⟩ ^ e k) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_pow _ _ _

include hc in
theorem prod_valuation_pos (e : B → ℕ) : 0 < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [← valuation_prod]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (prod_ne_zero hc e))


include hc hle in
theorem valuation_aeval_le {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    v.valuation (aeval w g) ≤ ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  have h := (v.valuation_le_one_iff _).2 (aeval (ratio v w c hc hle) g).2
  rw [coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod] at h
  rwa [mul_inv_le_iff₀ (prod_valuation_pos hc e), one_mul] at h

theorem mem_iff {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    g ∈ mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)) ↔
      v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  refine (mem_mCoordIdeal_iff _ hg).trans (Iff.trans (Eq.congr_left (aeval_residue hc hle g)) ?_)
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← v.valuation_lt_one_iff,
    coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod,
    mul_inv_lt_iff₀ (prod_valuation_pos hc e), one_mul]

end

theorem exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K)
    (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) →
    (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) →
    ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧
      (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧
      ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e →
        (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  intro B _ J _ p _ K _ _ _ w v c hc hle
  refine ⟨mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)), RingHom.ker_isPrime _,
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _, ?_, ?_, ?_, fun e g hg => mem_iff hc hle hg⟩
  · obtain ⟨S, hS, hSe⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    have hSV : Ideal.span S ≤ mCoordIdeal w := hSe.ge
    rw [hSe, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have hf0 : aeval w f = 0 := (mem_mCoordIdeal_iff w ha).1 (hSV (Ideal.subset_span hf))
    refine (mem_iff hc hle ha).2 ?_
    rw [hf0, map_zero]
    exact prod_valuation_pos hc a
  · intro k h
    have h1 := (X_mem_iff _ k (c k)).1 h
    have h2 : ratio v w c hc hle ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
    rw [h2, map_one] at h1
    exact one_ne_zero h1
  · intro e g h hg hh hhW
    have hh' : v.valuation (aeval w h) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k :=
      le_antisymm (valuation_aeval_le hc hle hh) (not_lt.1 fun hlt => hhW ((mem_iff hc hle hh).2 hlt))
    rw [hh']
    exact ⟨valuation_aeval_le hc hle hg, (mem_iff hc hle hg).1⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre
end
end

section


theorem _root_.GlobalTheory.T.TwistAut_holds : GlobalTheory.CompanionTheory.Ar.TwistAut := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | exact GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut <;> assumption)
end
