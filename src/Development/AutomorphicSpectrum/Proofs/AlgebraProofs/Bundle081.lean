module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecial
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle079
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle068
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle077
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle022
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle037
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle063
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle039
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle017
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle080
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.picard_generic_fibre_injective : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ Y : A.left.Opens, IsCompact (Y : Set A.left) →
    ∀ q : Pic Y.toScheme, pull (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q = 0 → q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero | exact GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.picard_mayer_vietoris_extend : ∀ (X : Scheme.{0}) (W V : X.Opens) (p : Pic W.toScheme),
    pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0 →
    ∃ q : Pic (W ⊔ V).toScheme, pull (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) q = p := by
  first | exact @GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero | exact GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.picard_generic_trivial_near_special : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic (pullback A.hom (spMap (algebraMap R C))),
      ∃ V : A.left.Opens, (∃ y ∈ V, A.hom y = IsLocalRing.closedPoint R) ∧
        pull (pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero.near_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero.near_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero.near_zero <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof
    GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
  have hCM : GenericProjClosureModel.Statement :=
    GenericProjClosureModel.proof TwistedDualGensExist.proof
      (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
        (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
      (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)
  have hFM : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSP := SegreFlagClosurePullback.proof GlobalTheory.T.pair_number_pullback hPE hFM
    PairNumberRelabel.proof VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE hFM
    GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE hCM hSCN)
    SymmetricSpanHsymm.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.section_through_closed_point : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)), Smooth X.hom →
    (∀ z : X.left, IsClosed {z} → X.hom z = IsLocalRing.closedPoint R →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z) ∧
    (∀ U : X.left.Opens, (∃ z ∈ U, X.hom z = IsLocalRing.closedPoint R) →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U) := by
  first | exact @GlobalTheory.CompanionTheory.Sections.exists_section | exact GlobalTheory.CompanionTheory.Sections.exists_section | (intros; apply GlobalTheory.CompanionTheory.Sections.exists_section <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.valuation_integers_rank_one : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing | exact GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.henselian_alg_closed_residue : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C],
    HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.Hens.henselian_and_residueField_isAlgClosed | exact GlobalTheory.CompanionTheory.CommAlg.Hens.henselian_and_residueField_isAlgClosed | (intros; apply GlobalTheory.CompanionTheory.CommAlg.Hens.henselian_and_residueField_isAlgClosed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generic_point_open_immersion : ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  first | exact @GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction | exact GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction | (intros; apply GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction <;> assumption)
end

end

section

@[expose] public section


theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main <;> assumption)

end
end
