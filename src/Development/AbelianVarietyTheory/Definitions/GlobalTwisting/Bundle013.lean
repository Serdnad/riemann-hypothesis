module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Lean.Meta.Injective

@[expose] public section

section

namespace GlobalTheory.Fc.S0


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure HypothesesU : Prop where
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  cohomologicalCsdTempered : GlobalTheory.Published.CohomologicalCsdTempered
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL
  galoisRepOfPolarizedCuspidal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  baseChangeDefiniteUnitary : GlobalTheory.Published.BaseChangeDefiniteUnitary
  bhattScholzeCrystallineLattices : GlobalTheory.Published.BhattScholzeCrystallineLattices
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  doublingMethod : GlobalTheory.Published.DoublingMethod
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  unlinkedProductIrreducible : GlobalTheory.Published.UnlinkedProductIrreducible
  depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective
  howeDualityGL : GlobalTheory.Published.HoweDualityGL
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  localGlobalAboveL : GlobalTheory.Published.LocalGlobalAboveL
  regularAlgebraicPurity : GlobalTheory.Published.RegularAlgebraicPurity
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  heckeLAdicParameterAbove : GlobalTheory.Published.HeckeLAdicParameterAbove
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  depthZeroInertia : GlobalTheory.Published.DepthZeroInertia
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  rayCharacterArtin : GlobalTheory.Published.RayCharacterArtin
  genericUnitaryDualGL : GlobalTheory.Published.GenericUnitaryDualGL
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  pseudoCoefficientUpq : GlobalTheory.Published.PseudoCoefficientUpq
  harishChandraCharacters : GlobalTheory.Published.HarishChandraCharacters
  langlandsClassification : GlobalTheory.Published.LanglandsClassification
  labesseWaldspurger : GlobalTheory.Published.LabesseWaldspurger
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  besselUniquenessReal : GlobalTheory.Published.BesselUniquenessReal
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  siegelEisensteinSimplePole : GlobalTheory.Published.SiegelEisensteinSimplePole
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  regularisedSiegelWeilFirstTerm : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar

end GlobalTheory.Fc.S0
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

open GlobalTheory.Fc

def ReferenceChainEvaluationAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u

def ReferenceChainEvaluationAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ReferenceChainEvaluationAdmissible 𝒜

def H_aPtTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw

def TwistedPointAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPtTw 𝒜

def H_aPer0 (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)

def PeriodAtZeroAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPer0 𝒜

def H_aPerTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def TwistedPeriodAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPerTw 𝒜

def H_tie (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.RealPlaceSecondLayerConditions Fm

def Row_tie {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_tie 𝒜

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
end
