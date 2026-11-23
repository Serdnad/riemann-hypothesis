module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle008
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle018
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle012
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDenom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle016
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle011
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle015
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenActs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSiteFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle003
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

namespace UpperTheory.Gal.W2.Seed

open UpperTheory.Gal.Int.Geo.Pl (dict_holds sides_holds levBasic_holds)
open UpperTheory.Gal.CertificateRingHomMap (pLocComm_of pThLoc_of)

theorem tfCen_holds : TfCen := pTfCen pAvgK pTfAdm
theorem tfAct_holds : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
theorem tfIdem_holds : TfIdem := pTfIdem pTfAdm tfCen_holds
theorem tfMulL_holds : TfMulL := pTfMulL pTfAdm tfAct_holds pDosetIff
theorem tfMulR_holds : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
theorem tfLoc_holds : TfLoc := pTfLoc pTfAdm tfAct_holds pDosetIff
theorem knIff_holds : KNIff := pKNIff latCoord_holds
theorem atApart_holds : AtApart := pAtApart pJEq
theorem levFact_holds : LevFact := pLevFact atApart_holds pIntConj
theorem knIdx_holds : KNIdx := pKNIdx (pKNOpen knIff_holds)
theorem pPart_holds : PPart := pPPart pJEq
theorem memAct_holds : MemAct := pMemAct pMemSum pSumDoset tfAct_holds pDosetCosets
theorem memDeck_holds : MemDeck := pMemDeck pMemSum tfCen_holds
theorem levSec_holds : LevSec := pLevSec pIntConj
theorem knFact_holds : KNFact :=
  pKNFact knIff_holds pFacEq atApart_holds pCongGrpEx (pCongConj pLocComm_of) pLocComm pLocComm_of
theorem siteFact_holds : SiteFact := pSiteFact dict_holds sides_holds pIntConj pLocComm_of
theorem stabKer_holds : StabKer := pStabKer pFacEq knFact_holds pCongGrpEx
theorem seenShape_holds : SeenShape := pSeenShape stabKer_holds siteFact_holds (pCenFacts sides_holds) levBasic_holds pLocComm_of
theorem seenActs_holds : SeenActs := pSeenActs pMemSum memAct_holds memDeck_holds seenShape_holds levBasic_holds knIdx_holds
theorem actsConv_holds : ActsConv := pActsConv pTfAdm tfIdem_holds
theorem phiTy_holds : PhiTy := pPhiTy pPart_holds levSec_holds pFacEq pLocComm

theorem tyFact_holds : Spc.TyFact :=
  pTyFact pFacEq levSec_holds levFact_holds atApart_holds pCongGrpEx pDenom pLocComm pLocComm_of
theorem memFn_holds : Spc.MemFn := pMemFn seenShape_holds seenActs_holds actsConv_holds tyFact_holds
theorem phiEx_holds : Spc.PhiEx :=
  pPhiEx phiTy_holds seenShape_holds seenActs_holds tyFact_holds tfAct_holds tfCen_holds (tEig_of_thLoc (pThLoc_of pLocComm_of CertificateRingHomMap.pOfUBij_of)) atApart_holds pFacEq pJEq
    pLocComm

end UpperTheory.Gal.W2.Seed
