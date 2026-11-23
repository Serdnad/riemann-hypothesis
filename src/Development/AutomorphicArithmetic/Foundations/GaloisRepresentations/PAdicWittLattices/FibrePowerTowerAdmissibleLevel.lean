module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.ExistsDeeperNormalLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGSimOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGenSm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds
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

open UpperTheory.Gal.Int.Geo (KSEx KSNice)

universe u

namespace UpperTheory.Gal.G3

theorem nuInt_holds : NuInt := @pNuInt

theorem multBasic_holds : MultBasic := @pMultBasic @nuInt_holds

theorem kNBasic_holds : KNBasic := @pKNBasic

theorem sysOf_holds : SysOf := @pSysOf @nuInt_holds

theorem fibrePowerTower_admissibleLevel : AdmOf := @pAdmOf

theorem kNCong_holds : KNCong := @pKNCong

theorem gSimOf_holds : GSimOf := @pGSimOf @multBasic_holds

theorem relComp_holds : RelComp := @pRelComp

theorem tateDiff_holds : TateDiff := @pTateDiff

theorem tateTwist_holds : TateTwist := @pTateTwist @gSimOf_holds

theorem fullOf_holds : FullOf := @pFullOf

theorem relArith_holds : RelArith := @pRelArith

theorem transSelf_holds : TransSelf := @pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds

theorem transComp_holds : TransComp := @pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds

theorem homPull_holds : HomPull := @pHomPull

theorem tatePull_holds : TatePull := @pTatePull

theorem transPull_holds : TransPull := @pTransPull @homPull_holds @tatePull_holds

theorem transOfMap_holds : TransOfMap := @pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds

theorem rigid_holds : Rigid := @pRigid

theorem isogFEt_holds : IsogFEt := @pIsogFEt

theorem transKer_holds : TransKer := @pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds

theorem polUniq_holds : PolUniq := @pPolUniq

theorem mapOfIso_holds : MapOfIso := @pMapOfIso

theorem transDeep_holds : TransDeep := @pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds

theorem transIso_holds : TransIso := @pTransIso @isoPts_holds @isogFEt_holds

theorem transOrbit_holds : TransOrbit := @pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds

theorem transFree_holds : TransFree := @pTransFree @kNCong_holds

theorem genSm_holds : GenSm := @pGenSm

theorem powSm_holds : PowSm := @pPowSm @genSm_holds

theorem etDesc_holds : EtDesc := @pEtDesc @extPts_holds

theorem ptOrbit_holds : PtOrbit := @pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds

theorem witComp_holds : WitComp := @pWitComp @transSelf_holds @transComp_holds @transPull_holds

theorem witCart_holds : WitCart := @pWitCart @transIso_holds

theorem witForget_holds : WitForget := @pWitForget @mapOfIso_holds @transSelf_holds

theorem witDeep_holds : WitDeep := @pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds

theorem homDesc_holds : HomDesc := @pHomDesc @etDesc_holds

theorem polDesc_holds : PolDesc := @pPolDesc

theorem transDesc_holds : TransDesc := @pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds

theorem transCancel_holds : TransCancel := @pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds

theorem twFEt_holds : TwFEt := @pTwFEt @fEtBasic_holds @twGal_holds

theorem sigmaFEt_holds : SigmaFEt := @pSigmaFEt

theorem kSNice_holds : KSNice := @pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds

theorem quotUniq_holds : QuotUniq := @pQuotUniq @etDesc_holds

theorem transUniqPt_holds : TransUniqPt := @pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds

theorem ptEq_holds : PtEq := @pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds

theorem witUniq_holds : WitUniq := @pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds

theorem descMap_holds : DescMap := @pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds

theorem witEx_holds : WitEx := @pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds

theorem witOne_holds : WitOne := @pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds

theorem witTrans_holds : WitTrans := @pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds

theorem witFree_holds : WitFree := @pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds

theorem kSEx_holds : KSEx := @pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds

end UpperTheory.Gal.G3
