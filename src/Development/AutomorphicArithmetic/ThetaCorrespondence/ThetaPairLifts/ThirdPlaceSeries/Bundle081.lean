module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle594
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle052
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle158
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle162
public import Development.AutomorphicArithmetic.CharacterBoxes.ClassSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle075
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr


variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
def ysTh_alt (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpRealS (datTw x (thTw (Dof x) th)).R (datTw x (thTw (Dof x) th)).cG ((thTw (Dof x) th).rat l.rat.S) where
  fi := (by with_unfolding_all exact (l.b.YS.fi :))
  geq := (by with_unfolding_all exact (l.b.YS.geq :))
  rho := (by with_unfolding_all exact (l.b.YS.rho :))
  chi := (by with_unfolding_all exact (l.b.YS.chi :))
  eF := (by with_unfolding_all exact (l.b.YS.eF :))
  bsup := (by with_unfolding_all exact (l.b.YS.bsup :))
  act := by with_unfolding_all exact (l.b.YS.act :)
def exponentOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpTied (w.st (oTw x (thTw (Dof x) th)).Z).toD7 :=
  (dof_oTw x (thTw (Dof x) th)) ▸ (bsTw l.b.Bs th).exp
def rowPsiOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    ∀ i : Fin (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.m,
      Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (oTw x (thTw (Dof x) th)).Z).toD7 i)
        (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
end GlobalTheory.HeightCounting.Up
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc
theorem nonempty_hyps_of_allRows_alt : StandardLattice.SiegelMassRatioCM → LitThin → Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → Formalism.L2.SG.RowsPos.TypeP → Formalism.L2.SG.RowsPos.RowNGP → Formalism.L2.SG.RowsPos.RowMainEqP → (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → _root_.GlobalTheory.Fc.AllRowsAlt KP Q Q' Lk N DR → Nonempty (_root_.GlobalTheory.Fc.HypsAlt N DR) := by
  intro hP hLit hWu hRF hTy hNG hM hU hG KP Q Q' Lk N DR hc hx hA
  obtain ⟨R30, hR30, c30, cIc, hb30, hpos, r30⟩ := hA.c30
  have rTu := Row.rowL (KP := KP) (Q := Q) largeBaseProperty_true (_root_.GlobalTheory.T.hTu_cTmin_of_genusMass hU hG Q' Lk)
  have hall := RowL.and (hA.hn4 : RowL KP Q Q' Lk fun 𝒜 _ => R0.ClassCountBoundAllPoints 𝒜) <|
    RowL.and (hA.jOn : RowL KP Q Q' Lk fun 𝒜 _ => R0.H_jOn 𝒜) <|
    RowL.and (hA.hInstR : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.H_hInstR 𝒜) <|
    RowL.and (hA.aC2 : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.DivisionSecondComplementAdmissible 𝒜) <|
    RowL.and (hA.aP10 : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.LevelPrimeColumnValuationsClosed 𝒜) <|
    RowL.and (hA.aAtG : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.H_aAtG 𝒜) <|
    RowL.and (hA.aPt0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.ReferenceChainEvaluationAdmissible 𝒜) <|
    RowL.and (hA.aPtTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPtTw 𝒜) <|
    RowL.and (hA.aPer0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPer0 𝒜) <|
    RowL.and (hA.aPerTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPerTw 𝒜) <|
    RowL.and (hA.tie : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_tie 𝒜) <|
    RowL.and (hA.hRB : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.P_hRB_alt)) <|
    RowL.and (hA.hTw : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.TwistBundleCondition)) <|
    RowL.and (hA.hPA : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition)) <|
    RowL.and (hA.hLamP : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition)) <|
    RowL.and (hA.hDivG : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition)) <|
    RowL.and (hA.hDcPtG : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.DecompositionPointBundle)) <|
    RowL.and (hA.selJ : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition)) <|
    RowL.and (hA.sLp : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionLpBound) <|
    RowL.and (hA.sO : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionOrderBound) <|
    RowL.and (hA.hServ : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionServesFamily) <|
    RowL.and (hA.zL : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionZeroLocus) <|
    RowL.and (hA.hTF : RowL KP Q Q' Lk fun 𝒜 _ => R1.H_hTF 𝒜) <|
    RowL.and (hA.rRows : RowL KP Q Q' Lk (_root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR)) <|
    RowL.and (hA.nRest : RowL KP Q Q' Lk fun 𝒜 _ => N (GlobalTheory.Cp.D3 3 𝒜)) <|
    RowL.and (⟨R30, hR30, r30⟩ : RowL KP Q Q' Lk _) rTu
  obtain ⟨𝒜, σ, hE, hD, -, hn4, jOn, hInstR, aC2, aP10, aAtG, aPt0, aPtTw, aPer0, aPerTw, tie, hRB, hTw, hPA, hLamP, hDivG,
    hDcPtG, selJ, sLp, sO, hServ, zL, hTF, rRows, nRest, ⟨h30, irrC⟩, hTu⟩ :=
    UpperTheory.Top.classSel hP (fun D => hU D) KP Q Q' _root_.GlobalTheory.Fc.BundleCondition Lk _ (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) hc hx hall
  have s3 : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm := fun Fm h => ((GlobalTheory.T.workingFamClass_copies_eq_frozen.1 𝒜 _ Fm).1).1 h
  have s1 : ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm → W1 𝒜 Fm :=
    fun Fm h => ((GlobalTheory.T.workingFamClass_copies_eq_frozen.1 𝒜 _ Fm).2).1 h
  exact ⟨{
    𝒜 := 𝒜
    σ := σ
    cT := fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y
    hEx := fun hM la G hla hH => working_classes_frozen.2 _ _ (fun hM' => hE hM' la G hla hH) hM
    hduty := fun Fm h => GlobalTheory.T.workingFamClass_copies_eq_frozen.2 _ Fm (hD _ Fm h).1
    hRB := fun Fm hc x hx _ i => hRB Fm hc x hx i
    hTw := fun Fm hc x hx _ i => hTw Fm hc x hx i
    hPA := fun Fm hc x hx _ i => hPA Fm hc x hx i
    hLamP := fun Fm hc x hx _ i => hLamP Fm hc x hx i
    hDivG := fun Fm hc x hx _ i => hDivG Fm hc x hx i
    hDcPtG := fun Fm hc x hx _ i => hDcPtG Fm hc x hx i
    hTu := hTu
    hn4 := Formalism.MainNotions.Pk.Closed.sub hn4 s1
    hLit := hLit
    hWu := hWu
    hRF := hRF
    hTF := hTF
    c30 := c30
    hc30 := hb30
    sTy := hTy
    sNG := hNG
    sM := hM
    sLp := sLp
    sO := sO
    h30 := h30
    hInstR := fun Fm hc x hx _ i => hInstR Fm hc x hx i
    selJ := fun Fm hc x hx _ i => Classical.choice (selJ Fm hc x hx i)
    jOn := Formalism.MainNotions.Pk.Closed.sub jOn s3
    hMt := fun Fm h => (hD _ Fm h).2
    rRows := rRows
    aPt0 := Formalism.MainNotions.Pk.Closed.sub aPt0 s3
    aPtTw := Formalism.MainNotions.Pk.Closed.sub aPtTw s3
    aPer0 := Formalism.MainNotions.Pk.Closed.sub aPer0 s3
    aPerTw := Formalism.MainNotions.Pk.Closed.sub aPerTw s3
    aP10 := Formalism.MainNotions.Pk.Closed.sub aP10 s3
    aAtG := Formalism.MainNotions.Pk.Closed.sub aAtG s3
    aC2 := Formalism.MainNotions.Pk.Closed.sub aC2 s3
    hServ := hServ
    cIc := cIc
    hcI := hpos
    irrC := irrC
    zL := zL
    tie := Formalism.MainNotions.Pk.Closed.sub tie s3
    hU := hU
    hG := hG
    nRest := nRest }⟩
end GlobalTheory.Fc
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.trivial_piece_mem_base_change : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ → SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  first | exact @_root_.GlobalTheory.MuBlockLoc.mu_block_mem_alt | exact _root_.GlobalTheory.MuBlockLoc.mu_block_mem_alt | (intros; apply _root_.GlobalTheory.MuBlockLoc.mu_block_mem_alt <;> assumption)
end
end

section



section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pack
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RealPackage {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) : Type 1 where
  P : RowSideFamily O.ex
  Dc : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Zsc S
def realPackageOfBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S :=
  ⟨b.P, b.C.c.face, b.C.Sp, GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c, b.B⟩
def realPackageOfRealInput {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : R3.TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S) :
    _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S := ⟨R3.divisionPairOfAdelicFormsFaceColumnsData x, x.F.Dc, x.F.Sp, x.F.Zsc, _root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y⟩
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure TwistedBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) : Type 1 where
  intersectionNumber_baseChange : R3.Holds x.R x.F
  y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S
  r : _root_.GlobalTheory.Mem.R3.RecursiveInput y
  eq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y
  HD : _root_.Formalism.L2.HostDatumWithTies b.R.T.toTiedDataS
end Pack
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
def WPt.saturationAtWeightedPoint (q : WPt p.s K) :
    SAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 q.x.what₂.r.Y.eE fun u => (q.x.col.C.forms u).to0 := q.x.sx.1
set_option genInjectivity false in
set_option genSizeOfSpec false in

structure BundleWitness (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) : Type 1 where
  x : R3.TwIn q.O.ex
  a : R3.TwArgs q.O.ex q.x.what₂
  ax : HEq a.x x
  y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x
  recPin : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q b.R
  s : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (b.R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
    HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S ∧ b.S = sS.toRealSpectralMatching b.R
  pt : HEq y.y.tS q.saturationAtWeightedPoint.t ∧ y.y.cS = q.saturationAtWeightedPoint.c
  sx : HEq y.y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk)
  eF : HEq y.y.nexp.eF q.core_data_of_point.row.nexp.eF
  fi : HEq y.y.nexp.fi q.core_data_of_point.row.nexp.fi
  uS : y.y.uS = 1
  parts : (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r).PartsRow
  cW : HEq b.C.c.W q.B.wts ∧ HEq b.C.c.Xg q.x.what₂.r.z.Xg
  d3b : HEq y.HD.d3b q.x.pin.d3b
  side : _root_.Formalism.L2.SelectedSideOfRealRecord b.R (R3.divisionPairOfAdelicFormsFaceColumnsData x) (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r) y.HD q.core_data_of_point.a.Pq
  colPins : _root_.Formalism.L2.DIV.ColumnCharactersCompatible b.C.toS
def BundleLinkage (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.LkT _root_.GlobalTheory.Fc.BundleCondition :=
  linkOf (𝒮 := p.s) (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ q _ b => Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := p) q b)
end GlobalTheory.Mem.Top.Bl
end
end
end

section



section
noncomputable section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.SerCopy


namespace GlobalTheory.LayerMove.SerUp
variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C} (o : Oth W) (V' : DivStage B C W) (S' : SStage B C W)
variable {o} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 o.L.D.what₂.LL G Pl0 I0 (List ℕ) T o.L.D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks o.L.D.what₂.LL] {R : RealDat3 o.L.D A3 Ks}
  {cG : G0 R.Pg o.L.D.R.r ≃* G0g o.L.D.nd} {S : RatDat o.L.D.ntw} {YS : NExpRealS R cG S}
  {v₀ : ∀ (j : Fin o.L.D.R.m) (σ : o.L.D.what₂.LL →+* ℂ), (R.MW j σ).Vec}
end GlobalTheory.LayerMove.SerUp
end
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
open GlobalTheory.LayerMove

theorem _root_.GlobalTheory.T.geo_heq_geoHalf_of_same : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → HEq t'.r.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : _root_.GlobalTheory.HeightCounting.NAllCAlt (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq') := by
  intro K B f T w Z Wt S' N h nch p0 t p0' t' hs hg
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = (by with_unfolding_all exact ((GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) :)) := eq_of_heq ((by with_unfolding_all exact (hg :)))
  subst e7
  intro kKs hk YS kKs' hk' YS' hkk hfi heF a X' hX PV PV' hPV Pq Pq' hPq s
  have e8 : kKs' = (by with_unfolding_all exact (kKs :)) := eq_of_heq ((by with_unfolding_all exact (hkk :)))
  subst e8
  obtain ⟨fi', geq', rho', chi', eF', bsup', act'⟩ := YS'
  have e9 : fi' = (by with_unfolding_all exact (YS.fi :)) := eq_of_heq ((by with_unfolding_all exact (hfi :)))
  have e10 : eF' = (by with_unfolding_all exact (YS.eF :)) := eq_of_heq ((by with_unfolding_all exact (heF :)))
  subst e9 e10
  have e11 : X' = (by with_unfolding_all exact (((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp :)) := eq_of_heq ((by with_unfolding_all exact (hX :)))
  have e12 : Pq' = (by with_unfolding_all exact (Pq :)) := eq_of_heq ((by with_unfolding_all exact (hPq :)))
  subst e11 e12
  have e13 : (fun i => (PV' i).ψ) = (by with_unfolding_all exact ((fun i => (PV i).ψ) :)) := eq_of_heq ((by with_unfolding_all exact (hPV :)))
  have e14 : PV' = fun j => @Formalism.IndefR.principalLevelFrame.RowPsi.mk _ _ _ ((by with_unfolding_all exact ((PV ((j))).ψ : _))) ((by with_unfolding_all exact ((PV ((j))).inj : _))) ((by with_unfolding_all exact ((PV ((j))).into : _)))
      ((by with_unfolding_all exact ((PV ((j))).onto : _))) := funext fun j => SerUp.rowPsi_ext ((by with_unfolding_all exact ((congrFun e13 j) :)))
  subst e14
  exact ⟨@SerAt.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (ex := (by with_unfolding_all exact ((@SerUp.ex B w.C Z.W ⟨Z.V, Z.S, Z.N, Z.G⟩ (upL Z S' N h).V S' _ _ _ _ _ _ _ _ _ _ t.r.z.alg t.r.z.R t.r.z.cG _ YS
      t.r.z.geo.v₀ s.ex) :)))
    (bad := (by with_unfolding_all exact (s.bad :))) (ch := (by with_unfolding_all exact (s.ch :))) (join := (by with_unfolding_all exact (s.join :))) (sup := (by with_unfolding_all exact (s.sup :))) (off := (by with_unfolding_all exact (s.off :)))
    (lam := (by with_unfolding_all exact (((mvOf w Z S' N h).lam s.lam) :)))
    (lam_ok := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_ok s.lam_ok) :)))
    (lam_teich := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_teich s.lam_teich) :)))
    (lam_C := (by with_unfolding_all exact ((congrArg (mvOf w Z S' N h).cf s.lam_C) :)))
    (lam_q := (by with_unfolding_all exact (s.lam_q :)))
    (lam_tie := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_tie s.lam_tie) :)))⟩
end
end

section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefCore
theorem defCase_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M _ hm _ hW _ hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  obtain ⟨hp, hq, hr⟩ := hW.sig
  have hk := D.R.m_add_three_le_k
  have hq0 : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [hq]; rfl
    simpa [dat, hm] using this
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by
    have : (dat p i).p = D.R.k + ((i : ℕ) + 1) - 1 := by rw [hp]; rfl
    simp only [dat] at this
    omega
  refine ⟨⟨hq0, hp1, ?_, hJ.pins.2.1.2, hF, hJ.unf _ hj, ?_⟩, CompFin.finite_comp _ _, ?_, ?_⟩
  · exact goodAt_of_two_primes hJ.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  · exact (GlobalTheory.LevGeo.laws_core D p.T _ hJ hj).xiAbs
  · exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ _ _ (by omega)).1
  · intro σ hσ g
    exact GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.dict_mem_dom p.T hJ _ hj σ hσ g
end GlobalTheory.DefCore
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind

theorem _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.small_along_alt | exact _root_.GlobalTheory.Fc.Ind.small_along_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.small_along_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

theorem _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  first | exact @_root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip | exact _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip | (intros; apply _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip <;> assumption)
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
namespace GlobalTheory.ExpTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
def NumStAlt : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j, ∃ (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W ∧ NumOk P W
open Classical in
def ExponentSumStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w))
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j P W w
end GlobalTheory.ExpTie
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
namespace GlobalTheory.ShareOn
section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
end Model
section Point
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p _ _ => ∀ i, ModelAt p i (Fm.parT x hx ι).TO
def SharedWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  ShareW p i (1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3))
def BadWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  BadW p i (Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))))
end GlobalTheory.ShareOn
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.two_mul_log_card_Gp_le_b : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  first | exact @_root_.GlobalTheory.CovTop.two_log_card_levels_le_alt | exact _root_.GlobalTheory.CovTop.two_log_card_levels_le_alt | (intros; apply _root_.GlobalTheory.CovTop.two_log_card_levels_le_alt <;> assumption)
end
end
