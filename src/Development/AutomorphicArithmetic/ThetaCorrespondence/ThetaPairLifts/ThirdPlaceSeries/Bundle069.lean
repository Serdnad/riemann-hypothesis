module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Formalism.LocalToGlobal.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle063
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.LocalToGlobal.PtKOfReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle426
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle059
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.MiS
namespace GlobalTheory.Fam
@[reducible] def packB_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : _root_.GlobalTheory.MiS.RealPackAlt O.ex :=
  letI := b.B.alg
  { R := b.R, S := b.S, P := b.P, Dcf := b.C.c.face, Spf := b.C.Sp, Zscf := GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c,
    Ks := b.B.T.Q.c.F, Q := b.B.Q }
structure BundlePointConditions {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Prop where
  join : Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q)
  dc : DcPtG b.P
  frames : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q
  see : _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q
  ex : b.B.Q.Rl.toRealDat.ExAt
  prim : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
  fin : Formalism.L2.SG.PackageTie2.FinX b.S.Y
  gapS : GlobalTheory.Count.GapGe b.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  rS : 1 ≤ D.R.rS
end GlobalTheory.Fam
end
end
end

section




section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.Top4Wire2
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
def DefRowsFAlt (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) {eps : ℝ} (Fm : FamP eps)
    (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) [IsTotallyComplex (Fm.D x i).what₂.LL]
    (C CH : ℝ) : Prop :=
  ∀ (hok1 : (selP Fm hc x hx h i).1.A3.fam3.Ok3 1) (hsep : (selP Fm hc x hx h i).1.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (selI Fm hc x hx h i).Rl (faceT (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i)) (selI Fm hc x hx h i).sEE (hkCan (selP Fm hc x hx h i).1.A3) C CH) (hI : PassIn3 (selI Fm hc x hx h i).Rl (faceT (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : NumFactsAt Fm x i (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 lam0 C0 ce Sw C1)
    (NuC : ∀ w, Submodule (𝓞 (Fm.D x i).what₂.LL) (Fin (((selC Fm hc x hx h i).c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs).a w) → (Fm.D x i).what₂.LL))
    (I : DivisionCompatibilityDataThreeSided (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.toIndefData (Fm.ex x hx i).p0 ((selC Fm hc x hx h i).c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs)),
    DivTied3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.toIndefData (Fm.ex x hx i).p0 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I (selP Fm hc x hx h i).1.I → ∀ u, RowsU (selC Fm hc x hx h i).c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _)
          (letterOf (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 u) ((Fm.D x i).mem u).A.T (Fm.L x i).Nc lam0 C0 ce Fm.Csz Sw C1 (H u)) (I.wU u) (Cons.nuOf (Fm.L x i) u (I.eNu u))
theorem finite_T_of_squareIntegrableColumns {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex}
    (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : Finite P.T := by
  rw [K.tEq]
  exact ((Finset.finite_toSet K.TU).insert _).to_subtype
end Formalism.L2.Top4Wire2
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.link_alt_alt_bis : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3)
    (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (sTy : Formalism.L2.SG.RowsPos.TypeP)
    (sNG : Formalism.L2.SG.RowsPos.RowNGP)
    (sM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩))
    (sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩)
    (h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank), Closed (D3 3 𝒜) fun Fm _ => TuSize Fm → LinkS Fm 3 := by
  intro 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have sRes : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.ResidEv Fm := Formalism.L2.SG.ResidEvFree.residEv_closed_free (D3 3 𝒜)
  let ssel : Formalism.L2.SG.ThmSOwn.SSel (D3 3 𝒜) :=
    fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩
  have lS := Formalism.L2.SG.ThmSOwn.theoremS_transport_link_zero (C0 := 3) (D3 3 𝒜) ssel hWu hRF
    (fun Fm hc x hx h i => (selS Fm (d3_a hc) x hx h i).locTied)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.instTie_of_record (selS Fm (d3_a hc) x hx h i).inst
      (Formalism.MainNotions.RT.volTie_of_realTied _ ((sel Fm (d3_a hc)).2 x hx h i).T.theta.real) (hInstR Fm (d3_a hc) x hx h i).1
      (hInstR Fm (d3_a hc) x hx h i).2 (Fm.ties x i).cdScale_tie)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.one_le_qqI_of_inst (selS Fm (d3_a hc) x hx h i).inst)
    hTF c30 (by linarith) hc30 sRes sTy sNG sM sLp sO h30
  exact lS
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem bothRowsFromSiegelWeil_alt :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
      (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
        Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 :=
  fun hSW => _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio (GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil hSW)
end GlobalTheory
end
end
