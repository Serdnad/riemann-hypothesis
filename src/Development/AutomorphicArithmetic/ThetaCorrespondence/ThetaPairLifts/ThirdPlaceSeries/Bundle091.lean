module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Formalism.LocalToGlobal.PtKOfReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle072
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle449
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle580
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Formalism.PieriBlockIdeals.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.Bundle001
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.Fc
section Def
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling _root_.Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
open GlobalTheory.EX GlobalTheory.EX.OB
abbrev qRealOfBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) :
    _root_.Formalism.IndefR.IndefiniteRealisation b.R b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c) b.S b.B.T.Q.c.F := b.B.Q
def DefiniteSideCondition : _root_.GlobalTheory.Fc.R1.DefiniteSideType := fun D O c b C CH =>
  ∀ (hok1 : b.P.A3.fam3.Ok3 1) (hsep : b.P.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (_root_.GlobalTheory.Fc.qRealOfBundle b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) (_root_.GlobalTheory.Fc.qRealOfBundle b).sEE (hkCan b.P.A3) C CH) (hI : PassIn3 (_root_.GlobalTheory.Fc.qRealOfBundle b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : ∀ u, (ofRecord D O.L b.DH.1.1 b.DH.1.2).NumFacts (letterOf D O.L b.DH.1.1 b.DH.1.2 u) O.L.Nc lam0 C0 ce c Sw C1)
    (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs).a w) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs)),
    DivTied3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I b.P.I → ∀ u, RowsU b.C.toS.c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord D O.L b.DH.1.1 b.DH.1.2) (Equiv.refl _)
          (letterOf D O.L b.DH.1.1 b.DH.1.2 u) (D.mem u).A.T O.L.Nc lam0 C0 ce c Sw C1 (H u)) (I.wU u) (Cons.nuOf O.L u (I.eNu u))
end Def
end GlobalTheory.Fc
end
end
end

section



section
open Matrix NumberField
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace GlobalTheory.QuotientNormCoisometry
section Bound
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open _root_.Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Bound
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize in
theorem leafHeightMapBound_tie_of_infK : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → InfK → _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound @Comparison₂ := by
  intro hB hS hI
  obtain ⟨CF0, hI⟩ := hI
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hI⟩ := hI CF hCF
  obtain ⟨e1, he1, hS⟩ := hS
  refine ⟨e1, he1, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := hS eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨x1, hx1⟩ := hK Fm CH hc hL
  refine ⟨max C0 (max CF 0), fun C hC => ?_⟩
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x0, hx0⟩ := hI eps C (le_of_max_le_left hC)
  refine ⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hset := hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser
  have key := hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset
    a.ch ha.ok.is a.atScale ha.ok.field
  have hWF := (hB p hp).1
  have hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL,
      IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧
      ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ *
        (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹ =
        ((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding := fun v =>
    Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)
  have k3 := key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')
  rw [htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]
  exact k3.trans (bound_le d hC0 hCF')
end GlobalTheory.QuotientNormCoisometry
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.Top.Bl
theorem has3_neo_of_localLanglands_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (hB : ExistsUnlocalizedSaturatedState) (hA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL) (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL)
    (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) (hB0 : _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep) (hB1 : _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) (hB2 : _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep) (hC : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL) (hFin : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep)
    (S : SExt) (Γ : GeoP) : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) := by
  have h := StepW.and hB (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
  refine h.trans (StepW.of_all ?_)
  intro K B f T w _ _ H
  obtain ⟨⟨P, x, sat, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
  obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
  obtain ⟨imt⟩ := mt P x1
  obtain ⟨irat⟩ := rat P x1 la
  have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
  obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
  obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
  obtain ⟨sc⟩ := c P x4 l2
  obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ ⟨p4 (p3 p2), sat⟩
  exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


namespace GlobalTheory.TwInputs
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
structure GalSideAlt (D : D7) : Type 1 where
  wd : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : GlobalTheory.HeightCounting.LabTrue D wd
  cf : CharFrame D
  chr : GlobalTheory.HeightCounting.CharSide D cf
  triple : _root_.GlobalTheory.Triple.IsGaloisTriple D
  lam : GlobalTheory.LamTie.LamDat D
  lamOk : lam.Ok
  lamTie : GlobalTheory.LamTie.IsLamTie D.ntw lam
  rank : 100 ≤ D.R.r
  primes : ∀ k, 2 * D.R.r ≤ D.host.g k
section Abstract
end Abstract
end GlobalTheory.TwInputs
end
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem sc_of_sck_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (h : _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL) : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H P x l => by
    obtain ⟨s, h1, h2⟩ := exists_settings_conj (D := Dof x) l.a.elem.star l.b.Bs.cover
    obtain ⟨c, -⟩ := H P x l s h1 h2
    exact ⟨c⟩)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem sFino_of_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (h : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep := by
  refine StepW.trans h (StepW.of_all fun K B f T w _ _ H P x l S Γ hl => ?_)
  obtain ⟨Z, v, h1, h2⟩ := H P x l S Γ hl.1
  exact ⟨Z, { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
              chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨P, x, l, hl, h1, h2⟩⟩ }, h1, h2⟩
theorem exists_pre_point_with_henselian_level {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {S : SExt} {Γ : GeoP} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z c) (e : ExportAt (w.st Z).toD7 c.O.nch c.O.xd) :
    ∃ (P : Pre2 K w) (x : St P) (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ ∀ A, Nonempty (Seed (Dof x) A) := by
  obtain ⟨P, x, l, hl, hW, hk⟩ := b.nx.2.2.down
  have key := (TupTieW.tupTied_of_muIsW (w.st Z) f T c.Wt c.xi c.mu).1
  refine ⟨P, x, l, hl, GlobalTheory.HeightCounting.Up.nonempty_seed_of_kept (Dof x) (w.st Z).toD7 l.c.ch c.O.nch c.O.xd hk rfl (fun v v₀ hv ht => ?_) l.c.side.nct
    l.c.side.choice.twI_conj ?_ B.coeffGaloisSubfield_isGalois (twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.st Z).toD7 c.O.nch c.nch_tie B.coeffGaloisSubfield_isGalois) e b.nx.2.1.1.1.xd⟩
  · obtain rfl : v = v₀ := eq_of_heq hv
    exact (key v).2 (hW ▸ (twisted_st x v).1 ht)
  · exact (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).2.1.subset fun v hv => (twisted_st x v).1 hv
end GlobalTheory.HeightCounting.Up
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
theorem levelSq_yBound_atRec_alt :
    _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun c _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ r O hO => ?_⟩⟩⟩
  obtain ⟨st, td⟩ := hO.1.depth
  letI := hostAlg (Fm.D x i)
  have g1 : O.g1 = (Fm.D x i).host.g 0 := td.jets_eq_fact
  have g2 : O.g2 = (Fm.D x i).host.g 1 := td.g2_eq
  have f1 : O.f = ((Fm.D x i).R.f : ℝ) := td.f_eq
  have k1 : O.k = ((Fm.D x i).R.k : ℝ) := td.k_eq
  have hrec : (R2 p).grp_record := by
    obtain ⟨plg, iso, -, h2, h3, h4⟩ := p.grpRecPin
    exact ⟨p.R.eG.trans p.cG, plg, iso, h2, h3, h4⟩
  have yb : ∀ {large₂ : SizeData₂ (Fm.D x i)} {Pm : ParameterChoice' (Fm.D x i) large₂}, ParamsT (Fm.D x i) large₂ Pm →
      LeafYBound (onOf (R2 p) (F2 p) c (supArgs (R2 p))) := fun {_ Pm} _ =>
    leafYBound (F := F2 p) c (supArgs (R2 p)) Pm
  refine ⟨?_, ?_⟩
  · have := leafLevelSq (F := F2 p) c (supArgs (R2 p)) hrec
    unfold LeafLevelSq
    rw [g1, g2]
    exact this
  · have := yb (Fm.parT x hx i)
    unfold LeafYBound OnObj.y
    rw [g1, g2, f1, k1]
    exact this
end GlobalTheory.BigOn
end
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
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
namespace GlobalTheory.ExpTie
theorem atPts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (h' : _root_.GlobalTheory.BigOn.AtPtsAlt Q') : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (h.and h') fun Fm _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm =>
      ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm, hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩
theorem atPts_mono {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (H : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i),
      Q Fm x hx i p → Q' Fm x hx i p) : _root_.GlobalTheory.BigOn.AtPtsAlt Q' :=
  Closed.imp h fun Fm _ _ ⟨a, ha⟩ => ⟨a, fun x hx hle i p hp hm => H Fm x hx i p (ha x hx hle i p hp hm)⟩
end GlobalTheory.ExpTie
end
end
end

section



section
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.BigOn
theorem typePrimes_gt_three_r_alt :
    _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ k : Fin 2, 3 * (Fm.D x i).R.r < (Fm.D x i).host.g k := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i _ _ _ k => three_r_lt_g_of_params _ _ (Fm.params x hx i) k
end GlobalTheory.BigOn
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
theorem atPts_h_lt_g_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ =>
    ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ i _ _ _ j a => parOf_h_lt_g (Fm.L x i) (Fm.params x hx i) j a⟩⟩⟩
end GlobalTheory.ExpTie
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
  GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
theorem rows_big_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ,
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  refine ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_large_parameter_bound eps (2 * |Fm.Ct| + 2) heps
  refine ⟨max x0 2, fun x hx hle i _ _ _ j => ?_⟩
  have hCt := Fm.Ct_eq x i
  refine ⟨(Fm.L x i).sc.X', x ^ (2 * |Fm.Ct| + 2),
    rows_big_of_largeParameter (Fm.L x i) (Fm.params x hx i) j eps _ x (Fm.L_x x i hx) (Fm.L_eps x i) ?_ ?_
      ((le_max_right _ _).trans hle) (hx0 x ((le_max_left _ _).trans hle))⟩
  · rw [hCt]
    linarith [le_abs_self Fm.Ct]
  · rw [hCt]
    linarith [le_abs_self Fm.Ct, abs_nonneg Fm.Ct]
end GlobalTheory.ExpTie
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
theorem GlobalTheory.LiftWeightForced.atPts_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ,
    Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i)
      (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ j τ => GlobalTheory.LiftWeightForced.isLamPrime_lamLdef (Fm.D x i) j τ⟩⟩
end
end
end
