module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle551
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle088
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle089
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle085
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle090
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
import Mathlib.Tactic.Basify
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
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop
namespace GlobalTheory.ClassSumPinLink
open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
section Pack
variable {D : D7} {O : Obj D}


def ReadAtAlt {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) : Prop :=
  ∃ Yr : R3.Read (A3 := k.P.A3) k.B.Q.Rl.toRealDat
      (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 O.ex.p0,
    (∀ (i : Fin D.R.m) (v : Fin ((k.P.A3.indefDown k.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (k.B.Q.Rl.toRealDat.WL
        (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 false i)) → D.what₂.LL),
      HEq v y → Yr.mj.eW i (k.P.I.jW i v) = (k.B.Q.Rl.FW i).j (sg0 D k.P.A3.A)
        (jDL k.B.Q.Rl (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 i y)) ∧
    GlobalTheory.HeightCounting.EMtTheta Yr k.B.Q.nexp O.ex.nch


theorem readAt_rpkX_of_eMtTheta {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : R3.TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S)
    (h : GlobalTheory.HeightCounting.EMtTheta x.Y y.nexp O.ex.nch) : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) := by
  refine ⟨x.Y, ?_, h⟩
  intro i v z hvz
  obtain rfl := eq_of_heq hvz
  exact x.Z.jW_read i v


theorem classSumPin_of_readAt_of_pDiv {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) (h : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)) (hD : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c (b.part t)) :
    GlobalTheory.ExportPin.ClassSumPin (b.part t).pt := by
  obtain ⟨Yr, h1, h2⟩ := h
  exact classSumPin_of_read (b.part t).pt Yr h1 h2 hD
end Pack
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink
open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX


theorem eMtTheta_of_args_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} (t : RowsT K w Z Wt ex.p0) (n : NchT w Z Wt ex.nch) (c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n)
    (a : R3.TwArgs ex t) (x : R3.TwIn ex) (ax : HEq a.x x) {Sx : RatDat (w.st Z).toD7.ntw} (E : NExpRealS x.R x.cG Sx)
    (hS : HEq Sx (ratDatR (D := (w.st Z).toD7) t.r.z.R t.r.z.cG c.row.kKs c.row.hk))
    (hF : HEq E.eF c.row.nexp.eF) (hi : HEq E.fi c.row.nexp.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta (D := (w.st Z).toD7) t.r.Y c.row.nexp ex.nch) : GlobalTheory.HeightCounting.EMtTheta x.Y E ex.nch := by
  cases ax
  exact eMtTheta_of_pack a.pack a.x.Y t.r.Y a.eW (eq_of_heq hS) E c.row.nexp hF hi h
end GlobalTheory.ClassSumPinLink
namespace GlobalTheory.ClassSumPinLink

theorem pIota_classSumPin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.Fc.Ind.IotaPointSummands _ _ c (b.part t) ∧ (_root_.GlobalTheory.Fc.Ind.DivisorPointSummands _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  intro hL N S Γ hN K q c b hb t
  refine ⟨?_, fun hD => ?_⟩
  · obtain ⟨sP, sS, -, -, hS⟩ := hb.s
    have key : ∀ S' : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt b.R, S' = sS.toRealSpectralMatching b.R → ∀ x : S'.X.B.I.E, HEq (S'.X.ιE x) x := by
      rintro S' rfl
      exact sP.pin
    exact key b.S hS
  · have hth : GlobalTheory.HeightCounting.EMtTheta hb.x.Y hb.y.y.nexp q.O.ex.nch := by
      obtain ⟨m⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
      exact _root_.GlobalTheory.ClassSumPinLink.eMtTheta_of_args_alt q.x.what₂ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q) hb.a hb.x hb.ax hb.y.y.nexp hb.sx hb.eF hb.fi m.1.th
    have hR : _root_.GlobalTheory.ClassSumPinLink.ReadAtAlt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
      rw [hb.y.eq]
      exact _root_.GlobalTheory.ClassSumPinLink.readAt_rpkX_of_eMtTheta hb.y.y hth
    exact _root_.GlobalTheory.ClassSumPinLink.classSumPin_of_readAt_of_pDiv b t hR hD
end GlobalTheory.ClassSumPinLink
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem pRows_of_parts_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.FiringPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.summandRealBound D O c b →
    _root_.GlobalTheory.Fc.Ind.summandPrimitive D O c b → _root_.GlobalTheory.Fc.Ind.FramePointSummands D O c b → _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.CompatibilityConditions →
    _root_.GlobalTheory.Fc.Ind.RowPointSummands D O c b := by
  intro D O c b hF hB hP hFr hD hN hG hT
  exact
    { exAt := hF.1
      jEvBar := hF.2.1
      geoAct := hF.2.2.1
      evInj := hF.2.2.2
      ioExt := hB.ioExt
      oneMap := hB.oneMap
      prim := hP.1
      sep := hP.2
      ok := b.ok1
      framesOK := b.B.Q.frames hFr
      divRows := hD
      psi := b.psi
      d0 := _root_.GlobalTheory.T.ind_piece_degree_zero D O c b
      export_ := hN
      goodFT := hG
      w1 := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
      ties := hT }
end GlobalTheory.Fc.Ind
end
end

section



section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.lift_recursion_of_gram_bound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive := by
  first | exact @_root_.GlobalTheory.CovTop.liftRecursive_of_gram | exact _root_.GlobalTheory.CovTop.liftRecursive_of_gram | (intros; apply _root_.GlobalTheory.CovTop.liftRecursive_of_gram <;> assumption)
end
end

section



section

theorem _root_.GlobalTheory.T.set_at_of_size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt <;> assumption)
end
end

section



section

theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt <;> assumption)
end
end

section



section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.sum_c_of_deep_good : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := by
  first | exact @_root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | exact _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | (intros; apply _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt <;> assumption)
end
end

section



section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.uniform_lower_bound_of_sums' : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.HeightCondition → _root_.GlobalTheory.CovTop.CoverHeightSum → _root_.GlobalTheory.CovTop.SumBoundCondition → _root_.GlobalTheory.CovTop.UniformLowerBound := by
  first | exact @_root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps | exact _root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps | (intros; apply _root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps <;> assumption)
end
end

section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.gram_MK_spans_of_gramAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m),
    _root_.GlobalTheory.CovTop.RowsTAlt p → GramAt p i →
    Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) = ⊤ := by
  first | exact @_root_.GlobalTheory.CovTop.SpanMK.span_MK_eq_top_alt | exact _root_.GlobalTheory.CovTop.SpanMK.span_MK_eq_top_alt | (intros; apply _root_.GlobalTheory.CovTop.SpanMK.span_MK_eq_top_alt <;> assumption)
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_unit_root_ze_leafC_of_square_nonzero (p : PtAt ex Csz) (hp : p.PointConditions') {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (ht : TieAt d a)
    (hwf : (Df p).WF) (hR : ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false)
    (hQ : (∀ b u, ConvK a.ch b u) ∧ (∀ u, (∀ b, psiK a.ch b u = 0) → u = 0) ∧
      (∀ i j t, SquareNonzero a.ch.W a.ch.S.B a.ch.rm t i j ∧ a.ch.c i j t ≠ 0) ∧
      (a.ch.FieldOK → ∃ κ ze, FormulaAt a.ch κ ze)) :
    ∃ ze : Tup p → D.what₂.LL, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
      LeafC (p.S false) (d.data ze ∅ fun _ => 0) := by
  classical
  obtain ⟨hL, hI, hC, hF⟩ := hQ
  obtain ⟨κ, ze, hz, hform⟩ := hF ht.ok.field
  obtain ⟨R0, hR0⟩ := hR
  obtain ⟨hinj, hrow⟩ := _root_.GlobalTheory.T.iC_iota_mulVec_eq_iC p hp
  have hzK : ∀ t, ze t ≠ 0 := fun t h => by
    obtain ⟨n, hn, e⟩ := hz t
    rw [h, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hze : ∀ t, D.what₂.embLL (ze t) ≠ 0 := fun t => (map_ne_zero _).2 (hzK t)
  have hc0 : ∀ t, cTot a.ch t ≠ 0 := fun t => (cTot_ne_zero_iff _ _).2 fun i j => (hC i j t).2
  have key : ∀ t (y : Fin ((Df p).nV t) → D.what₂.LL) (b : Fin d.n),
      D.what₂.embLL (ze t) * cTot a.ch t * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
        κ * D.what₂.embLL ((d.V t).mulVec y b) := by
    intro t y b
    rw [← _root_.GlobalTheory.T.theta_j_ev0_eq_ic_pq p hp t y, ht.sums t (TieModel.inUse p t) y b]
    exact hform t _ (_root_.GlobalTheory.T.eV0_mem_goodF' p hp t y) b
  have lin : ∀ (b : Fin d.n) (z : Fin (p.S false).D → D.what₂.LL),
      psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding z)) =
        ∑ k, D.what₂.embLL (z k) *
          psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1)) := by
    intro b z
    have := out_sum_tw (twAt D.what₂.embLL p.P.A3.A.v0) (psiL a.ch b (hL b))
      ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) (cpt p.P.A3.fam3.base3.v0.embedding z)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact congrArg (· * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))) (twist_conj_base_embedding_eq p (z k))
  have hκ : κ ≠ 0 := by
    intro hκ0
    have h0 : ∀ y, (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y)) = 0 := by
      intro y
      apply hI
      intro b
      have := key p.P.A3.fam3.base3.μ0 y b
      rw [hκ0, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (hze _) (hc0 _))
    have i0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) := ⟨0, R0.pos⟩
    obtain ⟨y, hy⟩ := hwf.Pq_surj p.P.A3.fam3.base3.μ0 (Pi.single i0 1)
    have h1 := h0 y
    rw [hy] at h1
    have h2 := congrFun (hinj (h1.trans (map_zero _).symm)) i0
    simp [cpt] at h2
  let c0 : ℂ := κ⁻¹ * D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) * cTot a.ch p.P.A3.fam3.base3.μ0
  let Ψc : Matrix (Fin d.n) (Fin (p.S false).D) ℂ := Matrix.of fun b k =>
    c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))
  let ze' : Tup p → D.what₂.LL := fun t => ze t / ze p.P.A3.fam3.base3.μ0
  let r : Tup p → D.what₂.LL := fun t => ze' t * ∏ ij, d.rq t ij
  have hmain : ∀ t ∈ (Set.univ : Set (Tup p)),
      Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL = ((r t)⁻¹ • d.V t).map D.what₂.embLL := by
    intro t _
    have H : ∀ y : Fin ((Df p).nV t) → D.what₂.LL, ∀ b,
        (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b := by
      intro y b
      have e1 : Ψc.mulVec (cpt D.what₂.embLL (((p.S false).ι t).mulVec (((Df p).Pq t).mulVec y))) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← hrow, lin, Finset.mul_sum]
        simp only [Matrix.mulVec, dotProduct, Ψc, Matrix.of_apply, cpt]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e3 := (TieModel.ratio_eq ht t).2
      have eL : (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← Matrix.mulVec_mulVec, ← cpt_mulVec, ← Matrix.mulVec_mulVec]
        exact e1
      have eR : (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (D.what₂.embLL (ze t) / D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) *
            (cTot a.ch t / cTot a.ch p.P.A3.fam3.base3.μ0))⁻¹ * D.what₂.embLL ((d.V t).mulVec y b) := by
        rw [← cpt_mulVec]
        show D.what₂.embLL ((((r t)⁻¹ • d.V t).mulVec y) b) = _
        rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [show r t = ze t / ze p.P.A3.fam3.base3.μ0 * ∏ ij, d.rq t ij from rfl, map_mul, map_div₀, e3]
        rfl
      have hP : psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
          κ * D.what₂.embLL ((d.V t).mulVec y b) / (D.what₂.embLL (ze t) * cTot a.ch t) :=
        eq_div_of_mul_eq (mul_ne_zero (hze t) (hc0 t)) (by rw [mul_comm]; exact key t y b)
      rw [eL, eR, hP]
      exact mul_eq_one_of_covolume_identity _ _ _ _ _ _ hκ (hze t) (hze _) (hc0 t) (hc0 _)
    ext b col
    have := H (Pi.single col 1) b
    have hs : cpt D.what₂.embLL (Pi.single col (1 : D.what₂.LL)) = Pi.single col 1 := by
      funext i; by_cases hi : i = col <;> simp [cpt, hi]
    rw [hs, Matrix.mulVec_single, Matrix.mulVec_single] at this
    simpa using this
  have hbij : Function.Bijective ((p.S false).ι p.P.A3.fam3.base3.μ0).mulVec := (hR0 ▸ R0.l1c).1 _
  obtain ⟨⟨Ψ, -, hΨ⟩, -⟩ := GlobalTheory.complex_matrix_descends_of_rational_on_tuple D.what₂.embLL d.n (p.S false).D (Df p).dQ
    (Df p).nV (p.S false).ι (Df p).Pq d.V r Set.univ p.P.A3.fam3.base3.μ0 Ψc trivial hbij
    (hwf.Pq_surj _) hmain
  refine ⟨ze', by simp only [ze']; exact div_self (hzK _), fun t => ?_, Ψ, fun t _ => ?_⟩
  · obtain ⟨n, hn, e⟩ := hz t
    obtain ⟨m, hm, e'⟩ := hz p.P.A3.fam3.base3.μ0
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    show (ze t / ze p.P.A3.fam3.base3.μ0) ^ (n * m) = 1
    rw [div_pow, pow_mul (ze t), e, one_pow, pow_mul' (ze _), e', one_pow, div_one]
  · refine (hΨ t trivial).trans ?_
    show _ = (∏ ij, d.rq t ij)⁻¹ • ((ze' t)⁻¹ • d.V t)
    rw [smul_smul, mul_inv, mul_comm]
theorem oneMap_of_bundle_setAt_kernel_conditions (hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition) (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) (h1 : LinK) (h2 : InjK) (h3 : ConstK) (h4 : Formula2K) : _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap @Comparison₂ := by
  obtain ⟨CF0, hQ⟩ := hS.atPt (h1.and (h2.and (h3.and h4)))
  refine ⟨CF0, fun CF hCF => (hQ CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p hp q d hd => ?_⟩⟩
  obtain ⟨-, a, ht⟩ := hd
  obtain ⟨wf, R0, hR⟩ := hB p hp
  exact _root_.GlobalTheory.BigTop.Fun.exists_unit_root_ze_leafC_of_square_nonzero p hp d a ht wf ⟨R0, hR⟩ (q d.G d.W d.n a ht.ok)
end GlobalTheory.BigTop.Fun
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

theorem _root_.GlobalTheory.T.rank_gap_bound : _root_.GlobalTheory.BigTop.Fun.RankGapBound' := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.rankGapBound_alt | exact _root_.GlobalTheory.BigTop.Fun.rankGapBound_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.rankGapBound_alt <;> assumption)
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.type_data_unit_shift_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  first | exact @_root_.GlobalTheory.MiTop.linkComm_of_laws_alt | exact _root_.GlobalTheory.MiTop.linkComm_of_laws_alt | (intros; apply _root_.GlobalTheory.MiTop.linkComm_of_laws_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

theorem _root_.GlobalTheory.T.polynomial_descent_estimate' : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.desPol_alt | exact _root_.GlobalTheory.BigTop.Fun.desPol_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.desPol_alt <;> assumption)
end
end
