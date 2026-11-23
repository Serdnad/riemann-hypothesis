module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle067
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle873
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle063
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassRep
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ActsUnitarilyOfClauses
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.exists_isCuspParam_of_bc_good_index : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ → SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa → D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  first | exact @_root_.GlobalTheory.RowCuspFromLift.exists_isCuspParam_of_liftAt_good_index | exact _root_.GlobalTheory.RowCuspFromLift.exists_isCuspParam_of_liftAt_good_index | (intros; apply _root_.GlobalTheory.RowCuspFromLift.exists_isCuspParam_of_liftAt_good_index <;> assumption)
end
end

section



section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
end
@[reducible] def parametersOfDependence (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL :=
  _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
end GlobalTheory.Mem.Top.Bl
end
end
end

section



section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.kernel_columns_from_ties_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  first | exact @_root_.GlobalTheory.ColRows.rowsU_of_colPins_alt | exact _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt | (intros; apply _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.Ind
theorem small_along_alt : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  intro 𝒜 σ hS hP
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm CH hw _ _ => ⟨0, le_refl _, fun C _ => ?_⟩
  obtain ⟨x0, hx0⟩ := GlobalTheory.four_f_r_le_min_g_family _ Fm
  refine ⟨x0, fun x hx hx0' i => ?_⟩
  have hA := hx0 x hx0' hx i
  have hs := hS Fm (w3_a hw) x hx i
  have hp := hP Fm (w3_a hw) x hx i
  refine ⟨fun w hw1 => ((σ Fm (w3_a hw) x hx i).muDef C CH).2.2.2 w |>.2 hw1, ?_, ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  · exact _root_.GlobalTheory.T.indefScale_theta_degree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Fm.D x i).tcLL hA (σ Fm (w3_a hw) x hx i).ok1 hp.1 C CH
end GlobalTheory.Fc.Ind
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
def pointOfRealisation (pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T P) {Del h0 : ℕ} (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) {c : ℝ}
    (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf (zscOf P Del h0 c) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex c where
  P := rowSideOfCompatibleThetaPair P
  Del := Del
  h0 := h0
  hDel := hDel
  hh0 := hh0
  Dcf := Dcf
  Spf := Spf
  gamDvd := pin.gamDvd
  T := B.T
  alg := B.alg
  R := B.Q.Rl
  charW := B.Q.charW
  zs := B.Q.zs
  s0 := B.Q.s0
  s1 := B.Q.s1
  dc := B.Q.dc
  stdChar := B.Q.stdChar
  signs := B.Q.signs
  cG := B.Q.cG
  Sx := B.Q.Sx
  nexp := B.Q.nexp
  stdV := B.Q.stdV
  stdX := B.Q.stdX
  host := B.Q.host
  err_eq := B.Q.err_eq
  vpos := B.Q.vpos
  κ := B.κ
  v₀ := B.v₀
  fw := B.fw
  bar := B.bar
  O := B.O
  pins := B.pins
  rhoGeo := B.rhoGeo
  equivAll := B.equivAll
  cTie := B.cTie
  phase := B.phase
  qGuard := Qp.qGuard
  hF := Qp.hF
  phsOne := Qp.phsOne
  prXunit := Qp.prXunit
  grpRecPin := Qp.grpRecPin
  fdiag := Qp.fdiag
  eGtie := Qp.eGtie
  betaStd := Qp.betaStd
  tupT := Qr.tupT
  hm := Qr.hm
  Tp := Qr.Tp
  tupXi := Qr.recR.tupXi
  tupAt := Qr.recR.tupAt
  tupTie := Qr.tupTie
  tupT_tup := Qr.tupT_tup
  muEq := Qr.muEq
def PointSummands.pt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : PtAt O.ex c :=
  _root_.GlobalTheory.Fc.Ind.pointOfRealisation b.pin b.DH.2.1 b.DH.2.2 b.B b.pins b.Rr
def conditionOnPoint (G : PtP) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O c b => G D O c b.pt
def RowPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => b.pt.PointConditions'
end GlobalTheory.Fc.Ind
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def SizeAtAlt : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i)
def SettingAtPoint : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i p =>
  GlobalTheory.GLq.ESerTie (Fm.D x i) → HidaSetting (Fm.L x i) p.R.toRealDat p.F.lv2
def CharacterAtPoint (Q : ChP) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  ∀ (G : Grid p CF) (W : G.Weil) (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK → Q a.ch
theorem SettingAtPoint.atPt (h : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) {Q : ChP} (hQ : Big Q) : _root_.GlobalTheory.BigTop.Fun.CharacterAtPoint Q := by
  obtain ⟨c, hQ⟩ := hQ
  refine ⟨c, fun CF hCF => h.imp fun {eps} Fm _ _ a => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hQ eps CF hCF
  obtain ⟨x₁, a⟩ := a
  refine ⟨max x₀ x₁, fun x hx hle i p hp G W n b hb => ?_⟩
  exact hx₀ _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _
    (a x hx (le_of_max_le_right hle) i p hp hb.eser) b.ch hb.is b.atScale
end GlobalTheory.BigTop.Fun
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
namespace GlobalTheory.ThmAUpper
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ChiGrid in
theorem qn_not_mem_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ)
    (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 →
      ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit w hw
  classical
  obtain ⟨htw, hxi⟩ := xiH_twisted p w hw
  have hl : D.ntw.l (ex.nch.twI (D.plEq.symm w)) = D.what₂.places.resChar (D.plEq.symm w) :=
    (hfit.1.setting.1 _ htw).1
  have hQ := hfit.1.cond _ htw
  have hlev := p.charW.base.lev
  have key : ∀ PP ∈ twPl d.G (p.R.mu w),
      ((D.what₂.places.resChar (D.plEq.symm w) : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hlP
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    obtain ⟨hloc, hW0⟩ := hPP
    have hQt : PP ∈ p.R.toRealDat.toLevCh.Q (p.R.mu w) := hloc.resolve_left hW0
    have hS1 : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ S1 D := fun h => hW0 (by
      rw [d.G.pl.w_Q _ PP hQt h]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem h))
    have hram : ¬ (p.R.toRealDat.toLevCh.xiH (p.R.mu w)).UnrAt PP := (hlev.Q_ram _ PP).2 (Or.inl hQt)
    rw [hxi] at hram
    by_cases hd : (p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w))).UnrAt PP
    · have hψ : ¬ (p.Tp.psi (D.plEq.symm w)).UnrAt PP := fun h => hram (hd.mul h)
      have hmem : PP ∈ ex.nch.Q (D.plEq.symm w) := by
        by_contra hn
        exact hψ (((p.Tp.psi_is _ htw).ram PP).2 hn)
      have hS0 : PP ∈ D.ntw.S0 (ex.nch.twI (D.plEq.symm w)) := D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [hl]; exact hlP)
      exact Finset.disjoint_left.1 hQ.2.1 hmem hS0
    · have hover : ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        unfold Formalism.L2.Host.CharFrame.delAt at hd
        split_ifs at hd
        · by_contra h
          exact hd (p.R.C.isDel'.unr PP fun h' => h (Or.inr h'))
        · by_contra h
          exact hd (p.R.C.isDel.unr PP fun h' => h (Or.inl h'))
      apply hS1
      rw [S1_mem_OmF]
      rcases hover with h | h
      · right; right; left
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
      · right; right; right
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
  intro hmem
  rw [Qn, Nat.cast_prod] at hmem
  obtain ⟨PP, hPP, hin⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  have : NeZero PP.asIdeal := ⟨PP.ne_bot⟩
  have hq : (Ideal.absNorm (PP.asIdeal.under ℤ)).Prime := Nat.absNorm_under_prime PP.asIdeal
  have : PP.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm PP.asIdeal
  rw [Ideal.absNorm_eq_pow_inertiaDeg' PP.asIdeal hq, Nat.cast_pow] at hin
  have hqw := w.isPrime.mem_of_pow_mem _ hin
  have hqP : ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h : algebraMap ℤ (𝓞 D.host.E) ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ) ∈ PP.asIdeal :=
      Ideal.absNorm_mem (PP.asIdeal.under ℤ)
    rw [eq_intCast, Int.cast_natCast] at h
    exact h
  have e := resChar_eq (D.plEq.symm w) hq (by rw [Equiv.apply_symm_apply]; exact hqw)
  exact key PP hPP (e ▸ hqP)
end GlobalTheory.ThmAUpper
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
theorem eV0_mem_goodF_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), eV0 p t y ∈ (p.P.A3.A.fam.R t).goodF p.P.A3.A.fam.X := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ t y
  set B := p.P.A3.A.fam.R t
  set F := p.P.A3.A.fam
  obtain ⟨u, hu⟩ := Formalism.IndefR.CxPass.PassRep.range_vE_le B F.X p.P.P0 p.P.ψ0 ⟨y, rfl⟩
  have hrange : LinearMap.range (B.vE ⟨F.X, ⊥, 1⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt F.X ⊥ 1)).mulVecLin :=
    (image_idempotent_spec _ _ (B.S.gaMat B.r (goodAt F.X ⊥ 1))).2
  obtain ⟨z, hz⟩ : (B.vE ⟨F.X, ⊥, 1⟩).mulVecLin u ∈ LinearMap.range (B.S.gaMat B.r (goodAt F.X ⊥ 1)).mulVecLin :=
    hrange ▸ ⟨u, rfl⟩
  refine ⟨B.S.basis.equivFun.symm z, B.S.basis.equivFun.injective ?_⟩
  rw [← CSD.gaMat_mulVec_equivFun, LinearEquiv.apply_symm_apply]
  simp only [Matrix.mulVecLin_apply] at hu hz
  rw [hz, hu]
  show _ = B.S.basis.equivFun (B.S.basis.equivFun.symm ((B.vE (F.lvl p.P.P0 p.P.ψ0)).mulVecLin y))
  rw [LinearEquiv.apply_symm_apply]
  rfl
end GlobalTheory.BigTop.Fun
end
end
end

section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
variable (Y : Cov p i)
def RowsTAlt : Prop := p.PointConditions' ∧ RecTied D L
def EventuallyAtAllPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p : Pt Fm x hx ι), _root_.GlobalTheory.CovTop.RowsTAlt p → Q x hx ι p
theorem EventuallyAtAllPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop}
    (h : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q) (h' : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q') : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => Q x hx ι p ∧ Q' x hx ι p := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  exact ⟨max a b, fun x hx hle ι p hp =>
    ⟨h x hx ((le_max_left _ _).trans hle) ι p hp, h' x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩
def LiftsCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (PP C : ℝ), Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ C : ℝ, 0 ≤ C ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => ∀ i, Q Fm x hx ι p i (Fm.parT x hx ι).PP C
def CoversCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (_Y : Cov p i) (PP C : ℝ), Prop) : Prop :=
  _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y PP C
def GramCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => GramAt p i
def LiftRecursive : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RecAt p i
def LiftTruncation : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => CutAt p i
def LiftBadSet : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => BadAt p i
def LiftLambdaBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LamAt p i C
def SizeCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i PP C => SizeAt p i PP C
def MeasureCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => MeasAt p i C
def LiftRational : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RatAt p i
def CoreBound' : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => CoreAt p i C
def LiftLowBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LowAt p i C
def AnchorCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => AnchorAt p i C
def LowDefectCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → LowAt p i C
def DeepExistence : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
  ∃ Y : Cov p i, GoodCov p i Y
def DeepGoodness : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => DeepGoodAt p i Y
def RingCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => RingAt p i Y
def MapsCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => MapsAt p i Y
def CoverRank : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => RkAt p i Y PP
def MinimalGenerator : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => GminAt p i Y PP
def FlatDegreeCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => FlatDegAt p i Y
def FlatnessCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => FlatAt p i Y C
def UniformLowerBound : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => UAt p i Y C
def SumBoundCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => SumAt p i Y
def CoverDegree : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → DegAt p i Y u1
def ShareCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1
def HeightCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C u1
def CoverHeightSum : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HSAt p i Y PP C u1
def CovolumeBoundOfX : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
end GlobalTheory.CovTop
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem geoUnitary_tied_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hp _ i σ g x y
  have hm := p.charW.base.models
  exact GlobalTheory.UnitaryActionTest.geometric_unitary p.R.toRealDat hp.prim.unif hm.HW hm.gW
    (GlobalTheory.UnitaryActionTest.actsUnitarily_of_clauses p.R.toRealDat hm.HE hm.gE hm.ν0 hm.HW hm.gW hm.νW
      p.charW.base.fam.tie hm.cX hm.cV) i _ g x y
end GlobalTheory.CovTop
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1
theorem row_hServ_of_kerServ_alt : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (GlobalTheory.Svd.ServH fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => b.R.T.ker) → _root_.GlobalTheory.Fc.R1.SlotServiceCondition Q Lk := by
  intro Q Lk h
  refine Row.imp h fun 𝒜 σ _ hs => ?_
  obtain ⟨⟨a, ha, hK⟩, hA⟩ := hs
  refine ⟨⟨a, ha, fun e he hle => ?_⟩, ⟨a, ha, fun e he hle => ?_⟩⟩
  · obtain ⟨K, hK⟩ := hK e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.Cp.d3_a hc) hL⟩
  · obtain ⟨K, _⟩ := hK e he hle
    exact ⟨K, fun Fm _ _ _ hc x hx _ i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i⟩
end GlobalTheory.Fc.R1
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.JOnBundle
theorem row_jOn_of_row_hPA_alt : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → R0.JInvariantConditionAtConstructedPoints Q Lk := by
  intro Q Lk h
  apply _root_.GlobalTheory.JOnRow.row_jOn_of_realisations_alt _root_.GlobalTheory.Fc.BundleCondition Q Lk
  refine Row.imp h fun 𝒜 σ _ hA => ?_
  intro eps Fm hc x hx i
  have hb := hA Fm hc x hx i
  exact ⟨(σ Fm hc x hx i).R, (σ Fm hc x hx i).P, _, _, _, (σ Fm hc x hx i).S, _, inferInstance, inferInstance, inferInstance,
    (σ Fm hc x hx i).B.Q, 1, (σ Fm hc x hx i).C.ok1, hb.2, hb.1⟩
end GlobalTheory.Fc.JOnBundle
end
end
end
