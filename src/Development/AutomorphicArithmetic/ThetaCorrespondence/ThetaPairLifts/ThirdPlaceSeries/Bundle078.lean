module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle577
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle066
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle067
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.BuRationalOf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameInt
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b :=
  fun hL => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ ad k s =>
    frame_of (D := (w.st Z).toD7) t.r.z.R.toLevCh t.r.z.pins.char.base.lev t.r.Y.hF k (ad.PV k) (ad.std k) s
end GlobalTheory.FrameInt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenLocAt
section Gen
open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
end Gen
theorem actRead_at_mem_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ =>
    actRead_of t.r.Y t.r.z.pins.char.base.models t.r.z.pins.char.base.grp.red_L t.r.intersectionNumber_baseChange.ok
end GlobalTheory.CenLocAt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenRatAt
section Main
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Main
theorem cenRat_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ hR _ => hR.elim fun r => cenRat_of t r
end GlobalTheory.CenRatAt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem jumpsCard_of_built_alt (hH : HtCard) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (fr : OmFrame b.D) (hp : PhtOn b.A.wd fr fun _ _ _ _ => True) : JumpsCard D'.nd D'.naut := by
  obtain ⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  intro i a r w τ hw hτ hdR
  have hdA := ((Au.wdOf i a r w).2.2.2.1).mp hdR
  have e1 := (Au.wdOf i a r w).2.2.2.2 τ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have e2 := hp.card _ (L.Y.naut.iotaQC i) a r τ w trivial (fun x => (hτ x).symm) hdA
  show Multiset.card (L.Y.jumpsW i r τ) = a
  rw [e1, e2]
theorem jumpsCard_at_members_of_htCard : HtCard → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro hH hL
  refine evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  obtain ⟨fr, -, hp⟩ := (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd).pht
  exact _root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_of_built_alt hH c.a.nt.toNBuilt fr hp
end GlobalTheory.HeightCounting.JumpsAt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.automorphy_of_move {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au) : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL m.D (m.sideA_alt A).wdT (m.sideA_alt A).au := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.ndSpec_alt {big} {L : LocAll (lay0 D)} (x : NdSpec A.pl M C big L.X L.T) : NdSpec (m.sideA_alt A).pl (m.mt M) (m.ch C) big (m.loc L).X (m.loc L).T := @_root_.GlobalTheory.HeightCounting.NdSpec.mk (_) (_) (_) (_) (_) (_) (_)
    (iq := (by with_unfolding_all exact (x.iq :)))
    (iq_alg := (by with_unfolding_all exact (x.iq_alg :)))
    (iq_LL := (by with_unfolding_all exact (x.iq_LL :)))
    (iq_big := (by with_unfolding_all exact (x.iq_big :)))
    (B := @_root_.Formalism.L2.NLocBase.mk (_) (_)
      (Oc := (by with_unfolding_all exact (x.B.Oc :)))
      (ringOc := (by with_unfolding_all exact (x.B.ringOc :)))
      (domOc := (by with_unfolding_all exact (x.B.domOc :)))
      (dvrOc := (by with_unfolding_all exact (x.B.dvrOc :)))
      (ec := (by with_unfolding_all exact (x.B.ec :)))
      (ec_w := (by with_unfolding_all exact (x.B.ec_w :)))
      (V := (by with_unfolding_all exact (x.B.V :)))
      (acgV := (by with_unfolding_all exact (x.B.acgV :)))
      (modV := (by with_unfolding_all exact (x.B.modV :)))
      (modVO := (by with_unfolding_all exact (x.B.modVO :)))
      (towV := (by with_unfolding_all exact (x.B.towV :)))
      (iV := (by with_unfolding_all exact (x.B.iV :)))
      (iV_basis := (by with_unfolding_all exact (x.B.iV_basis :)))
      (Qc := (by with_unfolding_all exact (x.B.Qc :)))
      (hL := (by with_unfolding_all exact (x.B.hL :)))
      (hL_def := (by with_unfolding_all exact (x.B.hL_def :)))
      (hK := (by with_unfolding_all exact (x.B.hK :)))
      (hK_def := (by with_unfolding_all exact (x.B.hK_def :)))
      (split := (by with_unfolding_all exact (x.B.split :)))
      (Qc_over := (by with_unfolding_all exact (x.B.Qc_over :)))
      (Qc_conj := (by with_unfolding_all exact (x.B.Qc_conj :))))
    (Q_eq := (by with_unfolding_all exact (x.Q_eq :)))
    (mx := (by with_unfolding_all exact (x.mx :)))
    (mx_max := (by with_unfolding_all exact (x.mx_max :)))
    (mx_inj := (by with_unfolding_all exact (x.mx_inj :)))
    (mx_all := (by with_unfolding_all exact (x.mx_all :)))
    (phO := (by with_unfolding_all exact (x.phO :)))
    (phK := (by with_unfolding_all exact (x.phK :)))
    (phK_alg := (by with_unfolding_all exact (x.phK_alg :)))
    (phK_emb := (by with_unfolding_all exact (x.phK_emb :)))
    (Psi := (by with_unfolding_all exact (x.Psi :)))
    (Psi_inj := (by with_unfolding_all exact (x.Psi_inj :)))
    (Psi_range := (by with_unfolding_all exact (x.Psi_range :)))
    (Psi_pr := (by with_unfolding_all exact (x.Psi_pr :)))
    (ptX := (by with_unfolding_all exact (x.ptX :)))
    (ptX_hT := (by with_unfolding_all exact (x.ptX_hT :)))
    (iotaC := (by with_unfolding_all exact (x.iotaC :)))
    (iotaC_coh := (by with_unfolding_all exact (x.iotaC_coh :)))
    (Qc_eq := (by with_unfolding_all exact (x.Qc_eq :)))
    (std := (by with_unfolding_all exact (x.std :)))
    (act_hK := (by with_unfolding_all exact (x.act_hK :)))
    (twOf_eq := (by with_unfolding_all exact (x.twOf_eq :)))
    (twSide_eq := (by with_unfolding_all exact (x.twSide_eq :)))
    (psi_eq := (by with_unfolding_all exact (x.psi_eq :)))
    (twO_alg := (by with_unfolding_all exact (x.twO_alg :)))
    (tw_reads := (by with_unfolding_all exact (x.tw_reads :)))
    (heckeLoc_gamma_places := (by with_unfolding_all exact (x.heckeLoc_gamma_places :)))
    (nbr := (by with_unfolding_all exact (x.nbr :)))
    (nbr_ind := (by with_unfolding_all exact (x.nbr_ind :)))
    (self_good := (by with_unfolding_all exact (x.self_good :)))
    (nbr_iq := (by with_unfolding_all exact (x.nbr_iq :)))
    (bj := (by with_unfolding_all exact (x.bj :)))
    (bj_span := (by with_unfolding_all exact (x.bj_span :)))
    (bj_rel := (by with_unfolding_all exact (x.bj_rel :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.herm_wCell_last_mul_mulVec_eq_of_inWb {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {rep} (x : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL m.D rep (fun σ w ↦ ((m.sideA_alt A).wdT.e w) ((m.sideA_alt A).row.locR σ w)) (m.sideA_alt A).row.satR := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def Mv.sideB_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {low Pq S hk eig θ} (x : SideB D cf A.row low Pq S hk eig θ) : SideB m.D (m.cf cf) (m.sideA_alt A).row low Pq S hk eig θ := @_root_.GlobalTheory.HeightCounting.SideB.mk (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (twF := @_root_.GlobalTheory.HeightCounting.TwFrameC.mk (_)
      (K0 := (by with_unfolding_all exact (x.twF.K0 :)))
      (eO0 := (by with_unfolding_all exact (x.twF.eO0 :)))
      (j0 := (by with_unfolding_all exact (x.twF.j0 :)))
      (Lw := (by with_unfolding_all exact (x.twF.Lw :)))
      (eO := (by with_unfolding_all exact (x.twF.eO :)))
      (eOk := (by with_unfolding_all exact (x.twF.eOk :)))
      (iCq := (by with_unfolding_all exact (x.twF.iCq :)))
      (S0x := (by with_unfolding_all exact (x.twF.S0x :))))
    (tw := @_root_.GlobalTheory.HeightCounting.TwistFrameLowIndexCompatibility.mk (_) (_) (_)
      (pl_emb := (by with_unfolding_all exact (x.tw.pl_emb :)))
      (ringSpec_baseIntegersEquiv_algebraMap := (by with_unfolding_all exact (x.tw.ringSpec_baseIntegersEquiv_algebraMap :)))
      (ringSpec_baseEmbedding_compatible := (by with_unfolding_all exact (x.tw.ringSpec_baseEmbedding_compatible :)))
      (eO_alg := (by with_unfolding_all exact (x.tw.eO_alg :)))
      (eOk_alg := (by with_unfolding_all exact (x.tw.eOk_alg :)))
      (mu_g := (by with_unfolding_all exact (x.tw.mu_g :)))
      (hk_split := (by with_unfolding_all exact (x.tw.hk_split :)))
      (ringSpec_excludedPlaces_eq := (by with_unfolding_all exact (x.tw.ringSpec_excludedPlaces_eq :)))
      (concreteTwistFrame_extraExcludedPlaces_conj := (by with_unfolding_all exact (x.tw.concreteTwistFrame_extraExcludedPlaces_conj :)))
      (B_range := (by with_unfolding_all exact (x.tw.B_range :)))
      (sig_inj := (by with_unfolding_all exact (x.tw.sig_inj :)))
      (qs_pos := (by with_unfolding_all exact (x.tw.qs_pos :)))
      (concreteTwistFrame_extraExcluded_over_smallPrimes := (by with_unfolding_all exact (x.tw.concreteTwistFrame_extraExcluded_over_smallPrimes :))))
    (cover := (by with_unfolding_all exact (x.cover :)))
    (chiD := @_root_.Formalism.L2.NC.NChiData.mk (_)
      (mu0 := (by with_unfolding_all exact (x.chiD.mu0 :)))
      (etaT := (by with_unfolding_all exact (x.chiD.etaT :)))
      (del := (by with_unfolding_all exact (x.chiD.del :)))
      (psi := (by with_unfolding_all exact (x.chiD.psi :)))
      (chiI := (by with_unfolding_all exact (x.chiD.chiI :)))
      (embO := (by with_unfolding_all exact (x.chiD.embO :))))
    (chi := @_root_.Formalism.L2.NC.NormalizedCharacterCompatibility.mk (_) (_)
      (psi := (by with_unfolding_all exact (x.chi.psi :)))
      (del_fix := (by with_unfolding_all exact (x.chi.del_fix :)))
      (delta := (by with_unfolding_all exact (x.chi.delta :)))
      (chi1 := (by with_unfolding_all exact (x.chi.chi1 :)))
      (ringSpec_sidedEmbedding_fixedField := (by with_unfolding_all exact (x.chi.ringSpec_sidedEmbedding_fixedField :)))
      (etaT_unr := (by with_unfolding_all exact (x.chi.etaT_unr :)))
      (etaT_inf := (by with_unfolding_all exact (x.chi.etaT_inf :)))
      (lamG := (by with_unfolding_all exact (x.chi.lamG :))))
    (eta_eq := (by with_unfolding_all exact (x.eta_eq :)))
    (ringSpec_normalisedCharacter_eq := (by with_unfolding_all exact (x.ringSpec_normalisedCharacter_eq :)))
    (del_eq := (by with_unfolding_all exact (x.del_eq :)))
    (iCq_embO := (by with_unfolding_all exact (x.iCq_embO :)))
    (embO_star := (by with_unfolding_all exact (x.embO_star :)))
    (deltaRead := (by with_unfolding_all exact (x.deltaRead :)))
    (exp := @_root_.Formalism.L2.NExpTied.mk (_)
      (U_eq := (by with_unfolding_all exact (x.exp.U_eq :)))
      (psiU_gen := (by with_unfolding_all exact (x.exp.psiU_gen :)))
      (psiU_side := (by with_unfolding_all exact (x.exp.psiU_side :)))
      (psiU_xi := (by with_unfolding_all exact (x.exp.psiU_xi :)))
      (delU_cont := (by with_unfolding_all exact (x.exp.delU_cont :)))
      (delU_ine := (by with_unfolding_all exact (x.exp.delU_ine :)))
      (thU_empty := (by with_unfolding_all exact (x.exp.thU_empty :)))
      (sgnT := (by with_unfolding_all exact (x.exp.sgnT :)))
      (sgnT_one := (by with_unfolding_all exact (x.exp.sgnT_one :)))
      (Wt := (by with_unfolding_all exact (x.exp.Wt :)))
      (acgWt := (by with_unfolding_all exact (x.exp.acgWt :)))
      (modWt := (by with_unfolding_all exact (x.exp.modWt :)))
      (fdWt := (by with_unfolding_all exact (x.exp.fdWt :)))
      (rhoW := (by with_unfolding_all exact (x.exp.rhoW :)))
      (rhoW_irr := (by with_unfolding_all exact (x.exp.rhoW_irr :)))
      (rhoW_alg := (by with_unfolding_all exact (x.exp.rhoW_alg :)))
      (tauG := (by with_unfolding_all exact (x.exp.tauG :)))
      (sgnG := (by with_unfolding_all exact (x.exp.sgnG :)))
      (sgnG_one := (by with_unfolding_all exact (x.exp.sgnG_one :)))
      (tau_galois_first_character := (by with_unfolding_all exact (x.exp.tau_galois_first_character :)))
      (mtV := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => @fun x6 => @fun x7 => @fun x8 => @fun x9 => @_root_.Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).W : _)))
        (acg := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).acg : _)))
        (mod := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).mod : _)))
        (fd := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).fd : _)))
        (ρ := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).ρ : _)))
        (irr := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).irr : _)))
        (alg := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).alg : _)))
        (bc := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).bc : _)))
        (J := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J : _)))
        (χ := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).χ : _)))
        (J_open := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_open : _)))
        (hyp := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).hyp : _)))
        (QP := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP : _)))
        (QP_sub := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_sub : _)))
        (QP_cover := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_cover : _)))
        (QP_nconj := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_nconj : _)))
        (DP := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP : _)))
        (DP_sub := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_sub : _)))
        (DP_cover := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_cover : _)))
        (DP_nconj := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_nconj : _)))
        (sp := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp : _)))
        (sp_w := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp_w : _)))
        (redG := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).redG : _)))
        (J_mem := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_mem : _)))
        (chi_eq := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).chi_eq : _)))
        (real := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).real : _))))
      (rhoW_hw := (by with_unfolding_all exact (x.exp.rhoW_hw :)))
      (rhoW_wt := (by with_unfolding_all exact (x.exp.rhoW_wt :))))
    (pq := (by with_unfolding_all exact (x.pq :)))
    (psiU := (by with_unfolding_all exact (x.psiU :)))
    (rho := (by with_unfolding_all exact (x.rho :)))
    (chiL := (by with_unfolding_all exact (x.chiL :)))
    (hs := (by with_unfolding_all exact (x.hs :)))
    (eF := (by with_unfolding_all exact (x.eF :)))
    (bsup := (by with_unfolding_all exact (x.bsup :)))
    (act := (by with_unfolding_all exact (x.act :)))
    (cHk := (by with_unfolding_all exact (x.cHk :)))
    (hkEq := (by with_unfolding_all exact (x.hkEq :)))
    (cHk_del := (by with_unfolding_all exact (x.cHk_del :)))
    (hk_emb := (by with_unfolding_all exact (x.hk_emb :)))
    (sigSpan := (by with_unfolding_all exact (x.sigSpan :)))
    (rowS := (by with_unfolding_all exact (x.rowS :)))
    (rowS_eig := (by with_unfolding_all exact (x.rowS_eig :)))
    (hEig_zero := (by with_unfolding_all exact (x.hEig_zero :)))
    (rhoS := (by with_unfolding_all exact (x.rhoS :)))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.labConj_alt (x : LabConj D A.wdT) : LabConj m.D (m.sideA_alt A).wdT := (by with_unfolding_all exact (x :))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.DIV.RatFullFam
open Formalism.L2.Top3 Formalism.L2.Top4
theorem buRat_rrFull_closed_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧
        (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull) :=
  rRows.imp fun Fm CH _ h hc _ _ => by
    obtain ⟨C, _, x0, H⟩ := h hc
    have key : ∀ x ≥ max (max x0 (sel Fm (d3_a hc)).1) (Fm.x1 + 1), ∀ i : Fm.Ix x,
        (Fm.D x i).BuRational ∧ (Fm.D x i).RRFull := by
      intro x hx0 i
      have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
      have hx : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx0)
      obtain ⟨ra, _⟩ := H x hx hs h0 i
      obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx hs i
      have hok1 := (selC Fm (d3_a hc) x hx hs i).ok1
      have hU := _root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm (d3_a hc) x hx hs i).Q
      have hR := (hDivG Fm (d3_a hc) x hx hs i).toRows hU
      have hPt := Formalism.L2.DIV.dcPt_of_G hU (hDcPtG Fm (d3_a hc) x hx hs i)
      have hF := _root_.Formalism.L2.DIV.RatFullPt.indefinite_realisation_column_facts ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx hs i) hok1 hsep prows ra.seeIso ra.miStar
      exact ⟨Formalism.L2.DIV.RatFullPt.buRational_of _ hok1 hF hR hPt (Fm.ties x i).bu_def,
        Formalism.L2.DIV.RatFullPt.rrFull_of _ hok1 hF hR⟩
    exact ⟨⟨_, fun x hx i => (key x hx i).1⟩, ⟨_, fun x hx i => (key x hx i).2⟩⟩
end Formalism.L2.DIV.RatFullFam
end
end
end
