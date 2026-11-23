module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle363
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle108
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle109
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle083
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle110
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rankMu_all_linked_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | exact _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | (intros; apply _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberData
theorem val_sizes_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
    (fun κ _ O _ _ => Std κ.C ∧ Val κ.C κ.cD κ.ch O.L ∧ SizesAt O.L) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ h52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, h1⟩ := szRow_sizesAt eps he h52 C hC
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h2⟩ := h1 cD hcD
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x0, h3⟩ := h2 ch hch
  refine ⟨x0, fun K hK hx β _ c b _ => ?_⟩
  obtain ⟨e1, e2, e3, e4, -⟩ := hK
  have hv : Val C cD ch β.O.L := val_congr e1 e2 e3 (β.p.pt_val β.val)
  have hs : β.O.L.sc = K.s := β.sc
  refine ⟨hC, hv, h3 β.D β.O.L ?_ ?_ hv⟩
  · rw [hs]; exact e4
  · rw [hs]; exact hx
theorem dataNW_of_isGoodE_of_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := fun hL p =>
  ((_root_.GlobalTheory.Fam.MemberData.val_sizes_at_alt hL p).and (_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked hL p)).imp fun _ _ β _ _ _ _ _ H =>
    dataNW_of_val H.1.1 β.O.L H.1.2.1 H.1.2.2 H.2
end GlobalTheory.Fam.MemberData
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.LevLow
theorem levelPrime_lower_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  intro hL p
  have hA : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
    RowE.of_all fun _ K β _ b _ _ _ =>
      admissibleRanks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_mass K β.X β.c.isOver β.c.dsig_eq)
  exact (EvP.and (RowE.and hA (_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked hL p)) eventually_le_trace).mono
    fun _ _ _ H β hq c b hl => H.2 β (H.1 β hq c b hl).1 (H.1 β hq c b hl).2
end GlobalTheory.Core.LevLow
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPins_of_bWit_third_place_series : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := by
  first | exact @_root_.GlobalTheory.Fam.realPins_bundle_of_bWit | exact _root_.GlobalTheory.Fam.realPins_bundle_of_bWit | (intros; apply _root_.GlobalTheory.Fam.realPins_bundle_of_bWit <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_character_matches_witness' : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  first | exact @_root_.GlobalTheory.Fam.xi_chrEq_cols_alt | exact _root_.GlobalTheory.Fam.xi_chrEq_cols_alt | (intros; apply _root_.GlobalTheory.Fam.xi_chrEq_cols_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_places_match_witness' : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
  first | exact @_root_.GlobalTheory.Fam.mem_Q_packB_iff_mem_QE_of_bWit | exact _root_.GlobalTheory.Fam.mem_Q_packB_iff_mem_QE_of_bWit | (intros; apply _root_.GlobalTheory.Fam.mem_Q_packB_iff_mem_QE_of_bWit <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pk_at_vanishing_of_is_uni : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  first | exact @_root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero | exact _root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero | (intros; apply _root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_valEqv_of_bWit_std : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  first | exact @_root_.GlobalTheory.TopVal.pkVal_of_bWit_alt | exact _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt | (intros; apply _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bWit_C_eq_cf_of_sc_eq :
    ∀ (hL : UpperTheory.Zero.LLC.RecTExists) (p : GlobalTheory.Mem.Top.Bl.Parameters hL),
      GlobalTheory.Fc.EvP fun _ K =>
        ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c)
          (w : GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.x.R.C = b.R.T.n.cf :=
  GlobalTheory.Mem.Top.Bl.bwit_cf_eq_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  exact GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bWit_Pg_eq_image_plMap_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → (open Classical in w.x.R.Pg = b.R.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap b.R.T.ker.seam.iE)) :=
  _root_.GlobalTheory.Div.PgTie.pgEq_of_linked_alt
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

theorem _root_.GlobalTheory.T.sum_expansion' : _root_.GlobalTheory.ExpTie.ExponentSumStatement := by
  first | exact @_root_.GlobalTheory.ExpTie.sumExpSt_alt | exact _root_.GlobalTheory.ExpTie.sumExpSt_alt | (intros; apply _root_.GlobalTheory.ExpTie.sumExpSt_alt <;> assumption)
end
end
