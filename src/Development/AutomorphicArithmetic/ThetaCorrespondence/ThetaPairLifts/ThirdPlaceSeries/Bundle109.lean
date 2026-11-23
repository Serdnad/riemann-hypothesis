module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceUpperBoundAllMembers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle397
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle412
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.RowEx.frame_eq_and_twistPlacesOffPrimeQZero_of_bWit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → b.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero b.B.Q.Rl.toRealDat.toLevCh ∧ ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (b.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ := by
  intro hL p K q c b w
  have h2 := GlobalTheory.RowEx.FrmW.frame_of_args w.a w.x w.ax
  have e := congrArg (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero r.B.Q.Rl.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (r.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ) w.y.eq
  exact e.mpr h2
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MemberRanks
theorem admissible_ranks_at_member_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val _root_.GlobalTheory.Fc.BundleCondition (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)
end GlobalTheory.MemberRanks
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
theorem levelPrime_le_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  intro hL p
  exact eventually_trace_le.mono fun _ _ _ H β _ _ _ _ => H β
end GlobalTheory.LevelPrimeUpper
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Div.PgTie
open Classical in

theorem pgEq_of_linked_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → (open Classical in w.x.R.Pg = b.R.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap b.R.T.ker.seam.iE)) := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all ?_
  intro _ K _ q c b w _
  have hk := w.recPin.k.std
  rw [image_congr hk.X_eq hk.seam hk.Pr]
  have hl := q.x.what₂.r.z.lev.Pg
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hl.trans (image_refl _ rfl _).symm
end GlobalTheory.Div.PgTie
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.LinkLev
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev

theorem tS_fin_conj_match_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.y.y.tS ∈ Formalism.L2.Theta.GfC (Yc (q.w.D q.Z) 0) ∧ Formalism.IndefR.AutomorphicEvaluation.ConjLevel w.y.y.tS⁻¹ (levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (w.y.y.ιS ⁻¹' seeKS b.S.X) (fun k => seeChiS b.S.X (w.y.y.ιS k)) ∧ Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 b.S.X w.y.y.instEq w.y.y.tS := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all fun _ K _ => ?_
  intro q c b w hsc
  obtain ⟨sP, sS, hP, hS, hb⟩ := w.s
  have see := q.saturationAtWeightedPoint.see
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hι := (GlobalTheory.Mem.JIota.heq_iota_iff _ _ w.y.y.instEq w.y.y.ιS).1 w.y.y.ιS_eq
  have hX : b.S.X = q.saturationAtWeightedPoint.P.X := by
    rw [hb]
    exact spack_X_eq_of_heq (by rw [w.recPin.s.cols]; exact rfl) sP q.saturationAtWeightedPoint.P hP
  have key := levels_of_twArgs w.a w.x w.ax q.saturationAtWeightedPoint.P.X q.saturationAtWeightedPoint.P.inst q.saturationAtWeightedPoint.t ⟨see.conj, see.mat⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact see.fin
  · exact conjLevel_of_setting_eq _ _ hX _ _ _ hι _ _ ht _ _ key.1
  · exact of_setting_eq (fun X h t => Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 X h t) _ _ hX _ _ _ _ ht key.2
end GlobalTheory.Mem.R3.LinkLev
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.Comparison₂
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Tied
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → _root_.GlobalTheory.RealIndexBound.RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}
variable {P : Type} [Group P] [Finite P]
end Tied
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.ShareOn.Comparison₂
namespace GlobalTheory.ShareOn
theorem shareSt_of_shareWSt_alt : _root_.GlobalTheory.ShareOn.SharedWeightStatement → _root_.GlobalTheory.BigOn.ShareStatement := by
  intro h
  unfold _root_.GlobalTheory.ShareOn.SharedWeightStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt at h
  unfold _root_.GlobalTheory.BigOn.ShareStatement _root_.GlobalTheory.BigOn.ForallRecordObjects
  refine Closed.imp h fun Fm CH _ H => ⟨0, fun c _ _ => ?_⟩
  obtain ⟨x0, hx0⟩ := H
  exact ⟨x0, fun x hx hle i p hp hm r O hR =>
    Comparison₂.leafShareI_of_shareW p hR (hx0 x hx hle i p hp hm r hR.1.ok hR.2)⟩
end GlobalTheory.ShareOn
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SumExpAt
end GlobalTheory.SumExpAt
namespace GlobalTheory.SumExpAt
end GlobalTheory.SumExpAt
namespace GlobalTheory.ExpTie
open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem sumExpSt_alt : _root_.GlobalTheory.ExpTie.ExponentSumStatement :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ p _ _ j P W hD _ t w => lIncl_sumExp p j P W hD t w⟩⟩
end GlobalTheory.ExpTie
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  intro hL p
  apply GlobalTheory.Fc.EvP.of_all
  intro _ K _ q c b w hsc
  have hK : DV.KapDef (q.w.D q.Z) := b.R.T.what₂.ka
  have hB : ∀ Zs, HEq ((_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b).Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := by
    intro Zs
    apply heq_of_eq
    funext y j
    rw [← hsc]
    exact (forcedContent_eq_closedContent_numericalDatum _ _ _ _ hK y j).symm
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  have hX := y.eq ▸ hB
  letI := a.x.grp
  letI := a.x.fin
  have hX' : ∀ Zs : DefSub a.x.A3.fam3.amb3, HEq (a.x.F.Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := hX
  dsimp only
  clear * - hX'
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x', pack, _⟩ := a
  dsimp only at hX' ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x'
  dsimp only at pack hX' ⊢
  cases pack
  exact hX' _
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.LinkedPins

theorem realPins_of_seeAt_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (sS : SRest P)
    (e : S = sS.toRealSpectralMatching Rc) (hC : x.R.C = Rc.T.n.cf) (hD : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i))
    (hPg : open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE))
    (hs : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  subst e
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv := (by with_unfolding_all exact ((GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst ((y.ιS))).1 ((y.ιS_eq)) : _))
  refine _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ ex x Rc _ y hC hD hPg hs.fin ?_ ?_
  · rw [hι]
    exact (by with_unfolding_all exact (hs.conj :))
  · exact (by with_unfolding_all exact (hs.mat :))
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}

theorem realisation_normalisation_of_bundle_witness (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
  obtain ⟨x, a, ax, y, recPin, ⟨sP, sS, hP, -, e⟩, ⟨pt, -⟩, _⟩ := w
  cases ax
  obtain ⟨h1, h2, -⟩ := twArgs_lev _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hk := recPin.k.std
  have fd : ∀ V : Formalism.BasicNotions.TH.HSp (q.w.D q.Z), GlobalTheory.Mem.HostFrames.SignFrame V → IsFDiag V := fun V hV => by
    obtain ⟨d, -, h⟩ := hV.gram_eq (q.w.D q.Z).host.F
    exact ⟨d, h⟩
  have hWV := (GlobalTheory.Mem.HostFrames.frames_of_over K (q.w.st q.Z) q.x.isOver).2.1
  refine _root_.GlobalTheory.Fam.LinkedPins.realPins_of_seeAt_alt y.y sS e ?_ (fun i => ⟨fd _ (hWV i).1, fd _ (hWV i).2⟩) ?_ ?_
  · have hc : b.R.T.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst recPin.s.chr
    have hC : Top.Fr.at (q.w.st q.Z) q.w.I.C = Top.Fr.at (q.w.st q.Z) q.f := congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq
    exact (eq_of_heq h1).trans (hC.symm.trans hc.symm)
  · rw [image_congr hk.X_eq hk.seam hk.Pr]
    exact (eq_of_heq h2).trans (image_refl _ rfl _).symm
  · have ht : y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq pt
    have hcols : b.R.T.cols = q.x.col.C := recPin.s.cols
    rw [ht]
    exact seeAt_twArgs a sP.X sP.inst q.saturationAtWeightedPoint.t (setting_congr (D := (q.w.st q.Z).toD7)
      (fun X h => SeeAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 X h q.saturationAtWeightedPoint.t)
      (congrArg (fun C u => (C.forms u).to0) hcols) hP q.saturationAtWeightedPoint.see)
end GlobalTheory.Fam.LinkedPins
open GlobalTheory.MiS GlobalTheory.Fam in

theorem GlobalTheory.Fam.realPins_bundle_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := by
  intro hL p K q c b w
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation k.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [w.y.eq]
  exact _root_.GlobalTheory.Fam.LinkedPins.realisation_normalisation_of_bundle_witness q b w
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix
noncomputable section
namespace GlobalTheory.TopVal.OneForm
section Generic
variable {D : D7} {O : Obj D} {c : ℝ}

theorem row_of_btw_alt (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → D.what₂.LL)
    (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → D.what₂.LL) (hF : HEq F F') :
    ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = x.Y.tup s ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 D (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) (x.Y.jA s v) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ (t : k.P.T)
      (F : Fin ((k.P.A3.side3 k.P.Ps k.P.ψs k.P.Zs).nV t) → D.what₂.LL)
      (F' : Fin ((k.B.Q.F.fc (k.B.Q.Rl.toCx3 k.B.Q.F).zs).Df1.nV t) → D.what₂.LL), HEq F F' →
      ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), k.P.I.tup t = x.Y.tup s ∧
        HEq (k.B.Q.F.eV (k.B.Q.Rl.toCx3 k.B.Q.F).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
        HEq (k.P.I.jA t ((rV0 D k.P.A3.A k.P.Ps k.P.ψs t).mulVec F)) (x.Y.jA s v) := by
    intro k hk
    subst hk
    intro t F F' hF
    have e : F = F' := eq_of_heq hF
    subst e
    change x.T at t
    change (Fin ((x.A3.A.fam.R t).nV (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) → D.what₂.LL) at F
    refine ⟨t, (rV0 D x.A3.A x.F.P1 x.F.ψ1 t).mulVec F, rfl, heq_of_eq ?_, HEq.rfl⟩
    have hOk := y.intersectionNumber_baseChange.ok
    have hb : BlockHyp (x.A3.A.fam.R t) (x.A3.A.fam.lvl x.F.P1 x.F.ψ1) x.A3.A.fam.v0 1 :=
      ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
    unfold R3.rowForm rV0
    show (x.A3.A.fam.R t).S.basis.equivFun.symm (((x.A3.A.fam.R t).vE (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) *ᵥ F) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE hb]
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t F F' hF
end Generic
section Rows
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl
end Rows

theorem exists_frm_isRes_recVal {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) (rx : Bl.RXs q.x.what₂) (s : x.T)
    (v : Fin (rDim (q.w.D q.Z) x.A3.A x.F.P1 x.F.ψ1 s) → (q.w.D q.Z).what₂.LL) :
    ∃ φ : Frm q.w.I (x.Y.tup s), IsRes φ (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      ∀ u, RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u (x.Y.tup s) φ (x.Y.jA s v) := by
  have e : a.x = x := eq_of_heq ax
  subst e
  obtain ⟨s', v', k1, k2, k3⟩ := row_of_args (w := q.w) (Z := q.Z) (ex := q.O.ex) (t := q.x.what₂) a s v
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) k1 k2 k3 (one_form_rows rx s' v')

theorem recVal_packB_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  intro hL p K q c b hb hR t F F' hF
  obtain ⟨rx⟩ := hR
  obtain ⟨s, v, h1, h2, h3⟩ := _root_.GlobalTheory.TopVal.OneForm.row_of_btw_alt b hb.x hb.y t F F' hF
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) h1 h2 h3 (_root_.GlobalTheory.TopVal.OneForm.exists_frm_isRes_recVal q hb.x hb.a hb.ax rx s v)
end GlobalTheory.TopVal.OneForm
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem level_character_matches_witness_alt_bis : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j) := by
  intro hL p K q c b hw j
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := twistedAdelicData_characters_eq_frame _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a j
  have e : b.B.Q.Rl.mu0 = x.R.mu0 := congrArg (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => k.B.Q.Rl.mu0) y.eq
  have e' : a.x.R.mu0 = x.R.mu0 := congrArg (fun z : R3.TwIn q.O.ex => z.R.mu0) hx
  have e2 : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).mu0 = a.x.R.mu0 := e.trans e'.symm
  rw [e2]
  exact h0
end GlobalTheory.Fam
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 Formalism.IndefR Formalism.IndefR.Links
namespace GlobalTheory.Fam

theorem xi_chrEq_cols_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, recPin, s, pt, sx, eF, cW, d3b, side, colPins⟩ := hw
  have key : ∀ t : x.T, Formalism.IndefR.Links.ChrEq (x.R.toRealDat.xi t) (q.w.I.xi (x.Y.tup t)) := by
    have hxi : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → HEq (x.R.toLevCh.xiH (x.Y.tupT μ)) (q.w.I.xi μ) := by
      have h := eq_of_heq ax
      rw [← h]
      exact fun μ hμ => ((GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ _ _ a).2.2.1 μ hμ).2
    intro t
    have hu : Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (x.Y.tup t) := by
      rcases x.pins.char.tup.mu_used t with h | ⟨w, h⟩
      · rw [h]; exact Or.inl x.Y.tup0
      · rw [← h]
        obtain ⟨w', rfl⟩ := (q.w.D q.Z).plEq.surjective w
        exact Or.inr ⟨w', (x.Y.muAt w').symm⟩
    have h1 := hxi _ hu
    rw [x.Y.tupT_tup] at h1
    have h2 := x.pins.char.base.lev.xi t
    rw [eq_of_heq h1] at h2
    exact h2
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => ∀ t : k.P.T, Formalism.IndefR.Links.ChrEq (k.B.Q.Rl.toRealDat.xi t) (q.w.I.xi (k.P.I.tup t))) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact key
end GlobalTheory.Fam
end
end
