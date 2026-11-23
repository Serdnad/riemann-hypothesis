module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle308
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle451
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle459
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle517
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle518
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq.TopStep

open _root_.Formalism _root_.Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.MainNotions.G.CmpJ.PStabEq Matrix
open scoped TensorProduct

section Stab

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}



theorem stab_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hT : ¬ D.what₂.places.resChar w ∣ Fo.T)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hdual := (GlobalTheory.Port.formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi)
    (gramN_apply D (i + 1) hi) (Fo.K β).lev w').2.1 (GlobalTheory.Port.T_not_mem hg.1 hT w' h)
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Stab



theorem stepTies_top : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQp O hO' hunf E hE u v hg
  intro i hi h
  let F := t.C.forms u
  let dt := GlobalTheory.Port.detTieOf t.full.1.base (F.cls (i+1) hi (Or.inr h)).lev
  let Fo : FormsIn ((w.D Z).fm u) (i + 1) hi := GlobalTheory.Port.formsInOne (F.val (i+1) hi (Or.inr h)) dt
  let dtM : GlobalTheory.Port.MemDt F := ⟨fun j hj h' => GlobalTheory.Port.detTieOf t.full.1.base _, fun j h1 h2 β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hL0 := GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dtM i hi v hg
  rw [GlobalTheory.Port.formsInMem_top F dtM i hi h] at hL0
  have hL : GlobalTheory.Port.ChartBaseLatticeEqSelfDualAtP u Fo ((w.D Z).what₂.places.resChar v) := hL0
  obtain ⟨Cm, h1, h2, -⟩ := (F.val (i+1) hi (Or.inr h)).de
  obtain ⟨B0, hstd, hB⟩ := GlobalTheory.Port.baseEx_of t.g.herm u v hg Fo Cm h1 h2 hL
  haveI : IsFractionRing ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Kf :=
    (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O
  have hfin := GlobalTheory.Port.chi_fin_top F (i + 1) hi h
  have hrat : Formalism.L2.G.Cmp.ChiRatAll (F.cls (i+1) hi (Or.inr h)).lev (w.D Z).what₂.embLL := by
    obtain ⟨k, hR⟩ := (t.std u).ends (i+1) hi (Or.inr h)
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i+1) hi (badG (w.D Z)) (fun _ => ())
      _ rfl (fun β => Formalism.MainNotions.G.CmpJ.oneChart (F.cls (i+1) hi (Or.inr h)) β) k hR (fun _ => hfin) ()
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Mem.Top.KerTwPsi.exists_psiTiedJ hi (F.cls (i+1) hi (Or.inr h)).lev
    (Formalism.MainNotions.G.ChartsLv.sameU_of Fo ()) (t.cmp.embW u v hg) hrat hfin
  let S : StepD t.g.herm u v hg Fo :=
    { B := B0
      B_lat := fun _ => hB ()
      ψ := fun _ => ψ
      fin := fun β => GlobalTheory.Port.fin_of Fo β _ }
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ Fo.T := hg.2.2.2.2.2
  refine ⟨Fo, (inferInstance : Finite Unit), S, ?_, ?_, ?_, hstd, fun _ => hψ, ?_, trivial, hT⟩
  · intro β w' hw x hx hx1 hx2
    exact (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').2.2 (fun hb => Formalism.L2.G.bad_notOver u v hg w' hb hw)
      (GlobalTheory.Port.T_not_mem hg.1 hT w' hw) ((stab_frB Fo S β w' hw hT x hx).2 ⟨hx1, hx2⟩)
  · intro β w' hw x hx
    have hle := (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').1 hx
    exact (stab_frB Fo S β w' hw hT x hle.1).1 hle
  · exact Formalism.L2.G.bad_notOver u v hg
  · intro β cl
    exact GlobalTheory.Port.chRat_ofChiD (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 _ _ _

end GlobalTheory.Mem.Top.KerOne.CertEq.TopStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead


open GlobalTheory.Mem.R3.Rw.SideTie in
theorem rowSide_of_pk : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y hU b rep EE _ _ _ S n bs ty jA t
  exact ⟨ids hU t, real hU t, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem liftTie_of_pk : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y hU hLam rep jL t
  let I : LiftIds (y.L F) :=
    { jMj := fun i =>
        (LinearEquiv.ofInjective (t.jMj i) (t.jMj_inj i)).trans (LinearEquiv.ofEq _ _ (t.jMj_range i))
      jMt := fun μ hμ i =>
        (LinearEquiv.ofInjective (t.jMt μ i) (t.jMt_inj μ ((hU μ).1 hμ) i)).trans
          (LinearEquiv.ofEq _ _ (t.jMt_range μ ((hU μ).1 hμ) i))
      prtW := fun i π => y.prtW F i (rep π) }
  refine ⟨I, ⟨t.eW, t.eW_range, t.eW_norm, t.eW_lat⟩, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩
  refine ⟨fun i => GlobalTheory.HilbertLevels.holW R F y.tupT y.hm y.hTop y.hinj i, fun i x x' => t.jMj_ip i x x',
    fun μ hμ i x x' => t.jMt_ip μ ((hU μ).1 hμ) i x x', ?_, fun i π v => t.isot i π v,
    fun i π π' h => t.disj i π π' h, ?_⟩
  · intro μ hμ i x w _ hw hthC hgood
    exact t.theta μ ((hU μ).1 hμ) i x _ w hw hthC hgood
  · intro μ _ i π c h0 hc
    rw [hLam μ ((i : ℕ) + 1) (by omega) i.2 π h0]
    exact DV.lamTr_of_scalar D μ _ π c h0 hc



open GlobalTheory.Mem.R3.Rw.ComplexificationCasts in
theorem read_of_fits : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), o.Fits → ∀ m : Moved o, ∀ s : Side0 o, ∃ Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0, Y.tup = m.y.tup ∧ Y.tupT = m.y.tupT ∧ Y.PY = m.y.PY ∧ Y.PW = m.y.PW ∧ (∀ t, HEq (Y.jA t) ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j) ∧ (∀ t, HEq (Y.jA0 t) ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j) ∧ (∀ (i : Fin (w.D o.Z).R.m) t x, HEq (Y.eMt i t x) x) ∧ (∀ π, (principalLevelFrame.rowRepR m.z.R.θ (Y.eFT π)).Iso (m.t.rep π)) ∧ (∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) ∧ (∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x)) ∧ (∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) ∧ (∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)) := by
  intro B f T w Z₀ hX Wt z₀ q o hfits m s
  have hB : m.z.R.toRealDat.BaseW m.z.F.lv2 := m.z.pins.char.base
  have hmu := muAt_eq m
  have hU : ∀ μ, Used0 (w.st o.Z).toD7 μ ↔ m.y.Us μ := by
    intro μ; unfold Used0 Hd.Us; simp only [hmu]
  have hN : NumOK (w.st o.Z).toD7 := q.num o.η o.hη o.V o.S o.N o.G
  -- The coordinate maps of these local definitions reduce to the chain maps.
  let Ish := SideTie.ids (S := RowSide.sharp (w.st o.Z).toD7) hU (m.t.ch true)
  let Iz := SideTie.ids (D := (w.st o.Z).toD7) (R := m.z.R.toRealDat) (F := m.z.F.lv2)
    (S := s.p0.s) (bs := (w.st o.Z).toD7.what₂.onb0) (ty := (w.st o.Z).toD7.what₂.ft0)
    hU (m.t.ch false)
  have h1R := SideTie.real (S := RowSide.sharp (w.st o.Z).toD7) hU (m.t.ch true)
  have h0R := SideTie.real (D := (w.st o.Z).toD7) (R := m.z.R.toRealDat) (F := m.z.F.lv2)
    (S := s.p0.s) (bs := (w.st o.Z).toD7.what₂.onb0) (ty := (w.st o.Z).toD7.what₂.ft0)
    hU (m.t.ch false)
  have kL := liftTie_of_pk _ _ _ _ _ _ m.z.R.toRealDat m.z.F.lv2 m.y hU hN.lam m.t.rep _ m.t.lf
  obtain ⟨IL, mj, hLT, hPW, hMj, hMt, hEW⟩ := kL
  have kF := RepCls.reps_classes _ _ _ _ _ _ m.z.R.toRealDat m.z.F.lv2 m.y _ m.t.rep m.t.reps
  obtain ⟨eF, heF⟩ := kF
  have kE := exists_eE (E := (w.st o.Z).toD7.what₂.EE) m.y hB true
    (m.t.ch true).jE (m.t.ch true).jE_range
  obtain ⟨eE, heE⟩ := kE
  have hocc : ∀ π, (∃ σ, (q.p.ch true).ty σ = π) ∨ ∃ σ, (q.p.ch false).ty σ = π := fun π => by
    have k := (heF π).2.2.2
    obtain ⟨b, h0, hle⟩ := k
    have k' := exists_type (q.p.ch b).bs (q.p.ch b).ty π (m.t.ch b).jE _ ((m.t.ch b).ft π) h0 (hle.trans (m.t.ch b).jE_range.ge)
    cases b
    · exact Or.inr k'
    · exact Or.inl k'
  let Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0 := {
    tup := m.y.tup
    tupT := m.y.tupT
    tupT_tup := m.y.tupT_tup
    tupTie := fun μ h => tupTie m.y ((hU μ).1 h)
    tup0 := m.y.tup0
    muAt := hmu
    hm := m.y.hm
    hTop := m.y.hTop
    hinj := m.y.hinj
    Ish := Ish
    Iz := Iz
    IL := IL
    Kc := ⟨fun μ => m.z.R.toLevCh.xi (m.y.tupT μ)⟩
    PY := m.y.PY
    PW := m.y.PW
    eFT := eF
    ιW := m.y.ιW
    tied := ⟨h1R, h0R, hLT, colTie m.y hB hN.bu⟩
    prtE := fun π => by exact ((heF π).2.1 true).symm
    prtE0 := fun π => by exact ((heF π).2.1 false).symm
    prtWE := fun i π => by exact (hPW i π).trans ((heF π).2.2.1 i).symm
    xi := fun _ _ => rfl
    isomFin := m.y.isomFin
    frameMatch := m.y.frameMatch
    hF := m.y.hF
    stdPsi := m.y.stdPsi
    jA := fun t => by exact ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j
    jA0 := fun t => by exact ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j
    eMt := fun i t => by exact (LinearEquiv.funCongrLeft B.LL B.LL (finCongr (congrArg Mat1.n (m.t.hL i t))))
    formsA := fun t => by exact ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).forms
    latA := fun t => by exact ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).latT
    formsAtBottomLevel := fun t => by exact ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).forms
    latA0 := fun t => by exact ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).latT
    formsL := fun i t => by exact (cast_forms (m.t.hL i t) (q.p.tL (m.y.tup t) ((i : ℕ) + 1)))
    latL := fun i t => by exact (cast_lat (m.t.hL i t) (q.p.tL (m.y.tup t) ((i : ℕ) + 1)))
    topRead := fun t h x => by
      let e := (q.p.ch true).multTop (m.y.tup t)
      let v := ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j x
      change (m.t.ch true).jX (m.y.tup t) (e (e.symm v)) = _
      exact (congrArg ((m.t.ch true).jX (m.y.tup t)) (e.apply_symm_apply v)).trans
        ((m.t.ch true).top t ((hU _).1 h) x)
    topRead0 := fun t h x => by
      let e := (q.p.ch false).multTop (m.y.tup t)
      let v := ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j x
      change (m.t.ch false).jX (m.y.tup t) (e (e.symm v)) = _
      exact (congrArg ((m.t.ch false).jX (m.y.tup t)) (e.apply_symm_apply v)).trans
        ((m.t.ch false).top t ((hU _).1 h) x)
    mtRead := fun i t h x => by
      exact ((hMt _ h i _).trans ((congrArg (m.t.lf.jMt (m.y.tup t) i)
        (cast_apply (m.t.hL i t) (q.p.tL (m.y.tup t) ((i : ℕ) + 1)) x)).trans (m.t.lf.read i t ((hU _).1 h) x)))
    mj := mj
    mjRead := fun i v => by
      refine (hMj i v).trans ?_
      exact (m.t.lf.jMj_read i v).trans
        (congrArg (fun u => PiTensorProduct.lift ((m.z.R.HW i _).e u)) (hEW i v).symm)
    stable := fun μ => by exact (m.t.tA true μ).stable
    stable0 := fun μ => by exact (m.t.tA false μ).stable
    eE := by exact eE
    eE_read := fun x => by
      change (m.t.ch true).jE x = _
      exact heE x
    dall := by exact m.t.dall
    junk := fun μ h => iota_eq_zero _ m.y.hm μ ((m.t.ch true).junk μ fun h' => h ((hU μ).2 h'))
    cen0 := fun cG hk t => by
      exact (cen_of_tie ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)) (m.z.R.eG.trans cG) (fun z x => s.cen (m.y.tup t) z x)
        (s.is _ (stdIso_of_keep m.z cG hk) (m.y.tup t)))
    cen1 := fun cG hk t => by
      exact (cen_of_tie ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)) (m.z.R.eG.trans cG)
        (fun z x => o.N.ntypes.cenAmb (m.y.tup t) z x) ((hfits.cen _ (stdIso_of_keep m.z cG hk)).amb (m.y.tup t)))
    lam := hN.lam
    occ := by exact hocc
    kap := q.kap o.η o.hη o.V o.S o.N o.G
    bu := hN.bu
    ze := hN.ze }
  refine ⟨Y, rfl, rfl, rfl, rfl, fun _ => HEq.rfl, fun _ => HEq.rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t x
    exact heq_funCongr (K := B.LL) (congrArg Mat1.n (m.t.hL i t)) x
  · exact fun π => (heF π).1
  · intro x
    change HEq ((m.t.ch true).jE x) ((m.t.ch true).jE x)
    exact HEq.rfl
  · intro x
    change HEq ((m.t.ch false).jE x) ((m.t.ch false).jE x)
    exact HEq.rfl
  · exact fun i x => heq_of_eq (hEW i x)
  · exact fun μ h i x => heq_of_eq (hMt μ h i x)

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe.SxPass

section Mv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl Formalism.L2.SG.ColDict Formalism.L2.SG.HidaSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {F F' : ∀ u, Forms0 D u}



def trCar (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) : Transport X u (F' u) :=
  { t with
    hc_rep := fun c => by rw [(h u).2.2.2.1]; exact t.hc_rep c
    J_isom := fun c ξ η => by rw [(h u).2.2.2.2]; exact t.J_isom c ξ η }


theorem colDictL_car (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) (hK : X.LevelSubgroupCharacter) :
    colDictL X (trCar h t) hK = colDictL X t hK := by
  refine LinearMap.ext fun T => funext fun c => funext fun z => ?_
  exact congrArg (fun e => t.J (shP X u T.1 (t.hc c)) (e z)) (congrArg DFunLike.coe (h u).2.2.2.2)

theorem chi_of_heq {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} (e : U' = U) (h : HEq chi' chi)
    (x : G) (hx : x ∈ U') : chi' ⟨x, hx⟩ = chi ⟨x, e ▸ hx⟩ := by
  subst e
  rw [eq_of_heq h]


theorem lev_car (h : SameCar F F') {X : HidaSetting D} {u} {t : Transport X u (F u)} {hK : X.LevelSubgroupCharacter} (l : LevelMatch X t hK) :
    LevelMatch X (trCar h t) hK := by
  refine ⟨fun x => ?_, fun g y hr => ⟨?_, fun hk hy => ?_⟩⟩
  · rw [(h u).1]; exact l.1 x
  · rw [(h u).2.1]; exact (l.2 g y hr).1
  · rw [chi_of_heq (h u).2.1 (h u).2.2.1]; exact (l.2 g y hr).2 hk _



def packCar (h : SameCar F F') (P : SPack D F) : SPack D F' :=
  { P with
    tr := fun u => trCar h (P.tr u)
    into := fun u T => by rw [colDictL_car]; exact P.into u T
    bij := fun u => by unfold ColDictBij; rw [colDictL_car]; exact P.bij u
    lev := fun u => lev_car h (P.lev u)
    isom := fun u a b => by rw [colDictL_car]; exact P.isom u a b }



def restCar (h : SameCar F F') {P : SPack D F} (S : SRest P) : SRest (packCar h P) where
  hI := S.hI
  autTie := S.autTie
  colPin := fun u x => Subtype.ext ((LinearMap.congr_fun (colDictL_car h (P.tr u) P.Y.hK) _).trans (congrArg Subtype.val (S.colPin u x)))
  j := S.j
  rowPin := S.rowPin
  locTied := S.locTied



def satCar (h : SameCar F F') (p : RowPk D) (s : p.SAt F) : p.SAt F' :=
  { P := packCar h s.P, S := restCar h s.S, t := s.t, c := s.c, c_pos := s.c_pos, see := s.see, ev := s.ev, rowJ := s.rowJ }

end Mv

section Slot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem sxMv : SxMv := by
  intro K B f T w Z Wt p0 r col N h p0' t col' e ⟨s⟩
  obtain ⟨F₁, hF⟩ := exists_sameF_ofDiv (D := Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) fun u => (col.C.forms u).to0
  obtain ⟨s', -⟩ := GlobalTheory.T.spectralComparison_transported_divisionLatticeChange B w.C Z (pkOf r).G' (pkOf r).Pl0 (pkOf r).T (pkOf r).A (pkOf r).Ks (pkOf r).R (pkOf r).F
    (fun u => (col.C.forms u).to0) (pkOf r).eE (cast (sx_eq r col) s) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have c := StdUnique.sameStd B f T w Z (New.ofDiv (Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :)))) col ((by with_unfolding_all exact (col' :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have e' : pkOf t = (pkOf r).up Z Z.S N h := eq_of_heq e
  rw [sx_eq t col', e']
  exact ⟨satCar (D := Late.D (upL Z Z.S N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) ((pkOf r).up Z Z.S N h) ((by with_unfolding_all exact (s' :)))⟩

end Slot

end GlobalTheory.Mem.SRe.SxPass

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  first | exact @GlobalTheory.Mem.R3.Rw.St.eMt0_isometry | exact GlobalTheory.Mem.R3.Rw.St.eMt0_isometry | (intros; apply GlobalTheory.Mem.R3.Rw.St.eMt0_isometry <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.cuspFormType_eq_at_corresponding_lifts : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  exact @GlobalTheory.Mem.R3.Rw.Ext.cuspA_type_eq
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.tameCharacters_typePrimes_eq_of_extension : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext | exact GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext | (intros; apply GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem liftAutEq : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAutEq D := by
  intro hP D θ hθ ψ hψ V W χ χ' ha om hom μ 𝓕 hq Φ F hF
  obtain ⟨omO, H, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha hom
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  have hf := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
  simp only [hE] at hf
  have e' : ∀ g h, (om (g, h) Φ).1 0 = thKer ψ V W omO ⟨fun x => Φ.1 (toTWsmall V W x), hf⟩ g h := fun g h => by
    have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm
  simp only [e']
  exact (isKerSys_thKer hθ hψ (GlobalTheory.Ker.isWeak_of_datum H) H.om_cont).lift hP hθ hq hF _

end GlobalTheory.Mem.Lift
end
