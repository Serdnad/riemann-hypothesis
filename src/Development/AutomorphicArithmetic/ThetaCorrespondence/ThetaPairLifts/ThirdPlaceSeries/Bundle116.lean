module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle470
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTwistedClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle099
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle103
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle570
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle109
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle098
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle110
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
theorem eventually_sizeRows_and_logDeriv_le_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) →
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L ∧ |β.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps := by
  refine (_root_.GlobalTheory.Mem.AtSize.eventually_sizeRows_alt hL p).mono fun κ K _ H β hq => ⟨H β hq, ?_⟩
  have h := β.val.dlog
  rw [β.sc] at h
  exact h

theorem rowE_full_grid_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) : RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b.part t).pt.R.toRealDat G := by
  refine (_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.eventually_sizeRows_and_logDeriv_le_alt hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)).mono fun κ K hk H β hq c b hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have h2 : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ :=
    congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) he
  have hL' : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows q.O.L ∧ |q.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps :=
    Eq.ndrec (motive := fun s : Σ D : D7, Obj D => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows s.2.L ∧ |s.2.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps) (H β hq) h2
  have hsc0 : β.O.L.sc = K.s := β.sc
  have hsc : q.O.L.sc = K.s := Eq.ndrec (motive := fun s : Σ D : D7, Obj D => s.2.L.sc = K.s) hsc0 h2
  have hA : GridA CF K q.B q.f q.T := q.x.nx.2.2.down
  have hG : GridAt K.s CF (q.w.st q.Z) q.f (q.T.set q.f) := hA _ _ _ _ _ _
  suffices key : ∀ t : b'.Comparison₂, (b'.part t).pt.CompatibilityConditions → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF,
      ∃ G : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b'.part t).pt.R.toRealDat G by
    have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.CompatibilityConditions →
      ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧
        G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin s.1.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧
        Full (s.2.2.part t).pt.R.toRealDat G) he
    exact cast h1.symm key
  intro t ht G₀
  obtain ⟨hW1, hEx, hfin⟩ := _root_.GlobalTheory.Mem.Top.Bl.weight_one_places_finite_of_witness hL _ K q c b' w hsc
  obtain ⟨hC, hoff, hxi⟩ := _root_.GlobalTheory.RowEx.frame_eq_and_twistPlacesOffPrimeQZero_of_bWit hL _ K q c b' w
  have hset : GlobalTheory.RowClaim.HidaSetting q.O.L b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 :=
    _root_.GlobalTheory.PrimIn.rowTest_setting_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b'.B t.pins hW1 hEx hL'.1 ht.eSer hfin
  have hrec : GlobalTheory.SqTop.Rec q.O.L := ⟨hL'.1, hset.host, hset.hF, by rw [hsc]; exact hL'.2⟩
  have hb : (b'.part t).pt.Z.b = K.s.b := by
    have h0 : (b'.part t).pt.Z.b = q.O.L.sc.b := rfl
    rw [h0, hsc]
  have gen : ∀ z : ℝ, z = K.s.b → ∀ G₀ : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩,
      ∃ G : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full b'.B.Q.Rl.toRealDat G := by
    rintro z rfl G₀
    obtain ⟨G, hk, hF⟩ := @hG q.O.L hsc hrec _ _ _ _ _ _ _ _ _ b'.B.alg b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 hset hC hoff hxi G₀
    exact ⟨G, congrArg Prod.fst hk, congrArg (fun x => x.2.1) hk, fun a => congrFun (congrArg (fun x => x.2.2) hk) a, hF⟩
  exact gen _ hb G₀

theorem rowE_pinned_grid_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) : RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G₀) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have hsc : β.O.L.sc = K.s := β.sc
  have hsc' : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => s.2.1.L.sc) he
    exact this.symm.trans hsc
  have e := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.CompatibilityConditions →
    ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 s.1) ∧
      GlobalTheory.LamTie.IsLamTieFull s.1.ntw (GlobalTheory.BigTop.Fun.lamOf G₀)) he
  refine cast e.symm ?_
  intro t _
  obtain ⟨nl⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2.1
  have hp : GlobalTheory.HeightCounting.Up.ListPin (q.w.st q.Z).toD7 q.x.what₂.r.z.R.toRealDat.toLevCh CF K.s.b := nl.2.down
  have h1 := GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_twArgs w.a hp
  rw [eq_of_heq w.ax] at h1
  have h2 := _root_.GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_rpk_alt w.y.y (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b') w.y.eq h1
  rw [← hsc'] at h2
  exact h2
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
end
end

section



section

theorem _root_.GlobalTheory.T.leafKernel_tie_of_claim_inputs : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafKernel @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K | exact _root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K | (intros; apply _root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K <;> assumption)
end
end

section



section

theorem _root_.GlobalTheory.T.oneMap_of_bundle_setAt_lin_inj_const_formula : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions | exact _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions | (intros; apply _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.one_form_exists_heq_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  first | exact @_root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt | exact _root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt | (intros; apply _root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.BaseLevel
open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem topLev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x)
    {u : D.what₂.Word} (K₀ : ClsPTied u) (h : PairDataBaseTupleLevelEqualsClassLevel x K₀) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (ht : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = D.what₂.mu0) :
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  let readLevel (k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S) : Prop :=
    letI := k.B.alg
    let R := k.B.Q.Rl.toRealDat
    let P := R.levR k.B.Q.F.lv2 true
    ∀ s : k.P.T, k.P.I.tup s = D.what₂.mu0 →
      let d := datXP R P s
      GlobalTheory.Core.Rk.Top.TopLev K₀ (levS D.sp.X' R.βX d) (levChi D.sp.X' R.βX d)
  have hInput : readLevel (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y) := by
    intro s hs
    exact h s hs
  have hBundle : readLevel (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) :=
    (congrArg readLevel y.eq).mpr hInput
  exact hBundle t ht

theorem pairDataBaseTupleLevel_eq_classLevel_of_stdF {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K)
    (a : R3.TwArgs q.O.ex q.x.what₂) (v : q.B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((q.w.D q.Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (q.w.D q.Z) v Ch chOf) (hF : TC.StdF q.w.I q.w.l q.Z v F) : PairDataBaseTupleLevelEqualsClassLevel (O := q.O) a.x F.clsP := by
  -- Transport the level predicate using only the packed data and the tuple map.
  have hPack := congrArg (fun k => match k with
    | ⟨_, grp, fin, _, _, T, _, _, alg, R, face, _⟩ =>
      letI := grp
      letI := fin
      letI := alg
      ∀ tup : T → (q.w.D q.Z).what₂.Tup, HEq tup q.x.what₂.r.Y.tup →
        ∀ t : T, tup t = q.w.I.mu0 →
          let r := R.toRealDat
          let d := datXP r (r.levR face.lv2 true) t
          GlobalTheory.Core.Rk.Top.TopLev F.clsP
            (levS (q.w.D q.Z).sp.X' r.βX d) (levChi (q.w.D q.Z).sp.X' r.βX d)) a.pack
  let _ := a.x.grp
  let _ := a.x.fin
  let _ := a.x.alg
  refine (hPack.mpr ?_) a.x.Y.tup a.tup
  intro tup htup t ht
  have hTup : tup = q.x.what₂.r.Y.tup := eq_of_heq htup
  have z := q.x.what₂.r.z.lev
  have hix : R3.ixOf q.w.I _ t = q.w.I.mu0 :=
    (q.x.what₂.r.tup_ix t).symm.trans ((congrFun hTup t).symm.trans ht)
  have hQ : q.x.what₂.r.z.R.Q t = ∅ := (z.Q t).trans ((congrArg q.w.I.Q hix).trans q.w.I.twistPrimes_reference_tuple_eq_empty)
  have hc := z.is.chi
  rw [z.C] at hc
  exact topLev_levPOf q.w.I q.w.l q.Z q.w.ok q.w.pins v F hF r_le_X q.x.what₂.r.z.R.Pg (q.x.what₂.r.z.R.Q t) q.x.what₂.r.z.R.βX
    z.Pg hQ z.beta.2 q.x.what₂.r.z.R.eG q.x.what₂.r.z.idG q.x.what₂.r.z.R.chi (q.x.what₂.r.z.R.xiR t) hc

theorem levG_base_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  intro hL p K q c b hw u t ht
  obtain ⟨-, -, -, ⟨hC⟩, -⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  let F := b.R.T.cols.forms u
  have hF : TC.StdF q.w.I q.w.l q.Z u F := hC u
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  have hArgs := pairDataBaseTupleLevel_eq_classLevel_of_stdF q hw.a u F hF
  have hPair : PairDataBaseTupleLevelEqualsClassLevel hw.x F.clsP :=
    (congrArg (fun x => PairDataBaseTupleLevelEqualsClassLevel x F.clsP) hx).mp hArgs
  have hTop := topLev_of_btw_alt b hw.x hw.y F.clsP hPair t ht
  exact (levG_one_iff (D := q.w.D q.Z) F.clsP _ _).mpr hTop
end GlobalTheory.Fam.BaseLevel
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenBridge
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
end Local
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem eq_s_succ_of_succ_eq_m (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) : j = (J.G i).s + 1 := by
  have h1 : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  omega
def frameAtLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    Frame (J.G i).k ((I.rec7 l Z).sp.X j).rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) := by
  subst e
  exact (J.G i).FX _ le_rfl
def reductionHomAtLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k :=
  (toSum0 (J.G i).k _).toMonoidHom.comp (GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e))
def reductionHomAtLastLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k) :=
  MonoidHom.pi fun i => _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)
def finitePlaceCondition (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (p : GlobalTheory.FinPl.Pl (I.rec7 l Z)) : Prop := ∃ i, (J.G i).q.v = p
end GlobalTheory.PenBridge
end
namespace GlobalTheory.PenBridge
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
end Local
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem int_in_frame_at_level (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    IntIn (J.G i).q ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) (a.g.x j).L := by
  subst e
  exact fun y => (J.G i).latX _ le_rfl y
theorem rd_at_apply (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i e g = toSum0 (J.G i).k _ (GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) g) := rfl
end GlobalTheory.PenBridge
end
end

section



section
noncomputable section
namespace GlobalTheory.TopVal.LevTw
section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
end Gen
section Cols
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
variable {B : Base} {X : PreX B.toPre} (I : TC B X)
end Cols
section Pack
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levRead_packB_of_bWit {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    LevRead q.w.I q.w.l q.Z (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).toLevCh (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup := by
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := levRead_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have h1 : LevRead q.w.I q.w.l q.Z x.R.toLevCh (x.R.toRealDat.levR x.F.lv2 true) x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => LevRead q.w.I q.w.l q.Z k.B.Q.Rl.toRealDat.toLevCh
      (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) k.P.I.tup) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
    rw [y.eq]
    exact h1
  exact h2

theorem levIs_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) :
    LevIs ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev
      (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  have hxi : b.R.T.n.tp.xi = q.w.I.xi := (congrArg (fun s => s.2.xi) hw.recPin.s.chr).trans q.x.n.xi
  obtain ⟨l0, s, he, hs, -, -, hP⟩ := (_root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw).2.2.2.2
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (s' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes b.R.T.n.tp b.R.T.cols Tw), Tw = TC.tw q.w.I q.w.l l0 q.Z →
      HEq s' s → LevIs (s'.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev
        (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
        (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
    rintro _ s' rfl rfl
    refine _root_.GlobalTheory.TopVal.LevTw.levRead_packB_of_bWit q b hw t h _ _ _ _ _ (fun v hv => hv.imp id fun hv => ?_) (s'.pt.chi_fin u _ h) (hP.what₂ u _ h)
    have h1 := (s'.ch.Q_iff _ v).1 hv
    unfold Formalism.L2.Host.TupTied.InQ' at h1
    rw [hxi] at h1
    exact underQ_of_ram q.w.ok _ v h1
  exact key _ _ he hs
theorem levChi_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) g = star ((((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) :=
  fun q _ b hw u t h g κ hm => (_root_.GlobalTheory.TopVal.LevTw.levIs_of_bWit_alt q b hw u t h).2 g κ hm
end Pack
end GlobalTheory.TopVal.LevTw
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inRange_halfAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  first | exact @_root_.GlobalTheory.HalfLabels.halfAt_inRange_alt | exact _root_.GlobalTheory.HalfLabels.halfAt_inRange_alt | (intros; apply _root_.GlobalTheory.HalfLabels.halfAt_inRange_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inRange_kapAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @_root_.GlobalTheory.FrameOf.kapSt_alt | exact _root_.GlobalTheory.FrameOf.kapSt_alt | (intros; apply _root_.GlobalTheory.FrameOf.kapSt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.permAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  first | exact @_root_.GlobalTheory.FramePerm.permSt_alt | exact _root_.GlobalTheory.FramePerm.permSt_alt | (intros; apply _root_.GlobalTheory.FramePerm.permSt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tame_at_of_small_at : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  first | exact @_root_.GlobalTheory.TameStab.tameSt_alt | exact _root_.GlobalTheory.TameStab.tameSt_alt | (intros; apply _root_.GlobalTheory.TameStab.tameSt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.chiAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  first | exact @_root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt | exact _root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt | (intros; apply _root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt <;> assumption)
end
end
