module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle509
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle565
public import Formalism.PieriBlockIdeals.StatementE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle057
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.Mem.Top.Bl

theorem zscale_f0_of_witness_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (hsc : q.O.L.sc = K.s) :
    HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
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

theorem weight_one_places_finite_of_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ)
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.O.L.sc = K.s →
    (∀ v, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F 0 0) v → v ∈ b.B.Q.Rl.twPl) ∧
      b.B.Q.Rl.toRealDat.ExAt ∧ Finite b.P.T := by
  intro hL p K q c b w hsc
  have hZ := _root_.GlobalTheory.Mem.Top.Bl.zscale_f0_of_witness_alt q b w hsc
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  letI := a.x.grp
  letI := a.x.fin
  letI : Algebra (↥a.x.core.Q.c.F) (q.w.D q.Z).what₂.LL := a.x.alg
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a b.R b.S y.y hZ
  have hP : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree r.B.Q ∧ r.B.Q.Rl.toRealDat.ExAt ∧ Finite r.P.T) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y) :=
    ⟨h3, y.intersectionNumber_baseChange.aux.ex, finite_T_of_twArgs a⟩
  rw [← y.eq] at hP
  exact ⟨hP.1.w1 0 0, hP.2.1, hP.2.2⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
noncomputable def packK_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) :
    _root_.GlobalTheory.MiS.RealPackAlt O.ex :=
  letI := k.B.alg
  { R := R, S := S, P := k.P, Dcf := k.Dc, Spf := k.Sp, Zscf := k.Zsc, Ks := k.B.T.Q.c.F, Q := k.B.Q }

theorem mem_Q_packB_iff_mem_QE_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  have main : ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packK_alt (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y))).Q t ↔
      PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup ((_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y).P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
    intro t PP
    obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    have h1 := (hl _ (_root_.GlobalTheory.Fam.Inhab.used0_tupP_packOf_and_tupT_eq y.y t).1).1
    rw [(_root_.GlobalTheory.Fam.Inhab.used0_tupP_packOf_and_tupT_eq y.y t).2] at h1
    exact Iff.of_eq (congrArg (PP ∈ ·) (eq_of_heq h1))
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packK_alt k)).Q t ↔
      PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (k.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact main
end GlobalTheory.Fam
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal.Inj
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem eq_zero_of_pkAt_eq_zero_uni {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (gP : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t)
    (hz : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) : x = 0 := by
  exact eq_zero_of_hasMat (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.models.jX gP t x hz

theorem eq_zero_of_isRes_pkAt_eq_zero : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  intro hL p K q c b hw t φ x hx hz d
  have hx0 : x = 0 := _root_.GlobalTheory.TopVal.Inj.eq_zero_of_pkAt_eq_zero_uni (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b)
    (Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z).2.1 t x hz
  subst hx0
  obtain ⟨x, a, ax, y, -⟩ := hw
  have e : a.x = x := eq_of_heq ax
  subst e
  have h0 := eq_zero_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      ∀ (s : k.P.T) (φ : Frm q.w.I (k.P.I.tup s)), IsRes φ (0 : k.P.A3.A.fam.amb.FR s) → φ = 0 := by
    intro k hk
    subst hk
    exact h0
  rw [key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t φ hx]
  rfl
end GlobalTheory.TopVal.Inj
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal
namespace GlobalTheory.TopVal

theorem pkVal_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  intro hL p K q c b hw hs
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  have h1 : DatVal q.w.I q.w.l q.Z (aK := hw.x.alg) hw.x.R.toRealDat hw.x.Y.tup := by
    rw [← hx]
    exact datVal_twArgs K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ hw.a hs
  have h2 : (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => DatVal q.w.I q.w.l q.Z (aK := k.B.alg) k.B.Q.Rl.toRealDat k.P.I.tup) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
    rw [hw.y.eq]
    exact h1
  obtain ⟨cv, h3, h4⟩ := h2
  exact ⟨cv, h3, h4⟩
end GlobalTheory.TopVal
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.HeightCounting.Up
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem builtE_of_nExt_alt {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T)
    (h : BuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K B f T w Z c) : BuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K B f T w Z c := by
  obtain ⟨b, hb⟩ := h
  exact ⟨{ b with nx := ⟨b.nx.1, Classical.choice (hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2)⟩ }, hb⟩
noncomputable def witnessOfExtensionImplication {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {O : Obj2 (w.D Z)}
    (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K w Z O) : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O :=
  { x with nx := ⟨x.nx.1, Classical.choice (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2)⟩ }
noncomputable def weightedPointOfExtensionImplication {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    {K : Ctx} (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K) : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K :=
  ⟨q.B, q.f, q.T, q.w, q.Z, q.O, _root_.GlobalTheory.HeightCounting.Up.witnessOfExtensionImplication hN q.x⟩
theorem nonempty_bWit_wptOfNExt {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    {K : Ctx} (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (h : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness (_root_.GlobalTheory.HeightCounting.Up.weightedPointOfExtensionImplication hN q) b) := by
  have r := h.recPin
  exact ⟨⟨h.x, h.a, h.ax, h.y,
    { s := ⟨r.s.host, r.s.cols, r.s.full, r.s.g, r.s.theta, r.s.twE, r.s.twGood, r.s.chr, r.s.gal, r.s.nn, r.s.exp, r.s.chiD,
        r.s.twF, r.s.types, r.s.cover, r.s.plB, r.s.thetaChr, r.s.dt, r.s.pieces, r.s.inK, r.s.geo, r.s.tw⟩
      k := ⟨r.k.std, r.k.O, r.k.ent, r.k.adapted, r.k.top⟩
      crd := r.crd, entC := r.entC, std := r.std, rd := r.rd },
    h.s, h.pt, h.sx, h.eF, h.fi, h.uS, h.parts, h.cW, h.d3b, h.side, h.colPins⟩⟩
end GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem rows_of_stronger_nExt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c)) → (∀ K X f T c, IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c) ∧ (∀ K X f T c, IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c) ∧ (∀ K β c b, _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) K β c b → _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b) ∧ ∀ (M : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType), _root_.GlobalTheory.Fc.AllRowsAlt KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) M DR → _root_.GlobalTheory.Fc.AllRowsAlt KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ)) M DR := by
  intro hL N N' S Γ hN
  have hB : ∀ K X f T c, IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c :=
    positionOf_mono (builtE_of_nExt_alt (S := S) (Γ := Γ) hN)
  have hG : ∀ K X f T c, IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c :=
    positionOf_mono fun K B f T w Z c h =>
      ⟨builtE_of_nExt_alt (S := S) (Γ := Γ) hN K B f T w Z c h.1, h.2⟩
  have hLk : ∀ K β c b, _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) K β c b → _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b := by
    rintro K β c b ⟨q, b', ⟨h⟩, e⟩
    exact ⟨_root_.GlobalTheory.HeightCounting.Up.weightedPointOfExtensionImplication hN q, b', _root_.GlobalTheory.HeightCounting.Up.nonempty_bWit_wptOfNExt hN q b' h, e⟩
  refine ⟨hB, hG, hLk, fun M DR A => ?_⟩
  exact {
    hn4 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hn4
    jOn := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.jOn
    hInstR := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hInstR
    aC2 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aC2
    aP10 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aP10
    aAtG := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aAtG
    aPt0 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPt0
    aPtTw := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPtTw
    aPer0 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPer0
    aPerTw := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPerTw
    tie := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.tie
    hRB := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hRB
    hTw := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hTw
    hPA := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hPA
    hLamP := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hLamP
    hDivG := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hDivG
    hDcPtG := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hDcPtG
    selJ := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.selJ
    sLp := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.sLp
    sO := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.sO
    hServ := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hServ
    zL := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.zL
    hTF := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hTF
    rRows := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.rRows
    nRest := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.nRest
    c30 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => let ⟨c, cI, h1, h2, h3⟩ := h; ⟨c, cI, h1, h2, row_mono_id hS hLk h3⟩) A.c30 }
end GlobalTheory.HeightCounting.Up
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem colsStd_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (h : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    q.w.I.Ok ∧ Nonempty (GlobalTheory.Mem.Col2.TC.Pins q.B q.w.px) ∧ GlobalTheory.Mem.Col2.TC.IsTw q.w.I ∧
      Nonempty (GlobalTheory.Mem.Col2.TC.StdC q.w.I q.w.l q.Z b.R.T.cols) ∧ _root_.GlobalTheory.AdForm.TwStdAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  have hs := h.recPin.s
  refine ⟨q.w.ok, ⟨q.w.pins⟩, q.x.pin.isTw, ⟨?_⟩, ?_⟩
  · have e : b.R.T.cols = q.x.col.C := hs.cols
    rw [e]
    exact q.x.col.std
  · obtain ⟨he, hstd⟩ := hs.tw
    exact ⟨q.w.l0, _, he, (eqRec_heq _ _).symm, hstd⟩
end GlobalTheory.Fam
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpTie.Asm
open Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem expSt_of_alt : Formalism.CohomologicalDescent.E.ExCut → _root_.GlobalTheory.ExpTie.NumStAlt → _root_.GlobalTheory.ExpTie.ExponentSumStatement → _root_.GlobalTheory.ExpTie.ModelStatement → _root_.GlobalTheory.BigOn.ExponentStatement := by
  intro hcut hN hS hM
  obtain ⟨a, ha, H⟩ := (hN.and hS).and hM
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, N1⟩, ⟨x2, S1⟩⟩, ⟨x3, M1⟩⟩ := hK Fm CH hc hL
  refine ⟨0, fun c _ _ => ⟨max x1 (max x2 x3), fun x hx hle i p hp hMo r O hR => ?_⟩⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  choose Pj Wj hPW using N1 x hx h1 i p hp hMo
  obtain ⟨st, hRT⟩ := hR.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  intro C CH'
  exact hasExpBound_at p hcut O hRT.m_eq hRT.x_eq hRT.eps_eq hR.1.realisedChain_torus_eq Pj Wj (fun j => (hPW j).1) (fun j => (hPW j).2)
    (fun j t w => S1 x hx h2 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 t w)
    (fun j w hw hR' => M1 x hx h3 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 w hw hR') C CH'
end GlobalTheory.ExpTie.Asm
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
namespace GlobalTheory.ExpTie
theorem smallSt_alt : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  unfold _root_.GlobalTheory.ExpTie.SmallnessCondition _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  refine Formalism.MainNotions.Closed.of_all fun Fm CH => ?_
  refine _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ => ?_
  intro j P W hD hN w _ hWR
  have hC := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hR.ok hR.sep p.charW hR.prim
  have hst := DefFam3.toSub2_stable hC.stable
  have hin := DefFam3.toSub2_inBlock hR.prim.block
  refine ⟨Formalism.EigenvalueLevelCeiling.plc_prime w, ?_, ?_, fun k => DefFam.stable_lifts hst j _ k, DefFam.inBlock_lifts hin j _⟩
  · exact (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLargePrime_holds P hN.1 hN.2.1 _ hWR.1).2.2.2.2.2.1
  · refine not_dvd_discr_host _ (Formalism.EigenvalueLevelCeiling.plc_prime w) ?_
    rw [← hD.special]
    exact hWR.2.2.2
end GlobalTheory.ExpTie
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HalfLabels
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]
end GlobalTheory.HalfLabels
namespace GlobalTheory.HalfLabels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem halfAt_inRange_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ _ _ _ _ _ w _ _ _ => halfAt_all (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w)
end GlobalTheory.HalfLabels
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Int
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]
end Int
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pt
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
theorem kapSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ _ _ p _ _ j P _ _ _ w _ _ _ => kapAt p j P w⟩⟩⟩
end Pt
end GlobalTheory.FrameOf
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem permSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j P W _ _ w _ _ _ => permAt p j P w⟩⟩⟩
end GlobalTheory.FramePerm
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
namespace GlobalTheory.TameStab
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Groups
variable {G Γ : Type} [Group G] [Group Γ]
end Groups
theorem tameSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt Formalism.MainNotions.Closed _root_.GlobalTheory.BigTop.EventuallyAtPoints
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ => ?_⟩⟩⟩
  intro j P W hD _ w _ _ hS
  exact tameAt_of_smallAt p j P w hD.Nr hS
end GlobalTheory.TameStab
end
end
end
