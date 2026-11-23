module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle382
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThreeLeSplitAt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  first | exact @GlobalTheory.Port.jIn_nonempty_true | exact GlobalTheory.Port.jIn_nonempty_true | (intros; apply GlobalTheory.Port.jIn_nonempty_true <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.holds_at_bundlePoints_of_trueColumns : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.AtG.row_aAtG_of_rowPin | exact GlobalTheory.AtG.row_aAtG_of_rowPin | (intros; apply GlobalTheory.AtG.row_aAtG_of_rowPin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_frameValues_positive_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  first | exact @GlobalTheory.TwV.StepDel.del_of_pos | exact GlobalTheory.TwV.StepDel.del_of_pos | (intros; apply GlobalTheory.TwV.StepDel.del_of_pos <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_frameValues_step_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  first | exact @GlobalTheory.TwV.StepZero.del_zero | exact GlobalTheory.TwV.StepZero.del_zero | (intros; apply GlobalTheory.TwV.StepZero.del_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV



theorem joint_at_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  intro hC D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  obtain ⟨E, lam, hK⟩ := GlobalTheory.TwV.exists_cEmbC_lam t std J
  have hin := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨g, hLT, curve⟩ := hC D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) J.cop hin.1 hin.2.1 lam
  obtain ⟨Xi, muT, law⟩ := GlobalTheory.T.exists_adelicDatum_with_laws_at_joint t std J
  exact ⟨{ E := E, lam := lam, hK := hK, g := g, hLT := hLT, curve := curve, hfin := GlobalTheory.TwV.finClasses_sysS t std J, hst := GlobalTheory.TwV.finStab_site t std J, Xi := Xi, muT := muT, law := law }⟩

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Pdv

theorem rowAt_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (AtAll fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) := by
  intro hA hG hD hI Bd Q Lk ker hE
  choose x0 hx0 using GlobalTheory.ShapeUniform.shape_uniform
  refine ⟨fun κ D O c b => x0 κ.eps ≤ O.L.sc.x ∧ StdTie D O (ker D O c b), ?_, ?_⟩
  · have h1 : RowE Q Lk (fun κ D O _ _ => x0 κ.eps ≤ O.L.sc.x) := by
      unfold RowE EvP
      refine ParEv.of_all fun κ _ => ⟨x0 κ.eps, fun K hk hx β _ c b _ => ?_⟩
      show x0 κ.eps ≤ β.p.L.sc.x
      rw [β.sc]
      exact hx
    exact (h1.and hE).mono fun _ _ _ H => H
  · intro 𝒜 σ s eps Fm hc x hx i
    obtain ⟨κ, hl, _, ht⟩ := s Fm hc
    obtain ⟨_, h0, hst⟩ := ht x hx i
    have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
    have hge : x0 eps ≤ x := by
      have h0' : x0 κ.eps ≤ (Fm.L x i).sc.x := h0
      rw [hl.eps_eq, hxx] at h0'
      exact h0'
    have hsh := hx0 eps Fm x hge hx i
    have hsb : 3 ≤ (Fm.D x i).host.splitBound :=
      (hsh (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) (ker _ _ _ (σ Fm hc x hx i)).ent (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0))).2.2
    exact GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison hA hG hD hI (Fm.D x i) (objAt Fm x hx i) (ker _ _ _ (σ Fm hc x hx i)) hst hsb
      Fm.fixed.2.1.ge Fm.fixed.2.2.1.ge (fun Ee => ⟨(hsh Ee).1, (hsh Ee).2.1⟩)

end GlobalTheory.Pdv
end
