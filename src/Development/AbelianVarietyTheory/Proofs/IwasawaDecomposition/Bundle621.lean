module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle549
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle008
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle002
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_adelicReading_decoratedLatticeForms : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  first | exact @GlobalTheory.Mem.R3.BrgRead.exists_brgL | exact GlobalTheory.Mem.R3.BrgRead.exists_brgL | (intros; apply GlobalTheory.Mem.R3.BrgRead.exists_brgL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem levels_cls_cmp_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨Lv, I, H, hC, hX, hE0⟩ : ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
    by_cases hμ : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0
    · exact GlobalTheory.T.exists_comparisonData_steps_upTo_rank w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
    · exact GlobalTheory.T.comparison_data_steps_non_reference_tuple w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
  classical
  let S := Formalism.MainNotions.G.CmpJ.stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds t.Gt
  let clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1) :=
    fun j a L => if hj : j + 1 ≤ (w.D Z).R.m then
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else (hE0 j (by omega)).elim a
  have hcls : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) a L, clsS j a L =
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L) :=
    fun j hj a L => dif_pos hj
  refine ⟨Lv, clsS, Formalism.L2.G.Cmp.CmpUp.ofRat S.cmpS S.injS S.ratS, ?_, ?_, ?_⟩
  · intro j hj a a' L L' hL hL'
    rw [hcls j hj, hcls j hj, (Formalism.MainNotions.G.KAat.castCls_inj _ _).eq_iff]
    exact Formalism.MainNotions.G.KAat.clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (hX j hj) a a' L L' hL hL'
  · intro j hj x
    obtain ⟨x0, rfl⟩ := Formalism.MainNotions.G.KAat.castCls_surj (hC j hj) (j + 1) x
    obtain ⟨a, L, hL, e⟩ := Formalism.MainNotions.G.KAat.clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
    exact ⟨a, L, hL, (hcls j hj a L).trans (congrArg _ e)⟩
  · intro j hj
    exact S.intS (Formalism.MainNotions.G.CmpJ.descUp H t.Gt) j hj

end GlobalTheory.Mem.Top.KerOne
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  first | exact @GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt | exact GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt | (intros; apply GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.R3.LamMetric.inner_theta_eq_lam | exact GlobalTheory.Mem.R3.LamMetric.inner_theta_eq_lam | (intros; apply GlobalTheory.Mem.R3.LamMetric.inner_theta_eq_lam <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  first | exact @GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read | exact GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read | (intros; apply GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read <;> assumption)
end
