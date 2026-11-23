module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle487
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.SiteGoodPrimeTorsion
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_rowForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ)  := by
  first | exact @GlobalTheory.Mem.R3.RowsRead.exists_rowSide | exact GlobalTheory.Mem.R3.RowsRead.exists_rowSide | (intros; apply GlobalTheory.Mem.R3.RowsRead.exists_rowSide <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.Mem.Top.KerTwLv

theorem fill_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      Formalism.MainNotions.G.CmpJ.FillTie t.Gt u v hg (Fl u v hg) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  intro x s b hb
  have h1 := hw u v hg x s (b + 1) (by simp [SizeData₂.lifts]; omega)
  apply (Rat.cast_injective (α := ℝ))
  rw [Formalism.BasicNotions.D7.hcW_e]
  have e : (((((Fl u v hg).w x (b + 1) s : ℤ) : ℚ)) : ℝ) = (((Fl u v hg).w x (b + 1) s : ℤ) : ℝ) := by push_cast; rfl
  rw [e, h1]
  unfold wj G.kaJ wG
  rw [dite_eq_left (by omega)]
  push_cast
  ring

theorem fin_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Finite (Formalism.L2.G.compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
          (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt _ j hj β
  exact finite_compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram _ _ _
    (fun x hx => ((tt.ch.lev u _ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).U_eq x).1 hx)
    (tt.ch.finite_cls u _ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β)



theorem cmpJ_data_ne : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro hμ
  obtain ⟨tt, htt⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData w.I w.ok w.pins w.l Z w.l0 nch n.tp t.C n.xi t.std t.stdLv
  have hpl := GlobalTheory.T.served_place_no_chain_place_or_type_prime_over w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  obtain ⟨dt, hdt⟩ := GlobalTheory.T.twisted_chart_levels_determinant_maps_values w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hB := GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hψ := GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfin := fin_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfill := fill_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  let Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg :=
    { B := fun j hj => (hB j hj).choose
      fr_lat := fun j hj β => (hB j hj).choose_spec.2 β
      ψ := fun j hj β => (hψ j hj β).choose
      fin := hfin }
  have hhyp := GlobalTheory.T.twisted_chain_charts_hyperspecial_stabilise_lattice w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt hpl Cd
  let Zt := Formalism.MainNotions.G.KAat.atInTw (X0 := t.g.herm) tt.forms u ((w.D Z).what₂.muAt v) hμ dt (Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1)
  have A : Formalism.MainNotions.G.ChF.HypTies Zt t.Gt t.cmp :=
    { fl_t := (hfl u v hg).1
      fill := hfill
      step := fun j hj =>
        { frRat := fun β => Cd.frRat t.Gt (Fl u v hg) (hfl u v hg).1 j hj β
          sameU := fun β => Cd.sameU tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β
          hypT := fun β => (hhyp j hj β).1
          bad_p := hpl.2.1
          std := (hB j hj).choose_spec.1
          psi := fun β => (hψ j hj β).choose_spec
          chRat := hdt j hj
          hypC := fun β => (hhyp j hj β).2
          ok := hpl.1
          siteGood_prime_torsion := hpl.2.2
          Lb_eq := fun β => Cd.Lb_eq tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β } }
  exact ⟨Cd.Lv t.Gt (Fl u v hg) (hfl u v hg).1, Zt.I t.Gt, A.hyp t.g.cmp, fun j hj => rfl,
    fun j hj => (A.atHyp t.g.cmp).chX j hj, fun j hj => Cd.empty t.Gt (Fl u v hg) (hfl u v hg).1 j hj⟩

end GlobalTheory.Mem.Top.KerTwLv
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem WPt.colsTwTied : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), q.O.ex.tw = q.w.tw q.Z ∧ ∃ tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes q.x.n.tp q.x.col.C (q.w.tw q.Z), TC.StdTw q.w.I q.w.l q.Z q.w.l0 tw ∧ Formalism.L2.Rows.EMtTied (q.w.D q.Z) q.x.col.C tw := by
  intro 𝒮 K q
  refine ⟨?_, ?_⟩
  · exact congrArg (fun s : Σ (Gt : GatTies (q.w.D q.Z)) (cmp : LatCmp (q.w.D q.Z)) (tw : TwForms (q.w.D q.Z)),
      KerFam (q.w.D q.Z) Gt cmp tw (ofObj q.O).Gy => s.2.2.1) q.x.ker_eq
  · obtain ⟨tw, htw⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C q.x.n.xi q.x.col.std q.x.col.stdLv
    exact ⟨tw, htw, GlobalTheory.Mem.Col2.EMt.eMtTied q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C tw q.x.what₂.emt0 q.x.what₂.emt⟩

end GlobalTheory.Mem.Top.Bl

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  first | exact @GlobalTheory.HeightCounting.Up.sizes_host_at_record | exact GlobalTheory.HeightCounting.Up.sizes_host_at_record | (intros; apply GlobalTheory.HeightCounting.Up.sizes_host_at_record <;> assumption)
end
