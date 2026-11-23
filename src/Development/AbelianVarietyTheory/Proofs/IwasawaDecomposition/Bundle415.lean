module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle020
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle385
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle400
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem toTerm_eTT_symm {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := by
  have termRefl := Eq.refl ((eRT Z Y u u').symm s.toTerm)
  run_tac
    -- The kernel checks the conversion after the equivalences reduce.
    Lean.Elab.Tactic.closeMainGoalUsing `toTerm_eTT_symm fun _ _ => do
      return (← Lean.Meta.getLocalDeclFromUserName `termRefl).toExpr



def eFib {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) :
    fib Y ((eRT Z Y u u').symm t) ≃ fib (reY Z Y) t :=
  ((eTT Z Y u u').symm.subtypeEquiv fun s => by
    rw [toTerm_eTT_symm]
    exact ((eRT Z Y u u').symm.injective.eq_iff).symm).symm



theorem fibFin_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) : Finite (fib (reY Z Y) t) := by
  exact @Finite.of_equiv _ _ (h.fibFin u u' ((eRT Z Y u u').symm t)) (eFib Z Y u u' t)



theorem pairIndep_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (s₁ s₂ s₁' s₂' : TT (reY Z Y) (wd Z u) (wd Z u')) (e₁ : s₁.toTerm = s₁'.toTerm) (e₂ : s₂.toTerm = s₂'.toTerm)
    (r₁ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁ = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂)
    (r₂ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁' = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂') :
    s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂') := by
  have e₁' : ((eTT Z Y u u').symm s₁).toTerm = ((eTT Z Y u u').symm s₁').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₁]
  have e₂' : ((eTT Z Y u u').symm s₂).toTerm = ((eTT Z Y u u').symm s₂').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₂]
  let back := (eTT Z Y u u').symm
  have pair := h.pairIndep u u' (back s₁) (back s₂) (back s₁') (back s₂') e₁' e₂'
  run_tac
    -- The row equalities and the conclusion convert by reduction in the kernel.
    Lean.Elab.Tactic.closeMainGoalUsing `pairIndep_re fun _ _ => do
      let localExpr := fun name => return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
      return Lean.mkApp2 (← localExpr `pair) (← localExpr `r₁) (← localExpr `r₂)


set_option maxHeartbeats 16000000 in
theorem finX_reY : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  intro D Z X Y h
  refine
    { shInj := ?_
      shSurj := ?_
      inHH := ?_
      puLin := ?_
      finHH := ?_
      fibFin := ?_
      pairIndep := ?_
      Greal := fun u u' t => ?_
      cdEx := ?_
      volPos := ?_ }
  run_tac
    -- Elaborate the field proofs independently and let the kernel check their conversion.
    let h := Lean.mkIdent `h
    let Z := Lean.mkIdent `Z
    let Y := Lean.mkIdent `Y
    let u := Lean.mkIdent `u
    let u' := Lean.mkIdent `u'
    let t := Lean.mkIdent `t
    let fields := [
      ← `(FinX.shInj $h),
      ← `(FinX.shSurj $h),
      ← `(FinX.inHH $h),
      ← `(FinX.puLin $h),
      ← `(FinX.finHH $h),
      ← `(fibFin_re $Z $h),
      ← `(pairIndep_re $Z $h),
      ← `(FinX.Greal $h $u $u' ((eRT $Z $Y $u $u').symm $t)),
      ← `(FinX.cdEx $h),
      ← `(FinX.volPos $h)]
    for field in fields do
      Lean.Elab.Tactic.closeMainGoalUsing `finX_reY fun _ _ =>
        Lean.Elab.Term.elabTerm field none

end GlobalTheory.Mem.SRe

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.LayOfCore

variable {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B}

theorem ties (c : V4.Core K X f T) : Formalism.BasicNotions.Ties X.toD7 :=
  ⟨c.real.cdScale, c.real.dsig_all, c.row.bu_def, twCoverPair_of_tie _ _ c.nch_tie, X.B.coeffGaloisSubfield_isGalois, c.row.ft_occ⟩

theorem dgam (c : V4.Core K X f T) : DGamDef X.toD7 := fun u μ =>
  ⟨fun u' μ' i hi x => by
    rw [c.col.one u μ, ← c.col.one u' μ']
    exact (X.toD7.chTw u' μ').dvd_DGam i hi x, c.col.one u μ⟩

noncomputable def lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : Lay X.toD7 :=
  { c.O with
    ties := ties c
    rrDef := c.row.rrDef
    th_io := c.th_io
    vram := c.gy.vram
    fills_all := c.gy.fills
    idx := c.row.idx
    kap_def := c.row.kap_def
    lam_def := c.row.lam_def
    kapR_def := c.row.kapR_def
    piG_lev := c.col.piG_lev
    piT_lev := c.col.piT_lev
    seen := c.col.seen
    tauOf := c.col.tauOf
    dgam := dgam c
    nch_tie := c.nch_tie
    rationalRoots_def := c.row.rationalRoots_def
    duStar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).1
    Dstar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).2
    gauge_def := c.gauge_def }

theorem layObj_lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : layObj (lay c hv) = c.O := rfl

theorem isOver (c : V4.Core K X f T) : Over X.toD7 K.P K.Lv := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := c.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, X, h, rfl⟩

theorem untw (c : V4.Core K X f T) (w : X.toD7.what₂.places.Pl) (hw : X.toD7.what₂.muAt w = X.toD7.what₂.mu0) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ X.toD7.R.m) : X.toD7.what₂.Aj j w = 0 := by
  have a := c.row.untw w hw j h1 h2
  have b := c.row.untw (X.toD7.what₂.places.conj w) ((X.toD7.what₂.muAt_conj w).trans hw) j h1 h2
  unfold Rows.Data.Aj
  rw [hw, a.1, a.2, b.1]
  rfl

theorem fin (c : V4.Core K X f T) : {w | X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0}.Finite :=
  (TwFin.tw_fin X.B f T).2.2.2.subset fun w hw => c.mu.sub w (by_contra fun h => hw (c.mu.off w h))

theorem ledOK (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : LedOK K.s K.C K.cD K.ch (lay c hv) K.a K.b := by
  intro L hs hW hV
  refine ⟨fun w hw j hj => ?_, fun I hI he hk hf => ⟨c.gy.led L hs hW hV I hI he hk hf, fun u w hg => ?_, fun u w hg _ =>
    NP_full X.toD7 L I c.O.Gy K.C.GK c.O.cmp c.gy.vram u w hg⟩⟩
  · refine c.fval L hs hW hV w (fun h => (TwFin.tw_fin X.B f T).2.1 w ?_) j hj
    rw [← c.mu.tw w, ← c.mu.on w h]
    exact (congrArg c.xi hw).trans c.mu.mu0
  · have hC : K.C.cX.Ce = 1 := by
      have := K.std.1
      unfold FC.Fixed at this
      tauto
    rw [(c.gatNum u w hg).2, he, hC, hs]

theorem tupUsed (c : V4.Core K X f T) : DQ.TupUsedAt X.toD7 := by
  intro μ
  have hμ : c.xi μ ∈ T.set f := c.mu.range ▸ Set.mem_range_self μ
  rcases hμ with (h | h | h) | ⟨w, h⟩
  · exact .inl (c.mu.inj (h.trans c.mu.mu0.symm))
  · exact .inr (.inl (c.mu.inj (h.trans c.mu.star.symm)))
  · exact .inr (.inr (.inl (c.mu.inj (h.trans c.mu.star'.symm))))
  · by_cases hw : w ∈ c.Wt
    · exact .inr (.inr (.inr ⟨w, (c.mu.inj (h.symm.trans (c.mu.tw w).symm)).trans (c.mu.on w hw).symm⟩))
    · unfold TwDat.xiTw at h
      rw [c.mu.supp w hw, mul_one] at h
      split_ifs at h
      · exact .inr (.inr (.inl (c.mu.inj (h.symm.trans c.mu.star'.symm))))
      · exact .inr (.inl (c.mu.inj (h.symm.trans c.mu.star.symm)))

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem lay_of_core : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T),
    StandardLattice.VolumeEqMass₂ X.toD7 → ∃ Y : Lay X.toD7, layObj Y = c.O ∧ Over X.toD7 K.P K.Lv ∧ RecOK K.s K.C K.cD X.toD7 ∧
      LedOK K.s K.C K.cD K.ch Y K.a K.b ∧ DQ.TupUsedAt X.toD7 :=
  ev_imp TamePow.tame_of_pow fun _ hK X _ _ c hv =>
    ⟨lay c hv, layObj_lay c hv, isOver c,
      ⟨c.del, c.etaF, untw c, fin c, (Full.dgam_pos_and_full X.toD7).1, (Full.dgam_pos_and_full X.toD7).2,
        hK X c.isOver c.chiT, c.col.mink, c.col.atT⟩, ledOK c hv, tupUsed c⟩

end GlobalTheory.Mem.Top.LayOfCore
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsExactCond

theorem ksCond_exact : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt →
    V4.KsCond fun B f => ∃ δ : FieldDat B.toPre, B.KsExact δ f := by
  intro hR hP hA
  refine ⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

end GlobalTheory.Mem.KsExactCond
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.domain_point_stabilizer_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  first | exact @GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | exact GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | (intros; apply GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.ChiType

theorem embLL_chiAt_eq_levChi : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (w : Pl X.toD7.host.E) (hw : w ∈ (X.B.primes px).vGs) (u : (kP w)ˣ),
      X.toD7.what₂.embLL ((Formalism.L2.Col.chiAt I.Ch ⟨w, hw⟩ (i : ℕ) u : X.B.fields.Kˣ) : X.B.fields.K) =
        ((L.chi ((i : ℕ) + 1) w u : ℂˣ) : ℂ) := by
  intro X px I U L hI hL i w hw u
  have hw' : w ∈ L.Pg := hL.Pg ▸ hw
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP w)
  have hu0 : (u : kP w) ≠ 0 := u.ne_zero
  have ha0 : ((a : 𝓞 X.toD7.host.E) : X.toD7.host.E) ≠ 0 := by
    intro h0
    apply hu0
    rw [← ha, (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 X.toD7.host.E) X.toD7.host.E).1 h0, map_zero]
  let k : X.toD7.host.Eˣ := Units.mk0 _ ha0
  have h1 := (hI.ch_tied.mu0 i).atg ⟨w, hw⟩ k a u rfl ha.symm
  have h2 := hL.is.chi i w hw' a k u rfl ha.symm
  rw [hL.C] at h2
  have h2' : (L.chi ((i : ℕ) + 1) w u : ℂˣ) = ((((Top.Fr.at X I.C).mu0 i).locK w k))⁻¹ := by
    rw [← h2, MonoidHom.inv_apply, inv_inv]
  have e : Formalism.L2.Col.chiAt I.Ch ⟨w, hw⟩ (i : ℕ) u = I.Ch.chi i ⟨w, hw⟩ u := by
    simp only [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
    rw [dite_eq_left (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e, h2', Units.val_inv_eq_inv_val]
  change _ = (((((I.C.mu0 i).locK (⟨w, hw⟩ : {w // w ∈ (X.B.primes px).vGs}).1) k : ℂˣ) : ℂ))⁻¹
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  rfl

end GlobalTheory.Mem.ChiType
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



noncomputable section
namespace GlobalTheory.Mem.R3.LevChi

theorem chi_succ_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (w : {w // w ∈ (X.B.primes px).vGs}) (c : (𝓞 X.B.fields.E ⧸ w.1.asIdeal)ˣ),
      L.chi ((i : ℕ) + 1) w.1 c = Units.map X.toD7.what₂.embLL.toMonoidHom (Formalism.L2.Col.chiAt I.Ch w (i : ℕ) c) := by
  intro X px I U L hI hL i w c
  have hw : w.1 ∈ L.Pg := by rw [hL.Pg]; exact w.2
  have hres := hL.is.chi i w.1 hw
  have hmu : L.C.mu0 i = I.C.mu0 i := by rw [hL.C]; rfl
  rw [hmu] at hres
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ w.1.asIdeal)
  have hy0 : ((y : 𝓞 X.B.fields.E) : X.B.fields.E) ≠ 0 := by
    intro h
    have h0 : y = 0 := RingOfIntegers.ext h
    apply c.ne_zero
    rw [← hy, h0, map_zero]
  let x : X.B.fields.Eˣ := Units.mk0 _ hy0
  have h1 := hres y x c rfl hy.symm
  have h2 := (hI.ch_tied.mu0 i).atg w x y c rfl hy.symm
  have h3 : (((L.chi ((i : ℕ) + 1) w.1 c)⁻¹ : ℂˣ) : ℂ) = X.B.embLL (((I.Ch.chi i w c)⁻¹ : X.B.fields.Kˣ) : X.B.fields.K) :=
    (congrArg Units.val h1).trans h2
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀] at h3
  have h5 : ((L.chi ((i : ℕ) + 1) w.1 c : ℂˣ) : ℂ) = X.B.embLL ((I.Ch.chi i w c : X.B.fields.Kˣ) : X.B.fields.K) :=
    inv_injective h3
  have e : Formalism.L2.Col.chiAt I.Ch w (i : ℕ) = I.Ch.chi i w := by
    unfold Formalism.L2.Col.chiAt Formalism.L2.Col.extChi
    rw [dite_eq_left (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e]
  exact Units.ext h5

end GlobalTheory.Mem.R3.LevChi
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

theorem exists_int_of_finite {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {G : Type} [Group G] [Finite G]
    (f : G →* ℂˣ) (g : G) (h : ∃ y : K, σ y = ((f g : ℂˣ) : ℂ)) : ∃ z : 𝓞 K, σ (z : K) = ((f g : ℂˣ) : ℂ) := by
  obtain ⟨y, hy⟩ := h
  have hn : 0 < Nat.card G := Nat.card_pos
  have hfg : (f g) ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hy1 : y ^ Nat.card G = 1 := by
    apply σ.injective
    rw [map_pow, hy, map_one, ← Units.val_pow_eq_pow_val, hfg, Units.val_one]
  have hint : IsIntegral ℤ y := IsIntegral.of_pow hn (by rw [hy1]; exact isIntegral_one)
  exact ⟨⟨y, hint⟩, hy⟩

end GlobalTheory.MtIn


open GlobalTheory.MtIn in
theorem GlobalTheory.MtIn.levChi_integral : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (k : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J), ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ k : ℂ) := by
  intro X px I U L hI hL i t k
  have hfin : ∀ PP : Pl X.toD7.host.E, Finite (kP PP)ˣ := fun PP =>
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    Finite.of_injective _ Units.val_injective
  have lift : ∀ (PP : Pl X.toD7.host.E) (d : (kP PP)ˣ), ∃ (a : 𝓞 X.toD7.host.E) (kE : X.toD7.host.Eˣ),
      (kE : X.toD7.host.E) = a ∧ (d : kP PP) = Ideal.Quotient.mk _ a := by
    intro PP d
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d : kP PP)
    have ha0 : (a : X.toD7.host.E) ≠ 0 := by
      intro h0
      have : a = 0 := by exact_mod_cast h0
      apply d.ne_zero
      rw [← ha, this, map_zero]
    exact ⟨a, Units.mk0 _ ha0, rfl, ha.symm⟩
  have hchi : ∀ PP ∈ L.Pg, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = (((L.chi ((i : ℕ) + 1) PP)⁻¹ d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.chi i PP hPP a kE d h1 h2
    rw [hres, hL.C]
    have hw : PP ∈ (X.B.primes px).vGs := hL.Pg ▸ hPP
    exact ⟨_, ((hI.ch_tied.mu0 i).atg ⟨PP, hw⟩ kE a d h1 h2).symm⟩
  have hxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = ((L.xiR t PP d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.xiR t PP hPP a kE d h1 h2
    rw [hres, hL.xiH t]
    exact ⟨_, (hI.xi_reads (ixOf I U t) _).symm⟩
  let Pr : ℂˣ → Prop := fun u => ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = (u : ℂ)
  have hmul : ∀ a b : ℂˣ, Pr a → Pr b → Pr (a * b) := by
    rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
    exact ⟨za * zb, by rw [Units.val_mul, ← ha, ← hb, ← map_mul]; rfl⟩
  have hone : Pr 1 := ⟨1, by rw [Units.val_one, ← map_one X.toD7.what₂.embLL]; rfl⟩
  have gchi : ∀ PP ∈ L.Pg, ∀ (c : ℕ) (d : (kP PP)ˣ), Pr ((if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else
      fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) c PP d) := by
    intro PP hPP c d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) =
        fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹ := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.chi ((i : ℕ) + 1) PP)⁻¹ d (hchi PP hPP d)
  have gxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, Pr ((if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) PP d) := by
    intro PP hPP d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) = L.xiR t := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.xiR t PP) d (hxi PP hPP d)
  show Pr (Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t)) _)
  unfold Formalism.L2.DIV.levFn
  refine hmul _ _ (hmul _ _ ?_ (Finset.prod_induction _ Pr hmul hone fun PP hPP =>
    Finset.prod_induction _ Pr hmul hone fun c _ => ?_)) (Finset.prod_induction _ Pr hmul hone fun PP hPP => ?_)
  · unfold Formalism.L2.DIV.ext1
    split_ifs
    · exact hone
    · exact hone
  · exact gchi PP hPP (c + 1) _
  · exact gxi PP hPP _
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.diamondOperators_on_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}), I.ReadsK l Z u a i hi chOf K → (∀ β, FunKilled (K β).lev (X.piT u)) → I.IdY l Z u a i hi eY → I.IdV l u a eV → DilationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY eV chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  first | exact @GlobalTheory.Mem.Col2.DiaChart.dilTied | exact GlobalTheory.Mem.Col2.DiaChart.dilTied | (intros; apply GlobalTheory.Mem.Col2.DiaChart.dilTied <;> assumption)
end
