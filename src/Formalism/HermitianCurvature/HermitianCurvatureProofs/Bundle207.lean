module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle131
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle195
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Filter Topology

noncomputable section

theorem xD_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    xD (fun y => φ (y / ε)) = fun x => xD φ (x / ε) := by
  funext x
  simp only [xD]
  have h : (fun y => φ (y / ε)) = fun y => φ (ε⁻¹ * y) := by
    funext y
    rw [div_eq_inv_mul]
  rw [h, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]
  ring

theorem xD_iter_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    xD^[q] (fun y => φ (y / ε)) = fun x => (xD^[q] φ) (x / ε) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih, xD_dil _ hε]
    funext x
    rw [Function.iterate_succ_apply']

theorem xD_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD φ) := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  exact contDiff_id.mul hd

theorem xD_iter_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (q : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] φ) := by
  induction q with
  | zero => simpa using hφ
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact xD_contDiff ih

theorem xD_zero_of_const {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ) (hφ : ∀ y ∈ U, φ y = c) :
    ∀ y ∈ U, xD φ y = 0 := by
  intro y hy
  have h : φ =ᶠ[nhds y] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hy) hφ
  show y * deriv φ y = 0
  rw [h.deriv_eq]
  simp

private theorem xD_iterate_eq_ite_of_const_on_open {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ)
    (hφ : ∀ y ∈ U, φ y = c) : ∀ q : ℕ, ∀ y ∈ U, (xD^[q] φ) y = if q = 0 then c else 0 := by
  intro q
  induction q with
  | zero => intro y hy; simpa using hφ y hy
  | succ q ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    simp only [Nat.succ_ne_zero, if_false]
    exact xD_zero_of_const hU _ ih y hy

theorem truncated_supremum_bound_holds : NFCutSup := by
  unfold NFCutSup
  intro χ hχ q
  obtain ⟨hs, -, h1⟩ := hχ
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] χ) := xD_iter_contDiff hs q
  obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  refine ⟨max K0 1, fun ε hε x hx => ?_⟩
  rw [xD_iter_dil χ hε q]
  show |(xD^[q] χ) (x / ε)| ≤ max K0 1
  have hy : 0 < x / ε := div_pos hx hε
  rcases le_or_gt (x / ε) 1 with hy1 | hy1
  · have hb := hK0 (x / ε) ⟨hy.le, hy1⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left _ _)
  · rw [xD_iterate_eq_ite_of_const_on_open isOpen_Ioi 1 (fun z hz => h1 z (le_of_lt hz)) q (x / ε) hy1]
    refine le_trans ?_ (le_max_right _ _)
    split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nPt_bigPt_eq (k r : ℕ) (TT : ℝ) (c : Fin (r + 1) → ℂ) :
    TBB.nPt k r TT (TBB.bigPt r c) = ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then
      (Complex.normSq (c (Fin.last r)) - TT) ^ (k - 1)
      else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
  unfold TBB.nPt D.ptGG
  rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]
  exact Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights k r _ (r + 1) c 1

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) := by
  simp only [nPt_bigPt_eq]
  refine Finset.measurable_prod _ fun i _ => ?_
  by_cases h : 1 + (i : ℕ) = r + 1
  · simp only [h, if_true]
    exact ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub_const _).pow_const _
  · simp only [h, if_false]
    have hm : Measurable (fun c : Fin (r + 1) → ℂ => ‖c i‖) := continuous_norm.measurable.comp (measurable_pi_apply i)
    exact hm.pow_const _

theorem wPt_bigPt_eq (TT : ℝ) (r : ℕ) (c : Fin (r + 1) → ℂ) :
    Top.wPt TT r (TBB.bigPt r c) = Complex.normSq (∏ i, c i) /
      (Complex.normSq (∏ i, c i) - TT * Complex.normSq (∏ a : Fin r, c a.castSucc)) := by
  show Complex.normSq (D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (r + 1)).det /
    D.ptG TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
  unfold D.ptG
  rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
    Matrix.det_diagonal, Matrix.det_diagonal]

theorem measurable_wPt_bigPt (TT : ℝ) (r : ℕ) :
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) := by
  simp only [wPt_bigPt_eq]
  have h1 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ i, c i)) :=
    (Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply i)).measurable
  have h2 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ a : Fin r, c a.castSucc)) :=
    (Complex.continuous_normSq.comp (continuous_finsetProd _ fun a _ => continuous_apply _)).measurable
  exact h1.div (h1.sub (h2.const_mul TT))

theorem scalar_point_measurability_holds : ScalarMeas := fun k r TT => ⟨measurable_nPt_bigPt k r TT, measurable_wPt_bigPt TT r⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem entry_le_gN {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [← Real.sqrt_sq (norm_nonneg (g i j)), Complex.sq_norm]
  apply Real.sqrt_le_sqrt
  have h1 : Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
    Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun j' _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', Complex.normSq (g i j') ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
    Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
      (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem gN_ball_compact (k r : ℕ) (R : ℝ) : IsCompact {g : B.Mat k r | B.gN g ≤ R} := by
  have hc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max R 0, fun g hg => ?_⟩
  rw [Matrix.norm_le_iff (le_max_right _ _)]
  intro i j
  exact (entry_le_gN g i j).trans (le_trans hg (le_max_left _ _))

theorem cptCoef_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {X : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hX : KB.CptCoef Bs X) (A : ℝ) (m : ℕ) : B.InCC A m X := by
  obtain ⟨R, hR⟩ := hX.2.1
  exact Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hX.1 (gN_ball_compact k r R)
    (fun g hg hgC => by by_contra h; exact hgC (hR g hg h)) A m

theorem empty_list_measurability_holds : EmptyMeas := by
  intro Wp Wq _ _ _ _ _ _ P p X hX
  set Bs := p.T.base with hBs
  set T := Tz P.k P.r Bs.z with hT
  set T' := Tz P.k P.r Bs.z' with hT'
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hc := Formalism.FourierDecayAlt.P.CutBP.jgq_continuousOn Bs hThr (cptCoef_inCC Bs hX A 0)
  have hcn : ContinuousOn (fun q => ‖B.hsVec (B.JF Bs X (B.gq Bs q))‖ ^ 2) (JF.QDom P.k P.r Bs.z Bs.z') :=
    ((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.continuous.comp_continuousOn hc).norm).pow 2
  have hm := Formalism.FourierDecayAlt.P.CutBP.aesm_weight_smul Bs hcn
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have hm2 := hm.comp_measurePreserving hmp
  refine hm2.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc0
  show bcWeight P.k P.r T T' (e c) • ‖B.hsVec (B.JF Bs X (B.gq Bs (e c)))‖ ^ 2 = topD p X [] c
  rw [he c, smul_eq_mul]
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc0
  unfold topD
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p X hl]
  have hk : 2 ≤ P.k := p.hl.2.2
  have hcin : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc0 _
  have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hcin a)
  have hGeq : TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ i : Fin P.r, c i.castSucc) * (Complex.normSq (c (Fin.last P.r)) - T * T') := by
    show D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    ring
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p X c hc0 hG]
    have hζ : T * T' ≤ Complex.normSq (c (Fin.last P.r)) := by
      rw [hGeq] at hG
      have := (pos_iff_pos_of_mul_pos hG).1 hp
      linarith
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r T T' c hζ
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · have hV : p.V X (TBB.bigPt P.r c) = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right (fun h => hG h.2)]
    rw [hV]
    have hw0 : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      unfold bcWeight
      split_ifs with hle
      · have hle2 : Complex.normSq (c (Fin.last P.r)) ≤ T * T' := by
          by_contra hlt
          push Not at hlt
          apply hG
          rw [hGeq]
          exact mul_pos hp (by linarith)
        have hle' : T * T' ≤ Complex.normSq (c (Fin.last P.r)) := hle
        have heq : Complex.normSq (c (Fin.last P.r)) - T * T' = 0 := by linarith
        show (∏ a : Fin P.r, ‖c a.castSucc‖ ^ (2 * (Mdim P.k P.r a - 2))) *
          (Complex.normSq (c (Fin.last P.r)) - T * T') ^ (P.k - 1) = 0
        rw [heq, zero_pow (by omega), mul_zero]
      · rfl
    rw [hw0]
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      rfl
    simp [h0]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

section

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_left (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg hh (Qx8.nlev_one _) (Qx8.uw_one z') (Qx8.nlev_one _)
  simpa using this

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg h hh 1 (Qx8.uw_one z')
  rw [Matrix.one_mul, Matrix.mul_one, hπ.1] at e1
  rw [Matrix.mul_one] at e2
  have e3 : (1 : Wp →L[ℂ] Wp).comp ((J g).comp (π' 1)) = (J g).comp (π' 1) := ContinuousLinearMap.id_comp _
  rw [e3] at e1
  rw [e2, ← e1]

theorem ld_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : QrD.InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : LdV X F g = (B.comp (QrD.dOp π X)).comp (J g) := by
  have h := QrD.dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp B).comp ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_left hD hg (QrD.exp_uw hX t)), J_left hπ hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold LdV
  rw [h3]
  exact h2.deriv

theorem lz_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : QrD.InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (QrD.ecOp π Z)).comp (J g) := by
  unfold LZ QrD.ecOp
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp

theorem fold_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r i ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil =>
    intro F B hF g hg v
    simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
    rw [hF g hg]
    rfl
  | cons p L ih =>
    intro F B hF g hg v
    have hp := hL p (by simp)
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [ih (fun q hq => hL q (by simp [hq])) (p.1 • F + LZ (Hpk k r) p.2 F) (p.1 • B + B.comp (QrD.ecOp π p.2))
      (fun x hx => by
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [lz_left hD hπ hc hJ hF hp.1 hp.2 hx, hF x hx]
        ext v
        simp) g hg v, QrD.ecRep_eq hπ hc hp.1 hp.2]
    simp

end LeftTypeActionHermitianCurvature

theorem left_type_action_holds : LeftTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 := LeftTypeActionHermitianCurvature.fold_left hD hπ hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J 1 (fun x _ => (ContinuousLinearMap.id_comp _).symm) g hg v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1
  simp only [id]
  rw [e1]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wl (A B : ℂ) : ℂ →L[ℝ] ℂ := A • ContinuousLinearMap.id ℝ ℂ + B • Complex.conjCLE.toContinuousLinearMap

theorem wl_apply (A B h : ℂ) : wl A B h = A * h + B * conj h := rfl

section Slice

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wOp (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) : Module.End ℂ (RadSp k r z z' π π') :=
  (js.map (X.op l)).prod

def dT (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 2 * X.op l 0

def dTb (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 5 * X.op l 3

def SlDom (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (Φ : RadSp k r z z' π π') : Prop :=
  ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧
    ∀ t ∈ Metric.ball t0 ε, ∀ c' : Cf r l.succ,
      ‖wtI l.succ c' * pairAt μ Φ Φ (glue l.succ (Function.update c l t) c')‖ ≤ F c'

def SliceGood (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)
    (Φ : RadSp k r z z' π π') : Prop :=
  Φ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') ∧
    ∀ js : List (Fin 6), SlDom μ l c (wOp X l js Φ)

end Slice

def PairAtDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (Φ Ψ : RadSp k r z z' π π'),
    Φ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') →
    Ψ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') →
    ∀ c ∈ OmX r, ∀ (c' : Cf r l.succ) (t : ℂ), t ≠ 0 →
      HasFDerivAt (fun s => pairAt μ Φ Ψ (glue l.succ (Function.update c l s) c'))
        (wl (pairAt μ (dT X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dTb X l Ψ) (glue l.succ (Function.update c l t) c'))
            (pairAt μ (dTb X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dT X l Ψ) (glue l.succ (Function.update c l t) c'))) t

def OuterLeib : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (S : Type) [Fintype S] [DecidableEq S] (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ), c ∈ OmX r →
    (∀ b, SliceGood X μ l c (u b)) → (∀ b, SliceGood X μ l c (v b)) → ∀ t : ℂ, t ≠ 0 →
      HasFDerivAt (fun s => form μ l.succ u v (Function.update c l s))
        (wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
            (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t))) t

end Formalism.FourierDecayAlt.P.CutSE
end
end
