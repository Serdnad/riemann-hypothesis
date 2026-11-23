module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviTransfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem borel_diag_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  have hdet := (hb τ).1
  have htri : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  rw [Matrix.det_of_upperTriangular htri] at hdet
  exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)


omit [NumberField E] [IsCMField E] in
theorem borel_char_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (la : Wt Ψ r) : bchar la b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    zpow_ne_zero _ (borel_diag_ne_zero hb τ i)


omit [NumberField E] [IsCMField E] in
theorem left_act_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1) * mat x τ :
    Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem normFactor_pos {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos
    (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _

theorem metric_rmul (h : NfacRmulStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phla X la (rmul x b) = phla X la x + Real.log (Complex.normSq (bchar la b)) := by
  have h1 := normFactor_pos X la hx
  have h2 : 0 < ‖bchar la b‖ := norm_pos_iff.2 (borel_char_ne_zero hb la)
  unfold phla
  rw [h r X la x hx b hb, Real.log_mul (inv_pos.2 h2).ne' h1.ne', Real.log_inv,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

theorem levi_transfer :
    (KapGGStatement (E := E)) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) := by
  intro hK hN r X x0 z hz
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hz
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hcd : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c =>
      (IW.cpt_entry_cd X x0 τ a c).differentiable (by simp)
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter
      (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hdet := hK r X x0 x1 1 U Φ bf hU hΦ (fun w hw =>
    ⟨hw.1, (hsplit _ hw.1 hw.2).2.1, by
      rw [left_act_one]; exact (hsplit _ hw.1 hw.2).2.2⟩) z hzU
  have hdet' : (fderiv ℂ Φ z).det ≠ 0 := by
    rw [hdet]; exact borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    have hu : IsUnit ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet')
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨x1, (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).toLinearMap ∘ₗ
    ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.toLinearMap, ho, ?_, ?_⟩
  · exact (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).injective.comp
      (hinj.comp (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.injective)
  intro la ξ
  have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
    classical
    intro w hw
    unfold bchar
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
      fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
      fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
    have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
      differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
    have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
      differentiableAt_zpow.2 (Or.inl (borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
    exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
  have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
    (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
  have hne : bchar la (bf z) ≠ 0 := borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
    rw [← metric_rmul hN.1 X la h1 h2, ← h3]
  have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
    rw [hΦz]
    exact (IW.phla_cpt_cdAt X x1 (IW.zero_mem_OmF X x1 ho) la).of_le HE.two_le_inf
  have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
    hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
    (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
  have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
  rw [hΦz] at hc
  unfold leviM
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
    HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
  exact congrArg Complex.re hc

end GlobalTheory.LeviTransfer
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrthNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.OrthNear.isOrth_x0F {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth
  intro τ
  generalize_proofs h
  exact (h τ).choose_spec.2

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem mat_cpt_eq_mat_mul_mat_nmat {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_mul_apply_eq_sum {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M N : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * N) = Matrix.of fun a b =>
      ∑ c, ∑ d, N c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G M c d * starRingEnd ℂ (N d b) := by
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * N) a = ∑ c, N c a • _root_.ReciprocityTheory.ChartRestriction.G.FD.col M c := by
    intro a
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mulVec_eq_sum_col]
    ext k
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, hcol, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_chartCoord_orthonormal_indep_lemma {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ) := by
  have hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) :=
    (hx τ).trans (hy τ).symm
  rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, gram_mul_apply_eq_sum, gram_mul_apply_eq_sum, hx']


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.OrthNear.dmin_cpt_eq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ i := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_chartCoord_orthonormal_indep_lemma X hx hy z τ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem densF_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y z := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem nfac_cpt_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem cpt_mem_dom_iff_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z ∈ X.dom := by
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ).det ≠ 0 ↔
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, Matrix.det_mul, Matrix.det_mul]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hx τ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hy τ]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_setOf_eq, hdet,
    _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.OrthNear.orthNear : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ c ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ≤ C ∧ c ≤ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∧ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ≤ C) := by
  intro r X la
  set x0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 := _root_.GlobalTheory.OrthNear.isOrth_x0F X
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.mp (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X x0) 0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF X x0 h0)
  set K := Metric.closedBall (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (ρ0 / 2)
  have hKsub : K ⊆ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨0, Metric.mem_closedBall_self (by linarith)⟩
  have hd : ContinuousOn (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) K := (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  have hn : ContinuousOn (fun z => X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) K :=
    (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont X x0 la).mono hKsub
  obtain ⟨z1, hz1, hmin1⟩ := hK.exists_isMinOn hKne hd
  obtain ⟨z2, hz2, hmin2⟩ := hK.exists_isMinOn hKne hn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hd
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hn
  refine ⟨ρ0 / 2, min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 z1) (X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z2)), max C1 C2,
    by linarith, lt_min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hKsub hz1)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X x0 (hKsub hz2)), ?_⟩
  intro x hx z hz
  have hzK : z ∈ K := Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hz.le)
  have hdom : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hKsub hzK
  rw [densF_eq_of_isOrth X hx h0, nfac_cpt_eq_of_isOrth X hx h0,
    cpt_mem_dom_iff_of_isOrth X hx h0]
  exact ⟨hdom, (min_le_left _ _).trans (isMinOn_iff.mp hmin1 z hzK),
    (Real.le_norm_self _).trans ((hC1 z hzK).trans (le_max_left _ _)),
    (min_le_right _ _).trans (isMinOn_iff.mp hmin2 z hzK),
    (Real.le_norm_self _).trans ((hC2 z hzK).trans (le_max_right _ _))⟩

end GlobalTheory.OrthNear
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.leviForm_weightMetric_orthonormal_diagonal : (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) := by
  first | exact @GlobalTheory.LeviZero.leviZero | exact GlobalTheory.LeviZero.leviZero | (intros; apply GlobalTheory.LeviZero.leviZero <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartChange

open Filter

theorem lintegral_ball_lt_top_of_localInverse {n : ℕ} (η θ : V n → V n) {U : Set (V n)} (hU : IsOpen U)
    (h0 : (0 : V n) ∈ U) (hη : DifferentiableOn ℂ η U) (hθ : ContinuousAt θ 0) (hθ0 : θ 0 = 0)
    (hηθ : ∀ᶠ z in 𝓝 (0 : V n), η (θ z) = z) (hθη : ∀ᶠ w in 𝓝 (0 : V n), θ (η w) = w)
    (g h : V n → ℝ≥0∞) (hgh : ∀ w ∈ U, g (η w) = h w) {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ w in Metric.ball (0 : V n) ρ, h w < ⊤) :
    ∃ S ∈ 𝓝 (0 : V n), ∫⁻ z in S, g z < ⊤ := by
  have hcd : ContDiffOn ℝ ∞ η U := by
    refine (contDiffOn_piLp 2).2 fun i => ?_
    have hi : DifferentiableOn ℂ (fun z => η z i) U := (differentiableOn_piLp 2).1 hη i
    exact (contDiffOn_of_differentiableOn n _ U hU hi).restrict_scalars ℝ
  have hfc : ContinuousAt (fun w => |(fderiv ℝ η w).det|) 0 := by
    have h1 : ContinuousOn (fderiv ℝ η) U := hcd.continuousOn_fderiv_of_isOpen hU (by simp)
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp (h1.continuousAt (hU.mem_nhds h0))).abs
  set C : ℝ := |(fderiv ℝ η 0).det| + 1 with hC
  have hb : ∀ᶠ w in 𝓝 (0 : V n), |(fderiv ℝ η w).det| < C := hfc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ w in 𝓝 (0 : V n), w ∈ U ∧ w ∈ Metric.ball (0 : V n) ρ ∧ θ (η w) = w ∧
      |(fderiv ℝ η w).det| < C := by
    filter_upwards [hU.mem_nhds h0, Metric.ball_mem_nhds (0 : V n) hρ, hθη, hb] with w a b c d
    exact ⟨a, b, c, d⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨η '' Metric.ball 0 δ, ?_, ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 (0 : V n), θ z ∈ Metric.ball (0 : V n) δ :=
      hθ.eventually (by rw [hθ0]; exact Metric.ball_mem_nhds _ hδ)
    filter_upwards [h1, hηθ] with z hz1 hz2
    exact ⟨θ z, hz1, hz2⟩
  · have hd : ∀ w ∈ Metric.ball (0 : V n) δ,
        HasFDerivWithinAt η (fderiv ℝ η w) (Metric.ball (0 : V n) δ) w := fun w hw =>
      (((hcd.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hB w hw).1)).hasFDerivAt).hasFDerivWithinAt
    have hinj : Set.InjOn η (Metric.ball (0 : V n) δ) := fun w hw w' hw' e => by
      rw [← (hB w hw).2.2.1, e, (hB w' hw').2.2.1]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hd hinj]
    calc ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal |(fderiv ℝ η w).det| * g (η w)
        ≤ ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal C * h w := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          rw [hgh w (hB w hw).1]
          gcongr
          exact (hB w hw).2.2.2.le
      _ = ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) δ, h w :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) ρ, h w := by
          exact mul_le_mul_right (lintegral_mono_set fun w hw => (hB w hw).2.1) _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open ExtFPf in
theorem zOf_zOf {r : ℕ} {X : Data E r} {x1 b c : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hbc : ∀ τ, mat b τ * mat c τ = 1) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (hcz : cpt X (rmul x1 c) z ∈ cell D) :
    D.zOf (cpt X (rmul x1 b) (D.zOf (cpt X (rmul x1 c) z))) = z := by
  obtain ⟨-, hβ, he⟩ := D.split _ hcz.1 hcz.2
  set w := D.zOf (cpt X (rmul x1 c) z)
  set β := D.bOf (cpt X (rmul x1 c) z)
  have hx1 := IW.orth_mem_dom X x1 ho
  have key : cpt X (rmul x1 b) w = rmul (cpt X x1 z) (invF X β) := by
    funext τ
    have e : mat x1 τ * mat c τ * mat (nmat X z) τ = mat x1 τ * mat (nmat X w) τ * mat β τ := congrFun he τ
    have hu : IsUnit (mat x1 τ).det := isUnit_iff_ne_zero.mpr (hx1 τ).1
    have huβ : IsUnit (mat β τ).det := isUnit_iff_ne_zero.mpr (hβ τ).1
    have e2 : mat c τ * mat (nmat X z) τ = mat (nmat X w) τ * mat β τ := by
      have := congrArg (fun M => (mat x1 τ)⁻¹ * M) e
      simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this
    have e3 : mat (nmat X z) τ = mat b τ * mat (nmat X w) τ * mat β τ := by
      rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hbc τ, Matrix.one_mul]
    show mat x1 τ * mat b τ * mat (nmat X w) τ = mat x1 τ * mat (nmat X z) τ * (mat β τ)⁻¹
    rw [e3]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huβ, Matrix.mul_one]
  rw [key]
  exact (D.uniq z hz _ (invF_mem X hβ)).2.1

open ExtFPf in
theorem cpt_zero_cell {r : ℕ} {X : Data E r} {x1 b : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hb : b ∈ Bor X.Ψ r) :
    cpt X (rmul x1 b) 0 ∈ cell D ∧ D.zOf (cpt X (rmul x1 b) 0) = 0 := by
  have h := D.uniq 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero] at h
  rw [IW.cpt_zero]
  exact ⟨⟨OrthogonalFrameDomain.rmul_mem_dom X (IW.orth_mem_dom X x1 ho) hb, h.1⟩, h.2.1⟩


open ExtFPf in
theorem chart_change : ∀ (r : ℕ) (X : Data E r) (x1 b : Frame X.Ψ r), IsOrth X x1 → b ∈ Bor X.Ψ r →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∀ ρ : ℝ, 0 < ρ → ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, φ (cpt X (rmul x1 b) z) < ⊤ →
    ∃ ρ' : ℝ, 0 < ρ' ∧ Metric.ball (0 : V (nd X)) ρ' ⊆ OmF X x1 ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', φ (cpt X x1 z) ∂muF X x1 < ⊤ := by
  intro r X x1 b ho hb φ _ hφ ρ hρ hint
  obtain ⟨D⟩ := luData_of lu_holds X x1 ho
  have hc := invF_mem X hb
  have hop : ∀ y : Frame X.Ψ r, IsOpen (cpt X y ⁻¹' cell D) := fun y =>
    (isOpen_cell D).preimage (OntoB.cd_cpt X y).continuous
  have hdiff : ∀ y : Frame X.Ψ r, DifferentiableOn ℂ (fun z => D.zOf (cpt X y z)) (cpt X y ⁻¹' cell D) :=
    fun y => D.hz.comp ((OntoB.cd_cpt X y).differentiable (by simp)).differentiableOn fun _ hz => hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have hO := (OntoB.isOpen_OmF X x1).mem_nhds h0
  obtain ⟨hb0, -⟩ := cpt_zero_cell D ho hb
  obtain ⟨hc0, hc1⟩ := cpt_zero_cell D ho hc
  obtain ⟨S, hS, hSi⟩ := lintegral_ball_lt_top_of_localInverse
    (fun z => D.zOf (cpt X (rmul x1 b) z)) (fun z => D.zOf (cpt X (rmul x1 (invF X b)) z))
    (hop (rmul x1 b)) hb0 (hdiff _)
    (((hdiff _).differentiableAt ((hop _).mem_nhds hc0)).continuousAt) hc1
    (by
      filter_upwards [hO, (hop _).mem_nhds hc0] with z hz1 hz2
      exact zOf_zOf D ho
        (fun τ => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)
    (by
      filter_upwards [hO, (hop _).mem_nhds hb0] with z hz1 hz2
      exact zOf_zOf D ho
        (fun τ => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)
    (fun z => φ (cpt X x1 z)) (fun z => φ (cpt X (rmul x1 b) z))
    (by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := D.split _ hw.1 hw.2
      show φ (cpt X x1 _) = φ _
      conv_rhs => rw [h3]
      exact (hφ _ h1 _ h2).symm) hρ hint
  have hdc : ContinuousAt (densF X x1) 0 := (OntoB.densF_continuousOn (X := X) (x0 := x1)).continuousAt hO
  set C : ℝ := densF X x1 0 + 1 with hC
  have hbd : ∀ᶠ z in 𝓝 (0 : V (nd X)), densF X x1 z < C := hdc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), z ∈ OmF X x1 ∧ z ∈ S ∧ densF X x1 z < C := by
    filter_upwards [hO, hS, hbd] with w a b c
    exact ⟨a, b, c⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨δ, hδ, fun z hz => (hB z hz).1, ?_⟩
  have hle : (muF X x1).restrict (Metric.ball 0 δ) ≤ ENNReal.ofReal C • volume.restrict S := by
    unfold muF
    rw [restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
    calc (volume.restrict (Metric.ball 0 δ ∩ OmF X x1)).withDensity
          (fun z => ENNReal.ofReal (densF X x1 z))
        ≤ (volume.restrict (Metric.ball 0 δ ∩ OmF X x1)).withDensity (fun _ => ENNReal.ofReal C) := by
          refine withDensity_mono ?_
          filter_upwards [ae_restrict_mem
            (measurableSet_ball.inter (OntoB.isOpen_OmF X x1).measurableSet)] with z hz
          exact ENNReal.ofReal_le_ofReal (hB z hz.1).2.2.le
      _ = ENNReal.ofReal C • volume.restrict (Metric.ball 0 δ ∩ OmF X x1) := withDensity_const _
      _ ≤ ENNReal.ofReal C • volume.restrict S := by
          refine Measure.le_iff'.2 fun s => ?_
          simp only [Measure.smul_apply, smul_eq_mul]
          have hsub : Metric.ball 0 δ ∩ OmF X x1 ⊆ S := fun z hz => (hB z hz.1).2.1
          exact mul_le_mul_right (Measure.le_iff'.1 (Measure.restrict_mono_set _ hsub) s) _
  refine lt_of_le_of_lt (lintegral_mono' hle le_rfl) ?_
  rw [lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSi

end GlobalTheory.ChartChange
end
