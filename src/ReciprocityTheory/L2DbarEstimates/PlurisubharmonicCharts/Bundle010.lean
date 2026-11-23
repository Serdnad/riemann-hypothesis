module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle008
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxD
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003

@[expose] public section

section

open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

theorem cmpa_cHess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) :
    cHess n (h ∘ τ) x = (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).transpose * cHess n h (τ x) *
      (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj := by
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [cmpa_hess_comp hU hxU hτ hh j k]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem cmpa_det_jac (L : V n →L[ℂ] V n) :
    (Matrix.of fun l j => (L (bas n j)) l).det = L.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1

theorem cmpa_det_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) :
    (cHess n (h ∘ τ) x).det = (((‖(fderiv ℂ τ x).det‖ ^ 2 : ℝ)) : ℂ) * (cHess n h (τ x)).det := by
  rw [cmpa_cHess_comp hU hxU hτ hh, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hc : ((Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj).det =
      conj ((Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).det) :=
    (RingHom.map_det (starRingEnd ℂ) _).symm
  rw [hc, cmpa_det_jac, Complex.sq_norm, ← Complex.mul_conj]
  ring

theorem cmpa_wdb_log {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℂ 2 g y) (hy : g y ≠ 0) (k : Fin n) :
    wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) y = conj (fderiv ℂ g y (bas n k) / g y) := by
  have hgd : DifferentiableAt ℂ g y := hg.differentiableAt (by simp)
  have hgR : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) y := hgd.hasFDerivAt.restrictScalars ℝ
  have hN := hgR.norm_sq
  have hpos : ‖g y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have hL := hN.log hpos
  have hF := Complex.ofRealCLM.hasFDerivAt.comp y hL
  unfold wdb
  rw [show (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) =
    ⇑Complex.ofRealCLM ∘ fun v => Real.log (‖g v‖ ^ 2) from rfl, hF.fderiv]
  have hG : (g y).re * (g y).re + (g y).im * (g y).im ≠ 0 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm]; exact hpos
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, innerSL_apply_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, nsmul_eq_mul, Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp <;>
    ring

private theorem wd_conj_of_complex_differentiableAt_eq_zero {h : V n → ℂ} {y : V n} (hh : DifferentiableAt ℂ h y) (j : Fin n) :
    wd n j (fun v => (starRingEnd ℂ) (h v)) y = 0 := by
  have H := (hh.hasFDerivAt.restrictScalars ℝ).star
  have H2 : fderiv ℝ (fun v => (starRingEnd ℂ) (h v)) y =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ h y).restrictScalars ℝ) := H.fderiv
  simp only [wd, H2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  try simp only [Complex.I_sq]
  try ring

theorem cmpa_hess_log {g : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U) (hxU : x ∈ U)
    (hg : DifferentiableOn ℂ g U) (hne : ∀ v ∈ U, g v ≠ 0) (j k : Fin n) :
    wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x = 0 := by
  have hgs : ContDiffOn ℂ ∞ g U := contDiffOn_of_differentiableOn n g U hU hg
  have ev : wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun v => conj (fderiv ℂ g v (bas n k) / g v) := by
    filter_upwards [hU.mem_nhds hxU] with v hv
    exact cmpa_wdb_log ((contDiffOn_infty.1 hgs 2).contDiffAt (hU.mem_nhds hv)) (hne v hv) k
  have e1 : wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x =
      wd n j (fun v => conj (fderiv ℂ g v (bas n k) / g v)) x := by
    simp only [wd, ev.fderiv_eq]
  rw [e1]
  apply wd_conj_of_complex_differentiableAt_eq_zero
  have hD : ContDiffOn ℂ ∞ (fderiv ℂ g) U := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hgs).2
  have h1 := (((hD.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).clm_apply
    (differentiableAt_const (bas n k))).mul ((hg.differentiableAt (hU.mem_nhds hxU)).inv (hne x hxU))
  exact h1

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem mem_ovl {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) :
    A.chart j y ∈ ovl A.chart j i :=
  ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hi]⟩

theorem trans_contDiffAt {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source)
    (hi : y ∈ (A.chart i).source) :
    ContDiffAt ℂ 2 ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) :=
  ((A.trans_contDiffOn j i).contDiffAt ((A.isOpen_ovl j i).mem_nhds (A.mem_ovl hj hi))).of_le
    (by norm_cast)

theorem levi_transfer (la : La) (f : Y → ℝ) (hf : A.SmoothFn f) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt j (fun x => A.ph la j x + f x) y ξ =
      A.leviAt i (fun x => A.ph la i x + f x) y
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)).ofLp := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : ContDiffAt ℂ 2 Φ v0 := A.trans_contDiffAt hj hi
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set h : V n → ℝ := fun u => A.ph la i ((A.chart i).symm u) + f ((A.chart i).symm u)
  have hh : ContDiffAt ℝ 2 h (Φ v0) := by
    rw [hΦv]
    exact (((A.smooth_ph la i).add (hf i)).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))).of_le (by norm_cast)
  set G := A.g la j i ∘ (A.chart j).symm
  have hG : ContDiffAt ℂ 2 G v0 :=
    contDiffAt_two_of_holo (A.isOpen_ovl j i) (A.holo_g la j i) hv0
  have hG0 : G v0 ≠ 0 := by
    simp only [G, Function.comp, v0, (A.chart j).left_inv hj]; exact A.g_ne la j i y hj hi
  set u2 : Fin 2 → V n → ℝ := ![fun v => h (Φ v), fun v => Real.log (Complex.normSq (G v))]
  have hu2 : ∀ k, ContDiffAt ℝ 2 (u2 k) v0 := by
    intro k; fin_cases k
    · exact hh.comp v0 (hΦ.restrict_scalars ℝ)
    · exact (contDiffAt_normSq_comp hG).log (Complex.normSq_pos.2 hG0).ne'
  have hev : (fun v => ((A.ph la j ((A.chart j).symm v) + f ((A.chart j).symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((∑ k, u2 k v : ℝ) : ℂ) := by
    filter_upwards [hO] with v hv
    have hxj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hxi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    have hsy : (A.chart i).symm (Φ v) = (A.chart j).symm v := by
      simp only [Φ, Function.comp]; exact (A.chart i).left_inv hxi
    have hne : ‖A.g la j i ((A.chart j).symm v)‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la j i _ hxj hxi)
    simp only [Fin.sum_univ_two, u2, Matrix.cons_val_zero, Matrix.cons_val_one, h, hsy, G,
      Function.comp, A.ph_trans la j i _ hxj hxi, Complex.normSq_eq_norm_sq]
    push_cast; ring
  unfold leviAt
  rw [leviV_congr hev, leviV_ofReal_sum hu2, Fin.sum_univ_two]
  have e1 : u2 0 = fun v => h (Φ v) := rfl
  have e2 : u2 1 = fun v => Real.log (Complex.normSq (G v)) := rfl
  rw [e1, e2, leviV_log_normSq hG hG0, add_zero]
  have hc := leviV_comp (f := fun u => ((h u : ℝ) : ℂ)) (Φ := Φ) (y := v0) ?_ hΦ ξ
  · rw [show (fun v => ((h (Φ v) : ℝ) : ℂ)) = (fun u => ((h u : ℝ) : ℂ)) ∘ Φ from rfl, hc, hΦv]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hh

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end
