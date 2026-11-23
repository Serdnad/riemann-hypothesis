module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle006
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgA

open Topology Filter
open ReciprocityTheory.L2DbarEstimates

variable {n : ℕ}

theorem grad_le_of_minorant (rh Ψ : V n → ℝ) (v0 : V n) (C : ℝ) (hC : 0 < C)
    (hΨ0 : 0 < Ψ v0) (hrh : ContDiffAt ℝ 2 rh v0) (hΨ : ContDiffAt ℝ 2 Ψ v0) (ξ : Fin n → ℂ)
    (hL : (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re ≤ 0)
    (hle : ∀ᶠ v in 𝓝 v0, -C * Real.log (Ψ v) ≤ rh v) (heq : rh v0 = -C * Real.log (Ψ v0)) :
    Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) ≤
      C * (leviV n (fun y => (rh y : ℂ)) v0 ξ).re := by
  set k : ℝ → ℝ := fun t => -C * Real.log t with hkdef
  set ψ : V n → ℝ := fun y => k (Ψ y) with hψdef
  have hk : ContDiffAt ℝ 2 k (Ψ v0) := contDiffAt_const.mul (Real.contDiffAt_log.2 hΨ0.ne')
  have hψ : ContDiffAt ℝ 2 ψ v0 := hk.comp v0 hΨ
  have hrd : DifferentiableAt ℝ rh v0 := hrh.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ ψ v0 := hψ.differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ v0 := hΨ.differentiableAt (by simp)
  have hkd : DifferentiableAt ℝ k (Ψ v0) := hk.differentiableAt (by simp)
  have hmin : IsLocalMin (fun y => rh y - ψ y) v0 := by
    filter_upwards [hle] with v hv
    simp only [hψdef, hkdef]
    linarith
  have hfd : fderiv ℝ rh v0 = fderiv ℝ ψ v0 := by
    have h := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hrd hψd] at h
    exact sub_eq_zero.1 h
  have hwd : ∀ j, wd n j (fun y => (rh y : ℂ)) v0 = wd n j (fun y => (ψ y : ℂ)) v0 := by
    intro j
    simp only [wd, fderiv_ofReal_apply hrd, fderiv_ofReal_apply hψd, hfd]
  have hdk : deriv k = fun t => -C * t⁻¹ := by
    funext t
    simp only [hkdef]
    rw [deriv_const_mul_field', Real.deriv_log']
  have hddk : deriv (deriv k) = fun t => C * (t ^ 2)⁻¹ := by
    rw [hdk]
    funext t
    rw [deriv_const_mul_field']
    show -C * deriv (fun x : ℝ => x⁻¹) t = _
    rw [deriv_inv]
    ring
  have hwdψ : ∀ j, wd n j (fun y => (ψ y : ℂ)) v0 =
      (((-C * (Ψ v0)⁻¹ : ℝ)) : ℂ) * wd n j (fun y => (Ψ y : ℂ)) v0 := by
    intro j
    rw [show (fun y => (ψ y : ℂ)) = fun y => (k (Ψ y) : ℂ) from rfl, wd_ofReal_comp hkd hΨd, hdk]
  have hchain := leviChain n k Ψ v0 ξ hΨ hk
  rw [hddk, hdk] at hchain

  have hmax : IsLocalMax (fun y => ψ y + (-1) * rh y) v0 := by
    have := hmin.neg
    refine this.congr ?_
    filter_upwards with y
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ψ y + (-1) * rh y) v0 := hψ.add (contDiffAt_const.mul hrh)
  have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcd hmax ξ
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hψ (contDiffAt_const.mul hrh) ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hrh ξ] at h2
  have hψL : leviV n (fun y => (ψ y : ℂ)) v0 ξ = leviV n (fun y => (k (Ψ y) : ℂ)) v0 ξ := rfl
  rw [hψL, hchain] at h2
  set N := Complex.normSq (∑ j, wd n j (fun y => (Ψ y : ℂ)) v0 * ξ j) with hN
  set LΨ := (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re
  set Lr := (leviV n (fun y => (rh y : ℂ)) v0 ξ).re
  have h3 : (-C * (Ψ v0)⁻¹) * LΨ + C * ((Ψ v0) ^ 2)⁻¹ * N ≤ Lr := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.neg_re, Complex.one_re, neg_mul, one_mul] at h2
    linarith
  have hlhs : Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) =
      (C * (Ψ v0)⁻¹) ^ 2 * N := by
    simp only [hwd, hwdψ, mul_assoc, ← Finset.mul_sum, Complex.normSq_mul, Complex.normSq_ofReal, hN]
    ring
  rw [hlhs]
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hi : 0 < (Ψ v0)⁻¹ := inv_pos.2 hΨ0
  have h4 : 0 ≤ (-C * (Ψ v0)⁻¹) * LΨ := by
    have : -C * (Ψ v0)⁻¹ ≤ 0 := by nlinarith
    nlinarith
  have h5 : (C * (Ψ v0)⁻¹) ^ 2 * N = C * (C * ((Ψ v0) ^ 2)⁻¹ * N) := by
    ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left (by linarith) hC.le

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgB

open Matrix
open scoped ComplexOrder Matrix
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

open scoped MatrixOrder in
theorem exists_factor {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosSemidef) :
    ∃ y : Matrix (Fin m) (Fin m) ℂ, M = yᴴ * y := by
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  exact ⟨y, hy⟩

theorem amgm_psd {m : ℕ} (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosSemidef) :
    P.det.re ^ ((m : ℝ)⁻¹) ≤ P.trace.re / m := by
  have hH := hP.1
  have hd : P.det.re = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  have ht : P.trace.re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]
    simp [← Complex.ofReal_sum]
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hP.eigenvalues_nonneg i
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin m))
    (fun _ => (m : ℝ)⁻¹) (fun i => hH.eigenvalues i) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]; field_simp) (fun i _ => hnn i)
  rw [hd, ht, ← Real.finsetProd_rpow _ _ (fun i _ => hnn i)]
  calc ∏ i, hH.eigenvalues i ^ ((m : ℝ)⁻¹) ≤ ∑ i, (m : ℝ)⁻¹ * hH.eigenvalues i := h
    _ = (∑ i, hH.eigenvalues i) / m := by rw [← Finset.mul_sum]; field_simp

theorem amgm {m : ℕ} (hm : 0 < m) {A A0 : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef)
    (hA0 : A0.PosDef) :
    A.det.re ^ ((m : ℝ)⁻¹) ≤ A0.det.re ^ ((m : ℝ)⁻¹) * ((A * A0⁻¹).trace.re / m) := by
  have hM : (A0⁻¹).PosDef := hA0.inv
  obtain ⟨y, hy⟩ := exists_factor hM.posSemidef
  have hP : (y * A * yᴴ).PosSemidef := hA.posSemidef.mul_mul_conjTranspose_same y
  have htr : (y * A * yᴴ).trace = (A * A0⁻¹).trace := by
    rw [hy, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  obtain ⟨ha, hai⟩ := det_re_pos_im hA
  obtain ⟨hb, hbi⟩ := det_re_pos_im hA0
  have hdet : (y * A * yᴴ).det.re = A.det.re * (A0.det.re)⁻¹ := by
    have e1 : (y * A * yᴴ).det = A.det * (A0⁻¹).det := by
      rw [hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]; ring
    rw [e1, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_eq_ofReal hA, det_eq_ofReal hA0]
    simp only [Complex.ofReal_re]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := amgm_psd hm hP
  rw [hdet, htr, Real.mul_rpow ha.le (inv_nonneg.2 hb.le), Real.inv_rpow hb.le] at h
  have hc : 0 < A0.det.re ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
  calc A.det.re ^ ((m : ℝ)⁻¹) = A0.det.re ^ ((m : ℝ)⁻¹) *
        (A.det.re ^ ((m : ℝ)⁻¹) * (A0.det.re ^ ((m : ℝ)⁻¹))⁻¹) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc.le

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace BigC

variable {r : ℕ}

private theorem norm_dmin_succ_div_castSucc_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin r) :
    0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
  have h := (hx τ).2
  have h1 := h i.succ
  have h2 := h i.castSucc
  refine norm_pos_iff.mpr (div_ne_zero ?_ ?_)
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro h0
    rw [h0] at h2
    simp at h2

private theorem nfac_pos_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    0 < X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _

private theorem phla_eq_sum_log_norm_dmin_ratio (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    phla X la x = ∑ τ, ∑ i : Fin r,
      (la τ i : ℝ) * Real.log ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
  unfold phla Data.nfac
  rw [Real.log_prod (fun τ _ =>
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (norm_dmin_succ_div_castSucc_pos X hx τ i)]
  ring

theorem phla_sub (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    phla X (la - la') x = phla X la x - phla X la' x := by
  rw [phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

theorem phla_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (k : ℕ) (la : Wt X.Ψ r) :
    phla X (k • la) x = k * phla X la x := by
  rw [phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  ring

theorem log_pnorm_sq (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hP : P x ≠ 0) :
    Real.log (X.pnorm la P x ^ 2) = Real.log (Complex.normSq (P x)) - phla X la x := by
  have hN := nfac_pos_of_mem_dom X hx la
  have hp : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have hn2 : Complex.normSq (P x) = ‖P x‖ ^ 2 := by
    first
      | exact Complex.normSq_eq_norm_sq _
      | exact (Complex.sq_norm _).symm
      | simp [Complex.normSq_eq_abs]
  rw [hp, mul_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hP)) (pow_ne_zero _ hN.ne'), hn2,
    Real.log_pow, Real.log_pow, phla]
  ring

end BigC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ortho_holds : OrthoStatement (E := E) := by
  intro r X x hx

  have hBor := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X := X) hx
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x),
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X := X) hx,
    fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ :
      Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    haveI : Invertible (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
      Matrix.invertibleOfIsUnitDet _ hdet
    have hM : (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).BlockTriangular id :=
      fun i j hij => (hBor τ).2 i j hij
    have hMi := Matrix.blockTriangular_inv_of_blockTriangular hM
    refine ⟨?_, fun a c hca => hMi hca⟩
    show ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).ne_zero
  · funext τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    show ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat x τ *
      ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
      (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
