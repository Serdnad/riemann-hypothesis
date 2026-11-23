module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff

noncomputable section

theorem gc_wdb_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wdb n j (g ∘ F) v = ∑ a, wdb d a g (F v) * (starRingEnd ℂ) (J (bas n j) a) := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wdb, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination ((D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 -
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem gc_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wd n j (g ∘ F) v = ∑ a, wd d a g (F v) * J (bas n j) a := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wd, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination (-(D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 +
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem gc_toLp_apply (n d : ℕ) (J : V n →L[ℂ] V d) (ξ : Fin n → ℂ) (b : Fin d) :
    J (WithLp.toLp 2 ξ) b = ∑ j, ξ j * J (bas n j) b := by
  have h : WithLp.toLp 2 ξ = ∑ j, ξ j • bas n j := by
    ext k
    simp [bas, Pi.single_apply]

  rw [h, map_sum]
  simp [map_smul]

theorem gc_sum_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (ξ : Fin n → ℂ) :
    ∑ j, wd n j (g ∘ F) v * ξ j = ∑ a, wd d a g (F v) * J (WithLp.toLp 2 ξ) a := by
  simp only [gc_wd_comp n d g F J v hg hF, gc_toLp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_four_indices_comm (n d : ℕ) (f : Fin n → Fin n → Fin d → Fin d → ℂ) :
    ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := by
  calc ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ j, ∑ k, ∑ b, ∑ a, f j k a b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ k, ∑ a, f j k a b := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ a, f j k a b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ a, ∑ k, f j k a b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem gc_leviV_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v))
    (ξ : Fin n → ℂ) :
    leviV n (g ∘ F) v ξ = leviV d g (F v) (fun b => fderiv ℂ F v (WithLp.toLp 2 ξ) b) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  have step : ∀ j k, wd n j (wdb n k (g ∘ F)) v = ∑ a, ∑ b,
      wd d b (wdb d a g) (F v) * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
    intro j k
    rw [wd_congr n j _ _ v (hwdb k),
      fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
        (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
      mul_zero, add_zero]
    have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
    rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  unfold leviV

  simp only [step, gc_toLp_apply, Finset.sum_mul, map_sum, map_mul, Finset.mul_sum]
  rw [sum_four_indices_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Wpsi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact if x ∈ X.dom then ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) else 0

theorem metricW_of (hR : NfacRmulStatement (E := E)) (hLa : NfacLactStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (ψ : Frame X.Ψ r → ℝ) (hψ : IsInvFn X ψ)
    (hψs : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0))
    (hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) :
    IsMetricW X la (Wpsi X la ψ) ∧ WLower X la (Wpsi X la ψ) := by
  classical

  have hlact1 : ∀ y : Frame X.Ψ r, lact (1 : GL (Fin r) E) y = y := by
    intro y; funext τ a c
    simp [lact, mat]
  have hψr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    have h := hψ 1 X.Γ.one_mem x hx b hb
    rwa [hlact1] at h
  have hψl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ψ (lact γ x) = ψ x := by
    intro γ hγ x hx
    have h := hψ γ hγ x hx (ExtFPf.oneF X) (ExtFPf.oneF_mem (X := X))
    rwa [ExtFPf.rmul_oneF] at h

  have hnpos : ∀ x ∈ X.dom, 0 < X.nfac la x := by
    intro x hx
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _)
      (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _))
  have hopen : IsOpen X.dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom (X := X)

  have hphr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      0 < ‖bchar la b‖ ∧ phla X la (rmul x b) = phla X la x + 2 * Real.log ‖bchar la b‖ := by
    intro x hx b hb
    have hn := hnpos x hx
    have h1 := hnpos (rmul x b) (OntoS.dom_rmul (X := X) hx hb)
    rw [hR r X la x hx b hb] at h1
    have hinv : 0 < ‖bchar la b‖⁻¹ := by
      by_contra hc
      push_neg at hc
      nlinarith
    refine ⟨inv_pos.mp hinv, ?_⟩
    unfold phla
    rw [hR r X la x hx b hb, Real.log_mul hinv.ne' hn.ne', Real.log_inv]
    ring
  have hphl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phla X la (lact γ x) = phla X la x := by
    intro γ hγ x hx
    unfold phla
    rw [hLa r X la γ hγ x hx]

  have hψc : ContinuousOn ψ X.dom := by
    intro x hx
    obtain ⟨x1, ho, b, hb, hxe⟩ := hO r X x hx
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, hcomp⟩ := hLU r X x1 ho
    have hn0 : nmat X (0 : V (nd X)) = ExtFPf.oneF X := by
      funext τ a c
      simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
      split_ifs <;> first | rfl | (exfalso; subst_vars; exact lt_irrefl _ ‹_ < _›) | simp_all
    have hc0 : cpt X x1 0 = x1 := by
      unfold cpt
      rw [hn0, ExtFPf.rmul_oneF]
    have hΔx : Δ x ≠ 0 := by
      have h := (hcomp 0 (zero_mem_OmF (X := X) x1 ho) b hb).1
      rwa [hc0, ← hxe] at h
    have hUo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      hopen.inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hmap : Set.MapsTo zOf {y | y ∈ X.dom ∧ Δ y ≠ 0} (OmF X x1) :=
      fun y hy => (hdec y hy.1 hy.2).1
    have hcomp' : ContinuousOn ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      (hψs x1 ho).continuousOn.comp hz.continuousOn hmap
    have heq : Set.EqOn ψ ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} := by
      intro y hy
      obtain ⟨hzy, hby, hye⟩ := hdec y hy.1 hy.2
      have hmem : cpt X x1 (zOf y) ∈ X.dom := hzy
      show ψ y = ψ (cpt X x1 (zOf y))
      exact (congrArg ψ hye).trans (hψr _ hmem _ hby)
    exact ((hcomp'.congr heq).continuousAt (hUo.mem_nhds ⟨hx, hΔx⟩)).continuousWithinAt
  have hphc : ContinuousOn (phla X la) X.dom := by
    show ContinuousOn (fun x => -2 * Real.log (X.nfac la x)) X.dom
    exact continuousOn_const.mul
      ((ExtFPf.nfac_contOn (X := X) la).log fun x hx => (hnpos x hx).ne')
  have hcont : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (hphc.add hψc).neg)
  have hW : ∀ x ∈ X.dom, Wpsi X la ψ x = ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) := by
    intro x hx
    simp [Wpsi, hx]
  have hWeq : Wpsi X la ψ = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ X.dom <;> simp [Wpsi, Set.piecewise, hx]
  unfold IsMetricW WLower
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hWeq]
    exact ContinuousOn.measurable_piecewise hcont continuousOn_const hopen.measurableSet
  · intro x hx b hb
    obtain ⟨hB, hph⟩ := hphr x hx b hb
    rw [hW _ (OntoS.dom_rmul (X := X) hx hb), hW x hx, hph, hψr x hx b hb,
      ← ENNReal.ofReal_div_of_pos (pow_pos hB 2)]
    congr 1
    rw [show -(phla X la x + 2 * Real.log ‖bchar la b‖ + ψ x)
        = -(phla X la x + ψ x) - Real.log (‖bchar la b‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_sub, Real.exp_log (pow_pos hB 2)]
  · intro γ hγ x hx
    rw [hW _ (OntoS.dom_lact (X := X) hγ hx), hW x hx, hphl γ hγ x hx, hψl γ hγ x hx]
  · obtain ⟨C, hC⟩ := hψb
    refine ⟨Real.exp (-C), Real.exp_pos _, fun x hx => ?_⟩
    rw [hW x hx, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hC x hx]))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

theorem diffOn_det {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) : DifferentiableOn ℂ (fun x => (m x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  have hp : ∀ σ : Equiv.Perm (Fin k), DifferentiableOn ℂ (fun x => ∏ i, m x (σ i) i) s := by
    intro σ
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => simp [differentiableOn_const]
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hm (σ a) a).mul ih
  fun_prop

theorem diffOn_inv {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) (hd : ∀ x ∈ s, (m x).det ≠ 0) :
    ∀ i j, DifferentiableOn ℂ (fun x => (m x)⁻¹ i j) s := by
  intro i j
  have hadj : DifferentiableOn ℂ (fun x => (m x).adjugate i j) s := by
    simp only [Matrix.adjugate_apply]
    refine diffOn_det (fun x => (m x).updateRow j (Pi.single i 1)) ?_
    intro a b
    by_cases h : a = j
    · simp [Matrix.updateRow_apply, h, differentiableOn_const]
    · simpa [Matrix.updateRow_apply, h] using hm a b
  have hinv : DifferentiableOn ℂ (fun x => ((m x).det)⁻¹) s := (diffOn_det m hm).inv hd
  refine (hinv.mul hadj).congr ?_
  intro x _
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

theorem Mx_diff (τ : X.Ψ) (a c : Fin r) : Differentiable ℂ (fun x => Mx X x0 x τ a c) := by
  simp only [Mx, Matrix.mul_apply, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  first
    | fun_prop
    | exact Differentiable.sum fun b _ => (differentiable_const _).mul
        ((differentiable_apply c).comp ((differentiable_apply b).comp (differentiable_apply τ)))

theorem Delta_diff : Differentiable ℂ (DeltaF X x0) := by
  have hdet : ∀ τ (k : Fin (r + 1)), Differentiable ℂ (fun x => lminor (Mx X x0 x τ) k) := by
    intro τ k
    rw [← differentiableOn_univ]
    exact diffOn_det (s := Set.univ)
      (fun x => (Mx X x0 x τ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt)))
      (fun i j => (Mx_diff τ _ _).differentiableOn)
  show Differentiable ℂ (fun x => ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k)
  fun_prop

def cellL (X : Data E r) (x0 : Frame X.Ψ r) : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ DeltaF X x0 x ≠ 0}

theorem Lm_diff (τ : X.Ψ) (i k : Fin r) :
    DifferentiableOn ℂ (fun x => Lm (Mx X x0 x τ) i k) (cellL X x0) := by
  have hl : ∀ x ∈ cellL X x0, ∀ k : Fin (r + 1), lminor (Mx X x0 x τ) k ≠ 0 := by
    intro x hx k
    have h1 : DeltaF X x0 x ≠ 0 := hx.2
    unfold DeltaF at h1
    exact Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp h1 τ (Finset.mem_univ _)) k
      (Finset.mem_univ _)
  by_cases h1 : (k : ℕ) < i
  · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte]
    have hinv : ∀ a b, DifferentiableOn ℂ (fun x => (lb (Mx X x0 x τ) i)⁻¹ a b) (cellL X x0) :=
      diffOn_inv (fun x => lb (Mx X x0 x τ) i) (fun a b => (Mx_diff τ _ _).differentiableOn)
        (fun x hx => by rw [det_lb]; exact hl x hx _)
    have hM : ∀ a b, DifferentiableOn ℂ (fun x => Mx X x0 x τ a b) (cellL X x0) :=
      fun a b => (Mx_diff τ a b).differentiableOn
    simp only [wv, Matrix.vecMul, dotProduct]
    refine DifferentiableOn.fun_neg ?_
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact (hM i _).mul (hinv j ⟨k, h1⟩)
  · by_cases h2 : k = i
    · subst h2
      simp only [Lm, Matrix.of_apply, lt_irrefl, ↓reduceDIte, ↓reduceIte]
      fun_prop
    · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte, h2, ↓reduceIte]
      fun_prop

theorem nF_diff (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => nF X x0 x τ a c) (cellL X x0) :=
  diffOn_inv (fun x => Lm (Mx X x0 x τ)) (fun i k => Lm_diff τ i k)
    (fun x _ => by rw [Lm_det]; exact one_ne_zero) a c

theorem bF_diff (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => bF X x0 x τ a c) (cellL X x0) := by
  simp only [bF, Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun b _ => (Lm_diff τ a b).mul (Mx_diff τ b c).differentiableOn

theorem bF_diffOn : DifferentiableOn ℂ (bF X x0) (cellL X x0) := by
  rw [differentiableOn_pi]
  intro τ
  rw [differentiableOn_pi]
  intro a
  rw [differentiableOn_pi]
  intro c
  exact bF_diff τ a c

theorem zF_diffOn : DifferentiableOn ℂ (zF X x0) (cellL X x0) := by
  rw [differentiableOn_euclidean]
  intro k
  simp only [zF, PiLp.toLp_apply]
  exact nF_diff _ _ _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end
