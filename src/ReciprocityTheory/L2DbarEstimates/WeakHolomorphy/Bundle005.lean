module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle004
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle003
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegIndep
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem reg_ball {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω) (hu : Integrable u)
    (hw : WeakHolo Ω u) (c : V n) (r : ℝ) (hr : closedBall c (3 * r) ⊆ Ω) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball c r) ∧ u =ᵐ[volume.restrict (ball c r)] U := by
  by_cases hr0 : 0 < r
  · refine ⟨mollify n r u, fun x hx => ?_, ?_⟩
    · have hx' : closedBall x r ⊆ Ω := by
        refine (Metric.closedBall_subset_closedBall' ?_).trans hr
        rw [Metric.mem_ball] at hx; linarith
      exact (mollify_differentiableAt hΩ hu hw hr0 hx').differentiableWithinAt
    · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
      filter_upwards [mollify_tendsto_ae hu] with x hx hxb
      rw [Metric.mem_ball] at hxb
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mollify n t u x = mollify n r u x := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr0)] with t ht1 ht2
        have ht1' : 0 < t := ht1
        have ht2' : t < r := ht2
        refine mollify_indep hΩ hu hw ht1' hr0 ((Metric.closedBall_subset_closedBall' ?_).trans hr)
        linarith
      have h2 : Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (mollify n r u x)) :=
        tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
      exact tendsto_nhds_unique hx h2
  · have h0 : ball c r = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hr0)
    refine ⟨u, ?_, ?_⟩
    · rw [h0]; exact differentiableOn_empty
    · rw [h0, Measure.restrict_empty]

theorem reg : RegStatement := by
  intro n Ω u hΩ hw
  apply reg_glue hΩ
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hr0 : 0 < ε / 8 := by positivity
  have h5 : closedBall x (5 * (ε / 8)) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have h4 : ball x (4 * (ε / 8)) ⊆ closedBall x (5 * (ε / 8)) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have h4Ω : ball x (4 * (ε / 8)) ⊆ Ω := h4.trans h5
  set u' := (closedBall x (5 * (ε / 8))).indicator u with hu'def
  have hu' : Integrable u' := by
    rw [hu'def, integrable_indicator_iff measurableSet_closedBall]
    exact hw.1.integrableOn_compact_subset h5 (isCompact_closedBall _ _)
  have hw' : WeakHolo (ball x (4 * (ε / 8))) u' := by
    refine ⟨hu'.locallyIntegrable.locallyIntegrableOn _, fun g hg v => ?_⟩
    have hzero : ∀ z, z ∉ tsupport g → dbarDir g z v = 0 := by
      intro z hz
      have h0 : fderiv ℝ g z = 0 := by
        rw [(notMem_tsupport_iff_eventuallyEq.mp hz).fderiv_eq]; simp
      simp [dbarDir, h0]
    have hts : tsupport g ⊆ ball x (4 * (ε / 8)) := hg.2.2
    have hpt : ∀ z, u' z * dbarDir g z v = u z * dbarDir g z v := by
      intro z
      by_cases hz : z ∈ tsupport g
      · rw [hu'def, Set.indicator_of_mem (h4 (hts hz))]
      · simp [hzero z hz]
    have h1 := hw.2 g ⟨hg.1, hg.2.1, hts.trans h4Ω⟩ v
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts.trans h4Ω h))])] at h1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts h))])]
    simp_rw [hpt]
    exact h1
  obtain ⟨U, hU, hae⟩ := reg_ball (Ω := ball x (4 * (ε / 8))) Metric.isOpen_ball hu' hw' x (ε / 8)
    (Metric.closedBall_subset_ball (by linarith))
  refine ⟨ε / 8, hr0, (Metric.ball_subset_ball (by linarith)).trans h4Ω, U, hU, ?_⟩
  refine Filter.EventuallyEq.trans ?_ hae
  refine ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_)
  rw [hu'def, Set.indicator_of_mem (h4 (Metric.ball_subset_ball (by linarith) hz))]

end ReciprocityTheory.L2DbarEstimates.C
end

section

namespace ReciprocityTheory.L2DbarEstimates.C

open Metric Set Filter Topology Complex
open scoped ContDiff

theorem exists_clm_of_I {n : ℕ} (A : V n →L[ℝ] ℂ) (hA : ∀ w : V n, A (I • w) = I * A w) :
    ∃ g' : V n →L[ℂ] ℂ, g'.restrictScalars ℝ = A := by
  refine ⟨{ toFun := A, map_add' := A.map_add, map_smul' := fun c w => ?_, cont := A.continuous }, ?_⟩
  · simp only [RingHom.id_apply, smul_eq_mul]
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
      A.map_add, A.map_smul, A.map_smul, hA]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [Complex.real_smul]
    ring
  · exact ContinuousLinearMap.ext fun w => rfl

theorem holoDeriv : HoloDerivStatement := by
  intro n Ω f hΩ hf v x hx
  have hs : ContDiffOn ℝ ∞ f Ω := holoSmooth n Ω f hΩ hf
  have hxn : Ω ∈ 𝓝 x := hΩ.mem_nhds hx
  have hloc : ∀ᶠ y in 𝓝 x, ∀ u : V n, fderiv ℝ f y u = fderiv ℂ f y u := by
    filter_upwards [hxn] with y hy u
    rw [((hf y hy).differentiableAt (hΩ.mem_nhds hy)).fderiv_restrictScalars ℝ]
    rfl
  have hD2 : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hs).2.contDiffAt hxn
  have hDd : DifferentiableAt ℝ (fderiv ℝ f) x := hD2.differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    ((contDiffOn_infty.1 hs 2).contDiffAt hxn).isSymmSndFDerivAt (by simp)
  have hder : ∀ u : V n, HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) x := by
    intro u
    simpa using hDd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have hI : ∀ w : V n, fderiv ℝ (fderiv ℝ f) x v (I • w) = I * fderiv ℝ (fderiv ℝ f) x v w := by
    intro w
    have hev : (fun y => fderiv ℝ f y (I • w)) =ᶠ[𝓝 x] fun y => I * fderiv ℝ f y w := by
      filter_upwards [hloc] with y hy
      rw [hy, hy, map_smul, smul_eq_mul]
    have h2 : HasFDerivAt (fun y => I * fderiv ℝ f y w) (I • (fderiv ℝ (fderiv ℝ f) x).flip w) x :=
      (hder w).const_mul I
    have h3 := ((hder (I • w)).congr_of_eventuallyEq hev.symm).unique h2
    have h4 := congrArg (fun L : V n →L[ℝ] ℂ => L v) h3
    simpa using h4
  have hA : ∀ w : V n, (fderiv ℝ (fderiv ℝ f) x).flip v (I • w) =
      I * (fderiv ℝ (fderiv ℝ f) x).flip v w := by
    intro w
    simp only [ContinuousLinearMap.flip_apply]
    rw [hsymm (I • w) v, hI w, hsymm w v]
  obtain ⟨gC, hgC⟩ := exists_clm_of_I _ hA
  have hev2 : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x] fun y => fderiv ℝ f y v := by
    filter_upwards [hloc] with y hy
    exact (hy v).symm
  exact ((hasFDerivAt_of_restrictScalars ℝ (hder v) hgC).congr_of_eventuallyEq hev2).differentiableAt.differentiableWithinAt

end ReciprocityTheory.L2DbarEstimates.C
end
