module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle001
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

variable {n : ℕ}

noncomputable def bumpProf (t s : ℝ) : ℝ := Real.smoothTransition (1 - 4 * (s / t) ^ 2)

noncomputable def mollConst (n : ℕ) : ℝ := (∫ z : V n, bumpProf 1 ‖z‖)⁻¹

noncomputable def mollProf (n : ℕ) (t s : ℝ) : ℝ := mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t s

noncomputable def moll (n : ℕ) (t : ℝ) (z : V n) : ℝ := mollProf n t ‖z‖

noncomputable def mollify (n : ℕ) (t : ℝ) (u : V n → ℂ) (x : V n) : ℂ :=
  ∫ y, (moll n t (x - y) : ℂ) * u y

theorem finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

theorem bumpProf_scale {t : ℝ} (ht : 0 < t) (z : V n) : bumpProf t ‖z‖ = bumpProf 1 ‖t⁻¹ • z‖ := by
  simp only [bumpProf, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, div_one]
  congr 1
  ring

theorem integral_bumpProf {t : ℝ} (ht : 0 < t) :
    ∫ z : V n, bumpProf t ‖z‖ = t ^ (2 * n) * ∫ z : V n, bumpProf 1 ‖z‖ := by
  simp_rw [bumpProf_scale ht]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z : V n => bumpProf 1 ‖z‖) ht.le,
    finrank_V, smul_eq_mul]

private lemma bumpProf_eq_zero_of_half_lt {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) : bumpProf t s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 1 / 2 < s / t := by rw [lt_div_iff₀ ht]; linarith
  nlinarith

private lemma continuous_bumpProf_norm (n : ℕ) (t : ℝ) : Continuous (fun z : V n => bumpProf t ‖z‖) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem integral_bumpProf_one_pos (n : ℕ) : 0 < ∫ z : V n, bumpProf 1 ‖z‖ := by
  have hcs : HasCompactSupport (fun z : V n => bumpProf 1 ‖z‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V n) (1 / 2)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact bumpProf_eq_zero_of_half_lt one_pos hz
  refine (continuous_bumpProf_norm n 1).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun z => Real.smoothTransition.nonneg _) (x := 0) ?_
  simp [bumpProf]

theorem mollConst_nonneg (n : ℕ) : 0 ≤ mollConst n := by
  unfold mollConst
  exact inv_nonneg.mpr (integral_nonneg fun z => Real.smoothTransition.nonneg _)

theorem moll_nonneg (n : ℕ) (t : ℝ) (z : V n) : 0 ≤ moll n t z := by
  have h : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  exact mul_nonneg (mul_nonneg (mollConst_nonneg n) (inv_nonneg.mpr h)) (Real.smoothTransition.nonneg _)

theorem moll_contDiff (n : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (moll n t) := by
  have h : moll n t = fun z => mollConst n * (t ^ (2 * n))⁻¹ *
      Real.smoothTransition (1 - 4 * (‖z‖ ^ 2 / t ^ 2)) := by
    funext z
    simp only [moll, mollProf, bumpProf, div_pow]
  rw [h]
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_norm_sq ℂ).div_const _))))

theorem moll_tsupport (n : ℕ) {t : ℝ} (ht : 0 < t) : tsupport (moll n t) ⊆ closedBall 0 (t / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hnot
  rw [mem_closedBall, dist_zero_right, not_le] at hnot
  apply hz
  simp only [moll, mollProf, bumpProf_eq_zero_of_half_lt ht hnot, mul_zero]

theorem moll_hasCompactSupport (n : ℕ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (moll n t) := by
  exact (isCompact_closedBall (0 : V n) (t / 2)).of_isClosed_subset (isClosed_tsupport _)
    (moll_tsupport n ht)

theorem moll_integral (n : ℕ) {t : ℝ} (ht : 0 < t) : ∫ z : V n, moll n t z = 1 := by
  simp only [moll, mollProf]
  rw [integral_const_mul, integral_bumpProf ht, mollConst]
  have h1 := integral_bumpProf_one_pos n
  have h2 : t ^ (2 * n) ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp

theorem moll_le (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ z : V n, moll n t z ≤ C / volume.real (ball (0 : V n) t) := by
  refine ⟨mollConst n * volume.real (ball (0 : V n) 1), fun t ht z => ?_⟩
  have hv : 0 < volume.real (ball (0 : V n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : V n) one_pos).ne' measure_ball_lt_top.ne
  have hball : volume.real (ball (0 : V n) t) = t ^ (2 * n) * volume.real (ball (0 : V n) 1) := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume (0 : V n) ht, finrank_V,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos ht _).le]
  rw [hball, mul_div_mul_right _ _ hv.ne']
  have htp : 0 < t ^ (2 * n) := pow_pos ht _
  have hb : bumpProf t ‖z‖ ≤ 1 := Real.smoothTransition.le_one _
  have hc := mollConst_nonneg n
  simp only [moll, mollProf]
  calc mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t ‖z‖
      ≤ mollConst n * (t ^ (2 * n))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hc (inv_nonneg.mpr htp.le))
    _ = mollConst n / t ^ (2 * n) := by ring

end ReciprocityTheory.L2DbarEstimates.C
end

section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem measurePreserving_smul_unit {n : ℕ} (a : ℂ) (ha : ‖a‖ = 1) :
    MeasurePreserving (fun z : V n => a • z) volume volume := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let L : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) a ha0).restrictScalars ℝ
      norm_map' := fun z => by simp [norm_smul, ha] }
  have hL : (fun z : V n => a • z) = L := by
    funext z
    rfl
  rw [hL]
  exact L.measurePreserving

theorem circle_mean {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (c + Complex.exp ((θ : ℂ) * I) • w) =
      ((2 * Real.pi : ℝ) : ℂ) * u c := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hρ1 : 1 < R / ‖w‖ := by
    rw [lt_div_iff₀ hwpos]
    linarith
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.ball 0 (R / ‖w‖)) := by
    intro ζ hζ
    have hmem : c + ζ • w ∈ ball c R := by
      rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hwpos] at hζ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact hζ
    have h1 : DifferentiableAt ℂ u (c + ζ • w) := hu.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => c + ζ • w) ζ :=
      (differentiableAt_id.smul_const w).const_add c
    exact (h1.comp ζ h2).differentiableWithinAt
  have hcl : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.closedBall 0 1) :=
    hg.mono (Metric.closedBall_subset_ball hρ1)
  have key := hcl.circleIntegral_sub_inv_smul (w := 0) (by simp)
  simp only [circleIntegral, deriv_circleMap, sub_zero, smul_eq_mul, zero_smul, add_zero] at key
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp ((θ : ℂ) * I) := by
    intro θ
    simp [circleMap]
  have h3 : ∀ θ : ℝ, circleMap 0 1 θ * I * ((circleMap 0 1 θ)⁻¹ * u (c + circleMap 0 1 θ • w)) =
      I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by
    intro θ
    have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    rw [hcm θ] at hne ⊢
    calc Complex.exp ((θ : ℂ) * I) * I * ((Complex.exp ((θ : ℂ) * I))⁻¹ * u (c + Complex.exp ((θ : ℂ) * I) • w))
        = I * u (c + Complex.exp ((θ : ℂ) * I) • w) * (Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹) := by ring
      _ = I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by rw [mul_inv_cancel₀ hne, mul_one]
  simp only [h3, intervalIntegral.integral_const_mul] at key
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [key]
  push_cast
  ring

theorem circle_mean_sq {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖u (c + Complex.exp ((θ : ℂ) * I) • w)‖ₑ ^ 2 := by
  have hmem : ∀ θ : ℝ, c + Complex.exp ((θ : ℂ) * I) • w ∈ ball c R := by
    intro θ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hw
  set F : ℝ → ℂ := fun θ => u (c + Complex.exp ((θ : ℂ) * I) • w) with hF
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    have h1 := (hu.differentiableAt (isOpen_ball.mem_nhds (hmem θ))).continuousAt
    have h2 : Continuous fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w := by fun_prop
    show ContinuousAt (u ∘ fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) θ
    exact ContinuousAt.comp (f := fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) (x := θ) h1
      h2.continuousAt
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hI : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ = ((2 * Real.pi : ℝ) : ℂ) * u c := by
    rw [← intervalIntegral.integral_of_le hpi]
    exact circle_mean hu hw
  have hint : IntegrableOn F (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun θ => ‖F θ‖ ^ 2) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    ((hcont.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcr : Continuous fun θ => (F θ * (starRingEnd ℂ) (u c)).re :=
    Complex.continuous_re.comp (hcont.mul continuous_const)
  have hint3 : IntegrableOn (fun θ => (F θ * (starRingEnd ℂ) (u c)).re) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcr.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpt : ∀ θ, 2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2 ≤ ‖F θ‖ ^ 2 := by
    intro θ
    have h := Complex.normSq_nonneg (F θ - u c)
    rw [Complex.normSq_sub] at h
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  have hre : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
      2 * Real.pi * ‖u c‖ ^ 2 := by
    have h1 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
        (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ * (starRingEnd ℂ) (u c)).re :=
      integral_re (hint.mul_const _)
    rw [h1, integral_mul_const, hI, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hreal : ‖u c‖ ^ 2 * (2 * Real.pi) ≤ ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 := by
    have h : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2) ≤
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 :=
      integral_mono ((hint3.const_mul 2).sub (integrable_const (‖u c‖ ^ 2))) hint2 hpt
    rw [integral_sub (hint3.const_mul 2) (integrable_const _), integral_const_mul, hre,
      integral_const] at h
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, smul_eq_mul] at h
    have hv : (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real univ = 2 * Real.pi := by
      simp [Measure.real, Real.volume_Ioc, hpi, Real.pi_pos.le]
    rw [hv] at h
    linarith
  have hen : ∀ θ, ‖F θ‖ₑ ^ 2 = ENNReal.ofReal (‖F θ‖ ^ 2) := fun θ => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  show ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ₑ ^ 2
  simp_rw [hen]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun θ => by positivity),
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end ReciprocityTheory.L2DbarEstimates.C
end

section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ae_eq_eqOn {n : ℕ} {Ω : Set (V n)} {U U' : V n → ℂ} (hΩ : IsOpen Ω)
    (hU : ContinuousOn U Ω) (hU' : ContinuousOn U' Ω) (h : U =ᵐ[volume.restrict Ω] U') :
    EqOn U U' Ω := by
  exact Measure.eqOn_open_of_ae_eq h hΩ hU hU'

theorem reg_glue {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball x r) ∧ u =ᵐ[volume.restrict (ball x r)] U) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ u =ᵐ[volume.restrict Ω] U := by
  classical
  choose! r hr hsub U hU hae using hloc
  have agree : ∀ x ∈ Ω, ∀ y ∈ Ω, EqOn (U x) (U y) (ball x (r x) ∩ ball y (r y)) := by
    intro x hx y hy
    apply ae_eq_eqOn (isOpen_ball.inter isOpen_ball)
    · exact ((hU x hx).mono inter_subset_left).continuousOn
    · exact ((hU y hy).mono inter_subset_right).continuousOn
    · have h1 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U x :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae x hx)
      have h2 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U y :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae y hy)
      exact h1.symm.trans h2
  have loc : ∀ y ∈ Ω, ∀ x ∈ ball y (r y), U x x = U y x := by
    intro y hy x hx
    have hxΩ : x ∈ Ω := hsub y hy hx
    exact agree x hxΩ y hy ⟨mem_ball_self (hr x hxΩ), hx⟩
  refine ⟨fun x => U x x, ?_, ?_⟩
  · intro y hy
    have hnhds : ball y (r y) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hr y hy))
    have hev : (fun x => U x x) =ᶠ[𝓝 y] U y :=
      Filter.eventually_of_mem hnhds (fun x hx => loc y hy x hx)
    exact (((hU y hy).differentiableAt hnhds).congr_of_eventuallyEq hev).differentiableWithinAt
  · obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : Ω => ball (x : V n) (r x)) (fun _ => isOpen_ball)
    have hcov : Ω = ⋃ x ∈ T, ball ((x : Ω) : V n) (r x) := by
      rw [hT]
      ext z
      simp only [mem_iUnion]
      constructor
      · intro hz
        exact ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
      · rintro ⟨x, hx⟩
        exact hsub x x.2 hx
    rw [hcov, Filter.EventuallyEq, ae_restrict_biUnion_iff _ hTc]
    intro x _
    filter_upwards [hae x x.2, self_mem_ae_restrict (measurableSet_ball (x := (x : V n)) (ε := r x))]
      with z hz hzb
    rw [hz]
    exact (loc x x.2 z hzb).symm

end ReciprocityTheory.L2DbarEstimates.C
end
