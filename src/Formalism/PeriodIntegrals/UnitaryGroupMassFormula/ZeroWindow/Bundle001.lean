module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightHalfWith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Metric Complex Filter Topology

namespace PI.ZW

abbrev zeta1 : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1

lemma zeta1_eq_sub_one_mul_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : zeta1 s = (s - 1) * riemannZeta s := by
  show DirichletCharacter.LFunctionTrivChar₁ 1 s = _
  unfold DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs]
  simp [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]

lemma zeta1_apply_one : zeta1 1 = 1 := by
  show DirichletCharacter.LFunctionTrivChar₁ 1 1 = 1
  unfold DirichletCharacter.LFunctionTrivChar₁
  simp

lemma analyticAt_riemannZeta_of_ne {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  exact DifferentiableOn.analyticAt (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

lemma order_zeta1 {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt zeta1 s = analyticOrderNatAt riemannZeta s := by
  have hev : zeta1 =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 := analyticAt_riemannZeta_of_ne hs
  simp only [analyticOrderNatAt]
  rw [analyticOrderAt_congr hev,
    show (fun z => (z - 1) * riemannZeta z) = (fun z : ℂ => z - 1) * riemannZeta from rfl,
    analyticOrderAt_mul h1 h2]
  have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
    (analyticOrderAt_eq_zero).2 (Or.inr (by simpa [sub_eq_zero] using hs))
  rw [h0, zero_add]

theorem rightOne_of (hJ : JensenCount) : RightOne := by
  intro hZ hI
  refine ⟨11 / Real.log ((19 / 10) / (37 / 20)), ?_⟩
  intro N _ χ hN t
  subst hN
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hlogq : 0 < Real.log ((19 / 10 : ℝ) / (37 / 20)) := Real.log_pos (by norm_num)
  set c : ℂ := 2 + (t : ℂ) * Complex.I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hc1 : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hcre] at this
    norm_num at this
  have hAn : AnalyticOnNhd ℂ zeta1 (closedBall c (19 / 10)) := fun z _ =>
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hcre]; norm_num)
  have hfc : zeta1 c ≠ 0 := by
    rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hc1]
    exact mul_ne_zero (sub_ne_zero.2 hc1) hζc
  have hζlow : (1 / 2 : ℝ) ≤ ‖riemannZeta c‖ := by
    have k := hI 1 (1 : DirichletCharacter ℂ 1) c (by rw [hcre]; norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq, hcre] at k
    have hpos : 0 < ‖riemannZeta c‖ := norm_pos_iff.2 hζc
    have k2 : ‖riemannZeta c‖⁻¹ ≤ 2 := by norm_num at k ⊢; linarith
    have := inv_le_of_inv_le₀ hpos k2
    norm_num at this ⊢
    linarith
  have hc1n : (1 : ℝ) ≤ ‖c - 1‖ := by
    have := Complex.abs_re_le_norm (c - 1)
    rw [Complex.sub_re, hcre, Complex.one_re] at this
    norm_num at this
    linarith
  have hfcl : (1 / 2 : ℝ) ≤ ‖zeta1 c‖ := by
    rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hc1, norm_mul]
    nlinarith [norm_nonneg (riemannZeta c)]
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hsph : ∀ z ∈ sphere c (19 / 10), ‖zeta1 z‖ ≤ 13 * (|t| + 5) ^ 2 := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    by_cases hz1 : z = 1
    · rw [hz1, zeta1_apply_one, norm_one]
      nlinarith
    · rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hz1, norm_mul]
      have hre : (1 / 10 : ℝ) ≤ z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, hcre, hz] at this
        have := (abs_le.1 this).1
        linarith
      have hcn : ‖c‖ ≤ 2 + |t| := by
        rw [hc]
        calc ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = 2 + |t| := by simp
      have hzn : ‖z‖ ≤ |t| + 4 := by
        have := norm_le_insert' z c
        have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
          calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
            _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        linarith
      have hz1n : ‖z - 1‖ ≤ |t| + 5 := by
        have := norm_sub_le z 1
        rw [norm_one] at this
        linarith
      have hζ := hZ z (by linarith) hz1
      have hz1pos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
      have hinv : 1 + 1 / z.re ≤ 11 := by
        have : 1 / z.re ≤ 10 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        linarith
      have hA : ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 5) * (|t| + 5) * 11 := by
        have h1 : 0 ≤ ‖z - 1‖ * ‖z‖ := by positivity
        calc ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) ≤ ‖z - 1‖ * ‖z‖ * 11 := mul_le_mul_of_nonneg_left hinv h1
          _ ≤ (|t| + 5) * (|t| + 5) * 11 := by
            have : ‖z‖ ≤ |t| + 5 := by linarith
            gcongr
      calc ‖z - 1‖ * ‖riemannZeta z‖
          ≤ ‖z - 1‖ * (1 + 1 / ‖z - 1‖ + ‖z‖ * (1 + 1 / z.re)) :=
            mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
        _ = ‖z - 1‖ + ‖z - 1‖ * (1 / ‖z - 1‖) + ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) := by ring
        _ = ‖z - 1‖ + 1 + ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) := by rw [mul_one_div_cancel hz1pos.ne']
        _ ≤ 13 * (|t| + 5) ^ 2 := by nlinarith
  have hM1 : (1 : ℝ) ≤ 13 * (|t| + 5) ^ 2 := by nlinarith
  have hsub : RightNear χ t ⊆ {z | z ∈ closedBall c (37 / 20) ∧ zeta1 z = 0} := by
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rw [hL] at h4
    have hρ1 : ρ ≠ 1 := by
      intro e
      rw [e] at h2
      simp at h2
    refine ⟨?_, by rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hρ1, h4, mul_zero]⟩
    rw [mem_closedBall, dist_eq_norm]
    have hsq : ‖ρ - c‖ ^ 2 ≤ (37 / 20) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hcre, hcim]
      have := abs_le.1 h3
      nlinarith
    nlinarith [norm_nonneg (ρ - c)]
  obtain ⟨hfin, hsum⟩ := hJ zeta1 c (13 * (|t| + 5) ^ 2) hAn hfc hM1 hsph _ hsub
  refine ⟨hfin, ?_⟩
  rw [hL]
  have hcongr : ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt riemannZeta ρ : ℝ) =
      ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt zeta1 ρ : ℝ) := by
    refine finsum_mem_congr rfl fun ρ hρ => ?_
    have hρ1 : ρ ≠ 1 := by
      intro e
      have h2 := hρ.2.1
      rw [e] at h2
      simp at h2
    rw [order_zeta1 hρ1]
  rw [hcongr]
  refine hsum.trans ?_
  simp only [Nat.cast_one, one_mul]
  set y : ℝ := |t| + 2 with hy
  have hy2 : (2 : ℝ) ≤ y := by linarith
  have hfpos : 0 < ‖zeta1 c‖ := by linarith
  have hq : 13 * (|t| + 5) ^ 2 / ‖zeta1 c‖ ≤ y ^ 11 := by
    rw [div_le_iff₀ hfpos]
    have e1 : |t| + 5 ≤ 3 * y := by linarith
    have e2 : (|t| + 5) ^ 2 ≤ 9 * y ^ 2 := by nlinarith
    have e3 : (256 : ℝ) ≤ y ^ 8 := by
      have := pow_le_pow_left₀ (by norm_num) hy2 8
      norm_num at this
      linarith
    have e4 : y ^ 10 ≤ y ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e5 : 256 * y ^ 2 ≤ y ^ 10 := by
      have := mul_le_mul_of_nonneg_right e3 (sq_nonneg y)
      calc 256 * y ^ 2 ≤ y ^ 8 * y ^ 2 := this
        _ = y ^ 10 := by ring
    have e6 : y ^ 11 * (1 / 2) ≤ y ^ 11 * ‖zeta1 c‖ :=
      mul_le_mul_of_nonneg_left hfcl (by positivity)
    nlinarith
  have hlog : Real.log (13 * (|t| + 5) ^ 2 / ‖zeta1 c‖) ≤ 11 * Real.log y := by
    rw [show (11 : ℝ) * Real.log y = Real.log (y ^ 11) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) hq
  calc Real.log (13 * (|t| + 5) ^ 2 / ‖zeta1 c‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ 11 * Real.log y / Real.log ((19 / 10) / (37 / 20)) := div_le_div_of_nonneg_right hlog hlogq.le
    _ = 11 / Real.log ((19 / 10) / (37 / 20)) * Real.log y := by ring

end PI.ZW
end
end

section

noncomputable section

open Metric Complex

namespace PI.ZW

lemma log_le_nine (X M' : ℝ) (hX : 2 ≤ X) (hM : 0 < M') (h : M' ≤ 170 * X) :
    Real.log M' ≤ 9 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have h170 : Real.log 170 ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  calc Real.log M' ≤ Real.log (170 * X) := Real.log_le_log hM h
    _ = Real.log 170 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    _ ≤ 9 * Real.log X := by linarith

lemma mem_closedBall_of_right {ρ : ℂ} {t : ℝ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) (h3 : |ρ.im - t| ≤ 1) :
    ρ ∈ closedBall (2 + t * I) (37 / 20) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ (37 / 20) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    have h4 := abs_le.mp h3
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 7 / 2 - ρ.re),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (ρ.im - t)) (by linarith : (0 : ℝ) ≤ 1 + (ρ.im - t))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq

lemma sphere_facts {z : ℂ} {t : ℝ} (hz : z ∈ sphere (2 + t * I) (19 / 10)) :
    1 / 10 ≤ z.re ∧ ‖z‖ ≤ |t| + 4 := by
  rw [mem_sphere, dist_eq_norm] at hz
  have hc : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  constructor
  · have h1 := Complex.abs_re_le_norm (z - (2 + t * I))
    rw [hz] at h1
    simp at h1
    linarith [(abs_le.mp h1).1]
  · calc ‖z‖ = ‖(z - (2 + t * I)) + (2 + t * I)‖ := by ring_nf
      _ ≤ ‖z - (2 + t * I)‖ + ‖(2 : ℂ) + t * I‖ := norm_add_le _ _
      _ ≤ |t| + 4 := by rw [hz]; linarith

theorem rightChi_of (hJ : JensenCount) : RightChi := by
  intro hL hI
  have hl : 0 < Real.log ((19 / 10) / (37 / 20) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨9 / Real.log ((19 / 10) / (37 / 20)), fun N _ χ hχ t => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcre : (2 + t * I : ℂ).re = 2 := by simp
  have hc0 : DirichletCharacter.LFunction χ (2 + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hcre]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := norm_pos_iff.mpr hc0
  have hinv := hI N χ (2 + t * I) (by rw [hcre]; norm_num)
  rw [hcre] at hinv
  have hfc : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
    have h := (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mp (hinv.trans (by norm_num))
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall (2 + t * I) (19 / 10)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hM1 : (1 : ℝ) ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    have : 0 ≤ 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by positivity
    linarith
  have hbd : ∀ z ∈ sphere (2 + t * I) (19 / 10), ‖DirichletCharacter.LFunction χ z‖ ≤
      1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := sphere_facts hz
    have hz0 : 0 < z.re := by linarith
    refine (hL N χ hχ z hz0).trans ?_
    have h1 : ‖z‖ / z.re ≤ 10 * (|t| + 4) := by
      rw [div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 10 * (|t| + 4))]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1))
    nlinarith
  have hS : RightNear χ t ⊆ {z | z ∈ closedBall (2 + t * I) (37 / 20) ∧ DirichletCharacter.LFunction χ z = 0} :=
    fun ρ hρ => ⟨mem_closedBall_of_right hρ.1 hρ.2.1 hρ.2.2.1, hρ.2.2.2⟩
  obtain ⟨hfin, hsum⟩ := hJ (DirichletCharacter.LFunction χ) (2 + t * I) _ han hc0 hM1 hbd (RightNear χ t) hS
  refine ⟨hfin, hsum.trans ?_⟩
  have hX : 2 ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have htN : |t| ≤ N * |t| := le_mul_of_one_le_left (abs_nonneg t) hNr
  have hM85 : 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) ≤ 85 * ((N : ℝ) * (|t| + 2)) := by
    nlinarith [abs_nonneg t]
  have hM' : (1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) / ‖DirichletCharacter.LFunction χ (2 + t * I)‖ ≤
      170 * ((N : ℝ) * (|t| + 2)) := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hfc (by linarith : (0 : ℝ) ≤ (N : ℝ) * (|t| + 2))]
  have h9 := log_le_nine _ _ hX (by positivity) hM'
  calc Real.log ((1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) /
        ‖DirichletCharacter.LFunction χ (2 + t * I)‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ (9 * Real.log ((N : ℝ) * (|t| + 2))) / Real.log ((19 / 10) / (37 / 20)) :=
        div_le_div_of_nonneg_right h9 hl.le
    _ = 9 / Real.log ((19 / 10) / (37 / 20)) * Real.log ((N : ℝ) * (|t| + 2)) := by ring

end PI.ZW
end
end

section

noncomputable section

open Complex Filter Topology

namespace PI.ZW

open DirichletCharacter

lemma differentiable_gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (gammaFactor χ s)⁻¹) := by
  by_cases h : χ.Even
  · simp only [DirichletCharacter.gammaFactor, h, if_true]
    exact Complex.differentiable_Gammaℝ_inv
  · simp only [DirichletCharacter.gammaFactor, h, if_false]
    exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  by_cases h : χ.Even
  · simp only [DirichletCharacter.gammaFactor, h, if_true]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · simp only [DirichletCharacter.gammaFactor, h, if_false]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

lemma isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact (DirichletCharacter.isPrimitive_def χ).mp hχ

lemma rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    rootNumber χ ≠ 0 := by
  intro h
  have h2 := hχ.completedLFunction_one_sub (-1)
  rw [h] at h2
  simp only [mul_zero, zero_mul] at h2
  norm_num at h2
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num : (2 : ℂ) ≠ 1))
    (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl two_ne_zero), h2, zero_div] at hne
  exact hne rfl

lemma isOpen_strip : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem transfer : Transfer := by
  intro N _ χ hχ ρ h0 h1 hz
  have hχi := isPrimitive_inv hχ
  have hstrip : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < (1 - s).re := fun s _ h => by simp; linarith
  have hfun : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ⁻¹ (1 - s) =
      ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
        DirichletCharacter.LFunction χ s := by
    intro s hs0 hs1
    have h1s := hstrip s hs0 hs1
    have hg1 := gammaFactor_ne_zero_of_re_pos χ⁻¹ h1s
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs0
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
        (Or.inl fun h => by rw [h] at h1s; simp at h1s),
      hχi.completedLFunction_one_sub s, inv_inv,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl fun h => by rw [h] at hs0; simp at hs0)]
    field_simp
  refine ⟨by rw [hfun ρ h0 h1, hz, mul_zero], ?_⟩
  have hρU : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ 𝓝 ρ := isOpen_strip.mem_nhds ⟨h0, h1⟩
  have hHd : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s *
      (gammaFactor χ⁻¹ (1 - s))⁻¹) {s | 0 < s.re ∧ s.re < 1} := by
    intro s hs
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs.1
    have hdg : DifferentiableAt ℂ (gammaFactor χ) s := by
      have h := ((differentiable_gammaFactor_inv χ) s).inv (inv_ne_zero hg0)
      have e : (fun x => (gammaFactor χ x)⁻¹)⁻¹ = gammaFactor χ := funext fun x => by
        simp only [Pi.inv_apply, inv_inv]
      rwa [e] at h
    have hdg1 : DifferentiableAt ℂ (fun s => (gammaFactor χ⁻¹ (1 - s))⁻¹) s :=
      ((differentiable_gammaFactor_inv χ⁻¹) (1 - s)).comp s ((differentiableAt_const 1).sub differentiableAt_id)
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2)) s :=
      (differentiableAt_id.sub_const _).const_cpow (Or.inl (by exact_mod_cast NeZero.ne N))
    exact (((hcp.mul_const _).mul hdg).mul hdg1).differentiableWithinAt
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re ∧ s.re < 1} :=
    fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hHa := hHd.analyticAt hρU
  have hLa := hLd.analyticAt hρU
  have hH0 : (N : ℂ) ^ (ρ - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ ρ * (gammaFactor χ⁻¹ (1 - ρ))⁻¹ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero hχi))
      (gammaFactor_ne_zero_of_re_pos χ h0)) (inv_ne_zero (gammaFactor_ne_zero_of_re_pos χ⁻¹ (hstrip ρ h0 h1)))
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [NeZero.ne N]
  have key : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    have e1 := analyticOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.LFunction χ⁻¹)
      (g := fun s : ℂ => 1 - s) (z₀ := ρ) (analyticAt_const.sub analyticAt_id) (by simp)
    rw [← e1]
    have e2 : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
        ((fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
          DirichletCharacter.LFunction χ) :=
      Filter.eventually_of_mem hρU fun s hs => hfun s hs.1 hs.2
    rw [analyticOrderAt_congr e2, analyticOrderAt_mul hHa hLa, (hHa.analyticOrderAt_eq_zero).mpr hH0, zero_add]
  have e : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    simp only [analyticOrderNatAt, key]
  exact e.le

end PI.ZW
end
end
