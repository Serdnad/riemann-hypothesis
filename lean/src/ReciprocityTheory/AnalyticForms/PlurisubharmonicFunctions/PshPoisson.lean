import Mathlib

open Complex Metric Real Filter Topology InnerProductSpace

namespace ReciprocityTheory.AnForm.A

noncomputable def poissonInt (g : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 w • g) 0 r

lemma poissonKernel_zero_continuousOn {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 r) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel, ← abs_of_pos hr]
  exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)

lemma poissonKernel_zero_nonneg {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : 0 ≤ poissonKernel 0 w z := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  refine div_nonneg ?_ (sq_nonneg _)
  simp only [sub_zero]
  rw [hz]
  nlinarith [norm_nonneg w]

lemma poissonKernel_zero_le {r δ : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) (hδ : 0 < δ) (hzw : δ ≤ ‖z - w‖) :
    poissonKernel 0 w z ≤ (r ^ 2 - ‖w‖ ^ 2) / δ ^ 2 := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  simp only [sub_zero]
  rw [hz]
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hden : δ ^ 2 ≤ ‖z - w‖ ^ 2 := by nlinarith [hzw, hδ]
  exact div_le_div_of_nonneg_left hnum (pow_pos hδ 2) hden

lemma circleAverage_poissonKernel_zero {r : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    Real.circleAverage (poissonKernel 0 w) 0 r = 1 := by
  have h : HarmonicOnNhd (fun _ : ℂ => (1 : ℝ)) (closedBall 0 r) :=
    fun _ _ => harmonicAt_const 1
  simpa only [smul_eq_mul, Pi.mul_def, mul_one] using h.circleAverage_poissonKernel_smul hw

lemma poissonInt_eq_re_of_circleIntegrable {g : ℂ → ℝ} {r : ℝ}
    (hg : CircleIntegrable g 0 r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w =
      (Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r).re := by
  rw [poissonInt, poissonKernel_eq_re_herglotzRieszKernel]
  exact (re_circleAverage_herglotzRieszKernel_smul hg hw).symm

lemma poissonInt_eq_re {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w =
      (Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r).re :=
  poissonInt_eq_re_of_circleIntegrable (hg.circleIntegrable hr.le) hw

/-- The Poisson integral is harmonic in the disk for circle-integrable boundary data. -/
lemma poissonInt_harmonicAt_of_circleIntegrable {g : ℂ → ℝ} {r : ℝ}
    (hg : CircleIntegrable g 0 r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    HarmonicAt (poissonInt g r) w := by
  have hi : CircleIntegrable (fun ζ => (g ζ : ℂ)) 0 r := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have h := (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hi w hw).harmonicAt_re
  apply (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr h
  filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
  exact poissonInt_eq_re_of_circleIntegrable hg hw'

lemma poissonInt_harmonicAt {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) : HarmonicAt (poissonInt g r) w :=
  poissonInt_harmonicAt_of_circleIntegrable (hg.circleIntegrable hr.le) hw

lemma poissonInt_zero {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    poissonInt g r 0 = Real.circleAverage g 0 r := by
  unfold poissonInt
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hz
  have hz0 : ‖z‖ ≠ 0 := by rw [hz]; exact hr.ne'
  simp only [smul_eq_mul, Pi.mul_apply, poissonKernel_def, sub_zero, norm_zero]
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hz0)]
  ring

lemma poissonInt_sub {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) (c : ℝ) :
    poissonInt g r w - c =
      Real.circleAverage (fun z ↦ poissonKernel 0 w z * (g z - c)) 0 r := by
  have hP := poissonKernel_zero_continuousOn hr hw
  have hPg : CircleIntegrable (poissonKernel 0 w • g) 0 r :=
    (hP.mul hg).circleIntegrable hr.le
  have hPc : CircleIntegrable (fun z => c • poissonKernel 0 w z) 0 r :=
    CircleIntegrable.const_smul (a := c) (hP.circleIntegrable hr.le)
  have hsplit : (fun z => poissonKernel 0 w z * (g z - c)) =
      fun z => (poissonKernel 0 w • g) z - c • poissonKernel 0 w z := by
    funext z
    simp only [smul_eq_mul, Pi.mul_apply]
    ring
  rw [hsplit, Real.circleAverage_fun_sub hPg hPc, Real.circleAverage_fun_smul,
    circleAverage_poissonKernel_zero hw]
  simp only [poissonInt, smul_eq_mul, mul_one]

lemma poissonInt_tendsto {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere (0 : ℂ) r) :
    Tendsto (poissonInt g r) (𝓝[ball 0 r] ζ₀) (𝓝 (g ζ₀)) := by
  have hζ : ‖ζ₀‖ = r := mem_sphere_zero_iff_norm.mp hζ₀
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M :=
    (isCompact_sphere 0 r).exists_bound_of_continuousOn (hg.sub continuousOn_const)
  set M' := max M 0
  have hMM : ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M' :=
    fun z hz => (hM z hz).trans (le_max_left _ _)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.continuousOn_iff.mp hg ζ₀ hζ₀ (ε / 2) (half_pos hε)
  let K : ℂ → ℝ := fun w => M' * ((r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2)
  have hKc : ContinuousAt K ζ₀ := by
    unfold K
    fun_prop
  have hKzero : K ζ₀ = 0 := by simp [K, hζ]
  obtain ⟨δ, hδ, hδK⟩ := Metric.continuousAt_iff.mp hKc (ε / 2) (half_pos hε)
  refine ⟨min (η / 2) δ, lt_min (half_pos hη) hδ, ?_⟩
  intro w hw hwd
  have hwb : ‖w‖ < r := mem_ball_zero_iff.mp hw
  have hδ1 : dist w ζ₀ < η / 2 := hwd.trans_le (min_le_left _ _)
  have hKlt : K w < ε / 2 := by
    have hKdist : dist (K w) (K ζ₀) < ε / 2 := hδK (hwd.trans_le (min_le_right _ _))
    rw [Real.dist_eq, hKzero, sub_zero] at hKdist
    exact (le_abs_self _).trans_lt hKdist
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hq : 0 ≤ (η / 2) ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ K w := mul_nonneg (le_max_right M 0) (div_nonneg hnum hq)
  have hpt : ∀ z ∈ sphere (0 : ℂ) r,
      ‖poissonKernel 0 w z * (g z - g ζ₀)‖ ≤ ε / 2 * poissonKernel 0 w z + K w := by
    intro z hz
    have hP0 := poissonKernel_zero_nonneg hw hz
    rw [norm_mul, Real.norm_of_nonneg hP0]
    by_cases hzη : dist z ζ₀ < η
    · have h3 := hgη z hz hzη
      rw [dist_eq_norm] at h3
      have h4 := mul_le_mul_of_nonneg_left h3.le hP0
      linarith
    · push Not at hzη
      have hzw : η / 2 ≤ ‖z - w‖ := by
        have h5 := dist_triangle z w ζ₀
        rw [dist_eq_norm z w] at h5
        linarith
      have hPle := poissonKernel_zero_le hw hz (half_pos hη) hzw
      have hgM := hMM z hz
      have h6 : poissonKernel 0 w z * ‖g z - g ζ₀‖ ≤
          (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' :=
        mul_le_mul hPle hgM (norm_nonneg _) (div_nonneg hnum hq)
      have h7 : (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' = K w := by simp [K, mul_comm]
      have h8 : 0 ≤ ε / 2 * poissonKernel 0 w z := mul_nonneg (half_pos hε).le hP0
      linarith
  rw [Real.dist_eq, poissonInt_sub hr hg hw (g ζ₀)]
  let f : ℂ → ℝ := fun z => poissonKernel 0 w z * (g z - g ζ₀)
  have hP := poissonKernel_zero_continuousOn hr hw
  have hf : CircleIntegrable f 0 r := (hP.mul (hg.sub continuousOn_const)).circleIntegrable hr.le
  have hscaled : CircleIntegrable (fun z => (ε / 2) • poissonKernel 0 w z) 0 r :=
    CircleIntegrable.const_smul (a := ε / 2) (hP.circleIntegrable hr.le)
  calc
    |Real.circleAverage f 0 r| ≤ Real.circleAverage |f| 0 r :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun z => (ε / 2) • poissonKernel 0 w z + K w) 0 r :=
      Real.circleAverage_mono hf.abs (hscaled.add (circleIntegrable_const (K w) 0 r)) (by
        intro z hz
        rw [abs_of_pos hr] at hz
        simpa [f, Real.norm_eq_abs] using hpt z hz)
    _ = ε / 2 + K w := by
      rw [Real.circleAverage_fun_add hscaled (circleIntegrable_const (K w) 0 r),
        Real.circleAverage_fun_smul, circleAverage_poissonKernel_zero hw,
        Real.circleAverage_const, smul_eq_mul, mul_one]
    _ < ε := by linarith

theorem poisson_ext {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere 0 r)) :
    ∃ Φ : ℂ → ℝ, ContinuousOn Φ (Metric.closedBall 0 r) ∧ (∀ ζ ∈ Metric.sphere 0 r, Φ ζ = g ζ) ∧
      Φ 0 = Real.circleAverage g 0 r ∧
      ∀ a s, 0 < s → Metric.closedBall a s ⊆ Metric.ball 0 r → Real.circleAverage Φ a s = Φ a := by
  refine ⟨fun z ↦ if ‖z‖ < r then poissonInt g r z else g z, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with hlt | heq
    · have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hlt
      have hca := (poissonInt_harmonicAt hr hg hzb).1.continuousAt
      have hev : poissonInt g r =ᶠ[𝓝 z] fun z ↦ if ‖z‖ < r then poissonInt g r z else g z := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      exact (hca.congr hev).continuousWithinAt
    · have hzs : z ∈ sphere (0 : ℂ) r := mem_sphere_zero_iff_norm.mpr heq
      have hval : (if ‖z‖ < r then poissonInt g r z else g z) = g z :=
        if_neg (by rw [heq]; exact lt_irrefl r)
      show Filter.Tendsto (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z)
        (𝓝[closedBall 0 r] z) (𝓝 (if ‖z‖ < r then poissonInt g r z else g z))
      rw [hval, ← Metric.ball_union_sphere, nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · refine Filter.Tendsto.congr' ?_ (poissonInt_tendsto hr hg hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      · refine Filter.Tendsto.congr' ?_ (hg z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_neg (by rw [mem_sphere_zero_iff_norm.mp hy]; exact lt_irrefl r)]
  · intro ζ hζ
    exact if_neg (by rw [mem_sphere_zero_iff_norm.mp hζ]; exact lt_irrefl r)
  · show (if ‖(0 : ℂ)‖ < r then poissonInt g r 0 else g 0) = Real.circleAverage g 0 r
    rw [if_pos (by rw [norm_zero]; exact hr)]
    exact poissonInt_zero hr
  · intro a s hs hsub
    have hev : Set.EqOn (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z) (poissonInt g r)
        (sphere a |s|) := by
      intro y hy
      rw [abs_of_pos hs] at hy
      have hyb : y ∈ ball (0 : ℂ) r := hsub (sphere_subset_closedBall hy)
      exact if_pos (mem_ball_zero_iff.mp hyb)
    rw [Real.circleAverage_congr_sphere hev]
    have ha : a ∈ ball (0 : ℂ) r := hsub (mem_closedBall_self hs.le)
    show _ = (if ‖a‖ < r then poissonInt g r a else g a)
    rw [if_pos (mem_ball_zero_iff.mp ha)]
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    intro y hy
    rw [abs_of_pos hs] at hy
    exact poissonInt_harmonicAt hr hg (hsub hy)

end ReciprocityTheory.AnForm.A
