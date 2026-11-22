import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.ChartForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.PSectionBoundedCountable

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionBounded

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

alias homog_congr := SectionNormSqExtension.homog_congr
alias homog_zero := SectionNormSqExtension.homog_zero
alias homog_add := SectionNormSqExtension.homog_add
alias homog_neg := SectionNormSqExtension.homog_neg
alias homog_sub := SectionNormSqExtension.homog_sub
alias homog_sum := SectionNormSqExtension.homog_sum
alias homog_one := SectionNormSqExtension.homog_one
alias homog_C := SectionNormSqExtension.homog_C
alias homog_mul := SectionNormSqExtension.homog_mul
alias homog_X := SectionNormSqExtension.homog_X
alias homog_pow := SectionNormSqExtension.homog_pow

def chartMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem homog_chartMon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMon c d) d :=
  SectionNormSqExtension.homog_chartMon c d

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k :=
  SectionNormSqExtension.aeval_chartMon y c d

theorem eval_chartMon (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k :=
  SectionNormSqExtension.eval_chartMon z c d

alias mConeMap_homog := SectionNormSqExtension.mConeMap_homog
alias vanish := SectionNormSqExtension.vanish
alias exists_form_of_mem_chartRingZ := SectionNormSqExtension.exists_form_of_mem_chartRingZ
alias exists_chartForm := SectionNormSqExtension.exists_chartForm

def coeffNorm (G : MRing ι) : ℝ := ∑ m ∈ G.support, ‖(Int.castRingHom ℂ) (G.coeff m)‖

theorem coeffNorm_nonneg (G : MRing ι) : 0 ≤ coeffNorm G :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_eval_le {z : (Σ k, ι k) → ℂ} {c : ∀ k, ι k} (hz : ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖)
    {G : MRing ι} {δ : K → ℕ} (hG : IsMultiHomog G δ) :
    ‖eval z (map (Int.castRingHom ℂ) G)‖ ≤ coeffNorm G * ∏ k, ‖z ⟨k, c k⟩‖ ^ δ k := by
  first
  | exact @GroundTheory.Variant₂.N1.norm_eval_le_of_forall_norm_le _ _ _ _ _ _ hz _ _ hG
  | exact GroundTheory.Variant₂.N1.norm_eval_le_of_forall_norm_le ..
  | (intros; apply GroundTheory.Variant₂.N1.norm_eval_le_of_forall_norm_le <;> assumption)

theorem zpow_combine {F : Type*} [Field F] {x : F} (hx : x ≠ 0) {du dw N D : ℕ} {a : ℤ}
    (hw : (dw : ℤ) = a + N) (hle : du + dw ≤ D) :
    x ^ du * x ^ N * x ^ (D - (du + dw)) = x ^ (-a) * x ^ D := by
  simp only [← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  rw [Nat.cast_sub hle]
  push_cast
  omega

theorem exists_upper (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * a k) →
      aeval y g = s * aeval y h → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
        B * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k) := by
  obtain ⟨N, δ, G, hG, hdeg, hGv⟩ := exists_chartForm y c hc (fun k => (n : ℤ) * a k) (hs c hc)
  refine ⟨coeffNorm G, coeffNorm_nonneg G, ?_⟩
  intro dg dh g h z hg hh hd hgy hz hmax hz0
  have hr : ∀ k, ‖z ⟨k, c k⟩‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hz0 k)
  have hΨ : IsMultiHomog (G * h - g * chartMon c N) (δ + dh) :=
    homog_sub (homog_mul hG hh) (homog_congr (homog_mul hg (homog_chartMon c N)) fun k => by
      have h1 : (δ k : ℤ) = n * a k + N k := hdeg k
      have h2 := hd k
      have : ((dg k + N k : ℕ) : ℤ) = ((δ k + dh k : ℕ) : ℤ) := by push_cast; linarith
      simp only [Pi.add_apply]
      exact_mod_cast this)
  have hΨy : aeval y (G * h - g * chartMon c N) = 0 := by
    rw [map_sub, map_mul, map_mul, hGv, hgy, aeval_chartMon]
    ring
  have hΨz := vanish hz hΨ hΨy
  simp only [map_sub, map_mul, eval_chartMon, sub_eq_zero] at hΨz
  have hPN : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ N k :=
    Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hδ : ∏ k, ‖z ⟨k, c k⟩‖ ^ δ k =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k)) * ∏ k, ‖z ⟨k, c k⟩‖ ^ N k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hr k),
      show ((δ k : ℕ) : ℤ) = (n : ℤ) * a k + N k from hdeg k]
  have e1 : ‖eval z (map (Int.castRingHom ℂ) g)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ N k =
      ‖eval z (map (Int.castRingHom ℂ) G)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := by
    rw [← norm_mul, hΨz, norm_mul, norm_prod]
    simp only [norm_pow]
  have key : ‖eval z (map (Int.castRingHom ℂ) g)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ N k ≤
      (coeffNorm G * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k)) *
        ∏ k, ‖z ⟨k, c k⟩‖ ^ N k := by
    rw [e1]
    calc _ ≤ (coeffNorm G * ∏ k, ‖z ⟨k, c k⟩‖ ^ δ k) * ‖eval z (map (Int.castRingHom ℂ) h)‖ :=
          mul_le_mul_of_nonneg_right (norm_eval_le hmax hG) (norm_nonneg _)
      _ = _ := by rw [hδ]; ring
  exact le_of_mul_le_mul_right key hPN

theorem exists_lower (y : (Σ k, ι k) → Ω) (A : HermLine ι) (q : ℕ) (w : Fin q → Ω)
    (hw : ∀ j, w j ∈ chartLat y A.a 1) (hgen : KH.GeneratesOn y A.a w)
    (hsm : ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ mcPts (mCoordIdeal y), (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  obtain ⟨u, hu, hsum⟩ := hgen c hc
  choose δu U hU hUv using fun j => exists_form_of_mem_chartRingZ y c hc (hu j)
  have hw' : ∀ j, w j * ∏ k, y ⟨k, c k⟩ ^ (-A.a k) ∈ chartRingZ y c := fun j => by
    have := hw j c hc
    simp only [Nat.cast_one, one_mul] at this
    exact this
  choose N δw g hg hdeg hgv using fun j => exists_chartForm y c hc A.a (hw' j)
  set D : K → ℕ := fun k => ∑ j, (δu j k + δw j k) with hD
  have hle : ∀ j k, δu j k + δw j k ≤ D k := fun j k =>
    Finset.single_le_sum (f := fun j => δu j k + δw j k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Φ : MRing ι := chartMon c D - ∑ j, U j * g j * chartMon c (fun k => D k - (δu j k + δw j k)) with hΦ
  have hΦh : IsMultiHomog Φ D := homog_sub (homog_chartMon c D) (homog_sum _ fun j _ =>
    homog_congr (homog_mul (homog_mul (hU j) (hg j)) (homog_chartMon c _)) fun k => by
      have := hle j k
      simp only [Pi.add_apply]
      omega)
  have hterm : ∀ j, aeval y (U j * g j * chartMon c (fun k => D k - (δu j k + δw j k))) =
      u j * (w j * ∏ k, y ⟨k, c k⟩ ^ (-A.a k)) * ∏ k, y ⟨k, c k⟩ ^ D k := by
    intro j
    rw [map_mul, map_mul, hUv j, hgv j, aeval_chartMon]
    calc u j * (∏ k, y ⟨k, c k⟩ ^ δu j k) * (w j * ∏ k, y ⟨k, c k⟩ ^ N j k) *
          ∏ k, y ⟨k, c k⟩ ^ (D k - (δu j k + δw j k))
        = u j * w j * ∏ k, (y ⟨k, c k⟩ ^ δu j k * y ⟨k, c k⟩ ^ N j k *
            y ⟨k, c k⟩ ^ (D k - (δu j k + δw j k))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          ring
      _ = u j * w j * ∏ k, (y ⟨k, c k⟩ ^ (-A.a k) * y ⟨k, c k⟩ ^ D k) := by
          congr 1
          exact Finset.prod_congr rfl fun k _ => zpow_combine (hc k) (hdeg j k) (hle j k)
      _ = _ := by
          rw [Finset.prod_mul_distrib]
          ring
  have hΦy : aeval y Φ = 0 := by
    rw [hΦ, map_sub, map_sum, aeval_chartMon, Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, hsum,
      one_mul, sub_self]
  refine ⟨∑ j, coeffNorm (U j), Finset.sum_nonneg fun j _ => coeffNorm_nonneg _, ?_⟩
  intro z hz hmax hz0
  have hr : ∀ k, ‖z ⟨k, c k⟩‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hz0 k)
  have hΦz := vanish hz hΦh hΦy
  simp only [hΦ, map_sub, map_sum, map_mul, eval_chartMon, sub_eq_zero] at hΦz
  have hbd : ∏ k, ‖z ⟨k, c k⟩‖ ^ D k ≤
      ∑ j, coeffNorm (U j) * A.h z * ∏ k, (‖z ⟨k, c k⟩‖ ^ (-A.a k) * ‖z ⟨k, c k⟩‖ ^ D k) := by
    have e0 : ∏ k, ‖z ⟨k, c k⟩‖ ^ D k = ‖∏ k, z ⟨k, c k⟩ ^ D k‖ := by
      rw [norm_prod]
      simp only [norm_pow]
    rw [e0, hΦz]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have hUz := norm_eval_le hmax (hU j)
    have hgz := hsm j (δw j) (N j) (g j) (chartMon c (N j)) z (hg j) (homog_chartMon c _)
      (fun k => by rw [hdeg j k]; push_cast; ring) (by rw [hgv j, aeval_chartMon]) hz
    rw [eval_chartMon, norm_prod, pow_one] at hgz
    simp only [norm_pow] at hgz
    rw [norm_mul, norm_mul, norm_prod]
    simp only [norm_pow]
    calc _ ≤ (coeffNorm (U j) * ∏ k, ‖z ⟨k, c k⟩‖ ^ δu j k) * ((∏ k, ‖z ⟨k, c k⟩‖ ^ N j k) * A.h z) *
          ∏ k, ‖z ⟨k, c k⟩‖ ^ (D k - (δu j k + δw j k)) := by
          gcongr
          exact mul_nonneg (coeffNorm_nonneg _) (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
      _ = coeffNorm (U j) * A.h z * ∏ k, (‖z ⟨k, c k⟩‖ ^ δu j k * ‖z ⟨k, c k⟩‖ ^ N j k *
            ‖z ⟨k, c k⟩‖ ^ (D k - (δu j k + δw j k))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          ring
      _ = _ := by
          congr 1
          exact Finset.prod_congr rfl fun k _ => zpow_combine (hr k) (hdeg j k) (hle j k)
  rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.prod_mul_distrib] at hbd
  have hPD : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ D k :=
    Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hR : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hQR : (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hr k))]
  set M := ∑ j, coeffNorm (U j)
  set PD := ∏ k, ‖z ⟨k, c k⟩‖ ^ D k
  set Q := ∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)
  set R := ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k
  have h1 : 1 ≤ M * A.h z * Q := by
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have := mul_lt_mul_of_pos_right hlt hPD
    nlinarith
  calc R = R * 1 := (mul_one R).symm
    _ ≤ R * (M * A.h z * Q) := mul_le_mul_of_nonneg_left h1 hR.le
    _ = M * A.h z * (Q * R) := by ring
    _ = M * A.h z := by rw [hQR, mul_one]

end SectionBounded

open SectionBounded in

theorem SectionBounded.proof : SectionBounded.Statement := by
  intro K _ ι _ Ω _ y A q w hw hgen hsm n s hs
  classical
  choose M hM0 hM using fun c hc => exists_lower y A q w hw hgen hsm c hc
  choose B hB0 hB using fun c hc => exists_upper y A.a n hs c hc
  refine ⟨∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c hc ^ n else 0, ?_⟩
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM c hyc z hz hcmax hz0
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ n := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * A.a k) ≤ M c hyc ^ n * A.h z ^ n := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 n
  have hCge : B c hyc * M c hyc ^ n ≤
      ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c hc ^ n else 0 := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c hc ^ n else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c' hc') n)
        · exact le_rfl) (Finset.mem_univ c)
    simpa only [dif_pos hyc] using this
  have hAh : 0 ≤ A.h z ^ n := pow_nonneg (A.pos z hz.1).le n
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M c hyc ^ n * A.h z ^ n) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M c hyc ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ n := by ring
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
