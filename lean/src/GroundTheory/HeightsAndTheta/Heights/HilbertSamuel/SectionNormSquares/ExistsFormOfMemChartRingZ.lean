import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.ChartForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + n * a k) ∧
    aeval y g = s * aeval y h

theorem cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} {g h g' h' : MRing ι}
    (hr : IsRep y a n s g h) (hr' : IsRep y a n s g' h') {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := hr'
  have hF : IsMultiHomog (g * h' - g' * h) (dg + dh') :=
    homog_sub (homog_mul hg hh') (homog_congr (homog_mul hg' hh) fun k => by
      simp only [Pi.add_apply]
      zify
      linear_combination hd' k - hd k)
  have hFy : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := vanish hz hF hFy
  simp only [map_sub, map_mul, sub_eq_zero] at this
  exact this

theorem exists_rep_at {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ gh : MRing ι × MRing ι, IsRep y a n s gh.1 gh.2 ∧ eval z (map (Int.castRingHom ℂ) gh.2) ≠ 0 := by
  choose c hc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_zero hz (hc k)
  obtain ⟨N, δ, G, hG, hdeg, hGv⟩ := exists_chartForm y c hyc (fun k => (n : ℤ) * a k) (hs c hyc)
  refine ⟨(G, chartMon c N), ⟨δ, N, hG, homog_chartMon c N, fun k => ?_, ?_⟩, ?_⟩
  · linear_combination hdeg k
  · rw [aeval_chartMon]
    exact hGv
  · rw [eval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

theorem metric_ne {A : HermLine ι} {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (n : ℕ) :
    (A.h z : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (A.pos z hz.1).ne')

def val (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ := by
  classical
  exact if hsz : s ∈ chartLat y A.a n ∧ z ∈ mcPts (mCoordIdeal y) then
    eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.1) /
      (eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.2) * (A.h z : ℂ) ^ n)
  else 0

theorem val_spec {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h) :
    eval z (map (Int.castRingHom ℂ) g) =
      val y A n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n := by
  have H := (exists_rep_at hs hz).choose_spec
  rw [val, dif_pos ⟨hs, hz⟩]
  have hc := cross hr H.1 hz
  have h1 := H.2
  have h2 := metric_ne (A := A) hz n
  rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h1 h2)]
  linear_combination (-(A.h z : ℂ) ^ n) * hc

theorem val_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h)
    (hh : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    val y A n s z = eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
  rw [eq_div_iff (mul_ne_zero hh (metric_ne hz n)), val_spec hs hz hr]
  ring

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a n t g₂ h₂) :
    IsRep y a n (s + t) (g₁ * h₂ + g₂ * h₁) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dh₂, dh₁ + dh₂, homog_add (homog_mul hg₁ hh₂) (homog_congr (homog_mul hg₂ hh₁) fun k => ?_),
    homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    zify
    linear_combination hd₂ k - hd₁ k
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k
  · rw [map_add, map_mul, map_mul, map_mul, hy₁, hy₂]
    ring

def w (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) : chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ) :=
  AddMonoidHom.mk' (fun s => val y A n s) fun s t => by
    funext z
    show val y A n ((s + t : chartLat y A.a n) : Ω) z = val y A n s z + val y A n t z
    by_cases hz : z ∈ mcPts (mCoordIdeal y)
    · obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at s.2 hz
      obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at t.2 hz
      have hT := metric_ne (A := A) hz n
      rw [AddSubgroup.coe_add, val_eq (add_mem s.2 t.2) hz (rep_add r₁ r₂) (by simpa using mul_ne_zero n₁ n₂),
        val_eq s.2 hz r₁ n₁, val_eq t.2 hz r₂ n₂]
      simp only [map_add, map_mul]
      field_simp
    · simp [val, hz]

theorem secNormAt_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : secNormAt y A n s z = ‖val y A n s z‖ := by
  have hT : 0 < A.h z := A.pos z hz.1
  have hnT : ‖(A.h z : ℂ) ^ n‖ = A.h z ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  have hb : IsBoundedAt y A n ‖val y A n s z‖ s z := by
    intro dg dh g h hg hh hd hy
    rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT]
  refine le_antisymm (secNormAt_le (norm_nonneg _) hb) ?_
  rw [secNormAt]
  refine le_csInf ⟨_, norm_nonneg _, hb⟩ ?_
  rintro c ⟨-, hc⟩
  obtain ⟨⟨g, h⟩, ⟨dg, dh, hg, hh, hd, hy⟩, hne⟩ := exists_rep_at hs hz
  have := hc dg dh g h hg hh hd hy
  rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT, mul_assoc, mul_assoc] at this
  exact le_of_mul_le_mul_right this (mul_pos (norm_pos_iff.mpr hne) (pow_pos hT n))

theorem exists_chartData [DecidableEq K] (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω)
    (hv : ∀ j, v j ∈ chartLat y A.a m) (c : ∀ k, ι k) :
    ∃ (d e : K → ℕ) (G : Fin N → MRing ι), (∀ k, (e k : ℤ) = d k + m * A.a k) ∧
      (∀ j, IsMultiHomog (G j) e) ∧ ∀ j, aeval y (G j) = v j * aeval y (chartMon c d) :=
  exists_chartForms_of_degree y A.a m N v hv c

def blockDeg (μ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩

open Classical in

def comp (g : MRing ι) (δ : K → ℕ) : MRing ι :=
  ∑ μ ∈ g.support.filter (fun μ => blockDeg μ = δ), monomial μ (coeff μ g)

theorem homog_comp (g : MRing ι) (δ : K → ℕ) : IsMultiHomog (comp g δ) δ := by
  classical
  intro μ hμ k
  obtain ⟨ν, hν, hμν⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hμ)
  have h1 := MvPolynomial.support_monomial_subset hμν
  rw [Finset.mem_singleton] at h1
  subst h1
  exact congrFun (Finset.mem_filter.mp hν).2 k

theorem sum_comp (g : MRing ι) : ∑ δ ∈ g.support.image blockDeg, comp g δ = g := by
  classical
  unfold comp
  rw [Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem _ hμ)]
  exact g.as_sum.symm

theorem comp_eq_zero {g : MRing ι} {δ : K → ℕ} (hδ : δ ∉ g.support.image blockDeg) : comp g δ = 0 := by
  classical
  unfold comp
  refine Finset.sum_eq_zero fun μ hμ => ?_
  exact absurd (Finset.mem_image.mpr ⟨μ, (Finset.mem_filter.mp hμ).1, (Finset.mem_filter.mp hμ).2⟩) hδ

theorem prod_X_pow_eq_monomial' (δ : K → ℕ) :
    (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ δ k) = monomial (Finsupp.equivFunOnFinite.symm δ) 1 := by
  classical
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  symm
  rw [Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_]
  · rfl
  · have h1 : (Finsupp.equivFunOnFinite.symm δ) k = 0 := Finsupp.notMem_support_iff.mp hk
    rw [h1, pow_zero]

theorem comp_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) (δ : K → ℕ) :
    comp g δ ∈ mCoordIdeal y := by
  classical
  show comp g δ ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y (homog_comp g δ)]
  suffices aeval y (comp g δ) = 0 by rw [this]; simp
  by_cases hδ : δ ∈ g.support.image blockDeg
  · have h0 : mConeMap y g = 0 := hg
    rw [← sum_comp g, map_sum] at h0
    have h1 : ∀ δ' ∈ g.support.image blockDeg, mConeMap y (comp g δ') =
        MvPolynomial.C (aeval y (comp g δ')) * monomial (Finsupp.equivFunOnFinite.symm δ') 1 := fun δ' _ => by
      erw [mConeMap_homog y (homog_comp g δ'), prod_X_pow_eq_monomial']
    rw [Finset.sum_congr rfl h1] at h0
    have h2 := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm δ)) h0
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h2
    simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero,
      EmbeddingLike.apply_eq_iff_eq] at h2
    rw [Finset.sum_ite_eq' _ _ _, if_pos hδ] at h2
    exact h2
  · rw [comp_eq_zero hδ, map_zero]

theorem exists_gens (y : (Σ k, ι k) → Ω) :
    ∃ F : Finset (MRing ι × (K → ℕ)), (∀ p ∈ F, IsMultiHomog p.1 p.2 ∧ p.1 ∈ mCoordIdeal y) ∧
      mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (mCoordIdeal y) : (mCoordIdeal y).FG)
  refine ⟨s.biUnion fun g => (g.support.image blockDeg).image fun δ => (comp g δ, δ), ?_, ?_⟩
  · intro p hp
    obtain ⟨g, hg, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨homog_comp g δ, comp_mem ?_ δ⟩
    rw [← hs]
    exact Submodule.subset_span hg
  · rw [← hs]
    refine Submodule.span_le.mpr fun g hg => ?_
    rw [← sum_comp g]
    refine Ideal.sum_mem _ fun δ hδ => Ideal.subset_span ⟨(comp g δ, δ), ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image_of_mem _ hδ⟩

theorem mem_mcPts_of_gens {y : (Σ k, ι k) → Ω} {F : Finset (MRing ι × (K → ℕ))}
    (hF : mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))))
    {x : (Σ k, ι k) → ℂ} (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0)
    (h0 : ∀ p ∈ F, eval x (map (Int.castRingHom ℂ) p.1) = 0) : x ∈ mcPts (mCoordIdeal y) := by
  refine ⟨hx, fun f hf => ?_⟩
  have hle : Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))) ≤
      RingHom.ker ((eval x).comp (map (Int.castRingHom ℂ))) := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    simpa [RingHom.mem_ker] using h0 p hp
  simpa [RingHom.mem_ker] using hle (hF hf)

theorem norm_eval_rep {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a m)
    {c : ∀ k, ι k} {d e : K → ℕ} {G : MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * A.a k) (hG : IsMultiHomog G e)
    (hGy : aeval y G = s * aeval y (chartMon c d)) {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    ‖eval x (map (Int.castRingHom ℂ) G)‖ =
      secNormAt y A m s x * ‖eval x (map (Int.castRingHom ℂ) (chartMon c d))‖ * A.h x ^ m := by
  rw [secNormAt_eq hs hx, val_spec hs hx ⟨e, d, hG, homog_chartMon c d, he, hGy⟩, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg (A.pos x hx.1).le]

theorem exists_G_ne {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {d e : K → ℕ} {G : Fin N → MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * A.a k)
    (hG : ∀ j, IsMultiHomog (G j) e) (hGy : ∀ j, aeval y (G j) = v j * aeval y (chartMon c d))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 :=
  exists_eval_ne_of_generates hgen hc he hG hGy hx hxc

end SectionNormSqExtension

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
