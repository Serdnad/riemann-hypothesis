import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem homog_congr {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : ∀ k, a k = b k) :
    IsMultiHomog f b :=
  fun m hm k => (hf m hm k).trans (h k)

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := fun m hm => by simp at hm

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hf m hm
  · exact hg m hm

theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a :=
  fun m hm => hf m (by rwa [support_neg] at hm)

theorem homog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact homog_add hf (homog_neg hg)

theorem homog_sum {J : Type} (s : Finset J) {f : J → MRing ι} {a : K → ℕ}
    (h : ∀ j ∈ s, IsMultiHomog (f j) a) : IsMultiHomog (∑ j ∈ s, f j) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero (ι := ι) a
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact homog_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem homog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  obtain ⟨k, i⟩ := p
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    rw [Pi.single_eq_same, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hb (eq_of_heq (Sigma.mk.inj_iff.mp e).2).symm
    · simp
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (congrArg Sigma.fst e).symm

theorem homog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

def chartMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem homog_chartMon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMon c d) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X ⟨k, c k⟩) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rw [e] at this
  exact this

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod]

theorem eval_chartMon (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod]

theorem mConeMap_homog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem vanish {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g : MRing ι}
    {d : K → ℕ} (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : eval z (map (Int.castRingHom ℂ) g) = 0 := by
  refine hz.2 g ?_
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y hg, h0]
  simp

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, homog_X p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, homog_C r, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * chartMon c δ₂ + e₂ * chartMon c δ₁,
      homog_add (homog_mul h₁ (homog_chartMon c δ₂)) ?_, ?_⟩
    · rw [add_comm δ₁]
      exact homog_mul h₂ (homog_chartMon c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMon, aeval_chartMon, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, homog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : K → ℤ) {t : Ω}
    (ht : t * ∏ k, y ⟨k, c k⟩ ^ (-e k) ∈ chartRingZ y c) :
    ∃ (N δ : K → ℕ) (G : MRing ι), IsMultiHomog G δ ∧ (∀ k, (δ k : ℤ) = e k + N k) ∧
      aeval y G = t * ∏ k, y ⟨k, c k⟩ ^ N k := by
  obtain ⟨δ', G', hG', hv'⟩ := exists_form_of_mem_chartRingZ y c hc ht
  refine ⟨fun k => δ' k + (e k).natAbs, fun k => δ' k + (e k + (e k).natAbs).toNat,
    G' * chartMon c (fun k => (e k + (e k).natAbs).toNat), ?_, fun k => ?_, ?_⟩
  · exact homog_congr (homog_mul hG' (homog_chartMon c _)) fun k => rfl
  · dsimp only
    omega
  · rw [map_mul, hv', aeval_chartMon, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    omega

theorem y_ne_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {p : Σ k, ι k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hX : (X p : MRing ι) ∈ mCoordIdeal y := by
    show X p ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hz.2 _ hX

theorem exists_chartForms_of_degree (y : (Σ k, ι k) → Ω) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω)
    (hv : ∀ j, v j ∈ chartLat y a m) (c : ∀ k, ι k) :
    ∃ (d e : K → ℕ) (G : Fin N → MRing ι), (∀ k, (e k : ℤ) = d k + m * a k) ∧
      (∀ j, IsMultiHomog (G j) e) ∧ ∀ j, aeval y (G j) = v j * aeval y (chartMon c d) := by
  classical
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose Nn δ G hG hdeg hGv using fun j =>
      exists_chartForm y c hc (fun k => (m : ℤ) * a k) (hv j c hc)
    have hN : ∀ j k, Nn j k ≤ ∑ i, Nn i k := fun j k =>
      Finset.single_le_sum (f := fun i => Nn i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    set L : K → ℕ := fun k => ∑ i, Nn i k + ((m : ℤ) * a k).natAbs with hL
    refine ⟨L, fun k => ((L k : ℤ) + m * a k).toNat, fun j => G j * chartMon c (L - Nn j), fun k => ?_,
      fun j => homog_congr (homog_mul (hG j) (homog_chartMon c _)) fun k => ?_, fun j => ?_⟩
    · simp only [hL]
      generalize ∑ i, Nn i k = S
      generalize (m : ℤ) * a k = q
      omega
    · have h1 := hdeg j k
      have h2 := hN j k
      simp only [Pi.add_apply, Pi.sub_apply, hL]
      generalize (m : ℤ) * a k = q at *
      generalize ∑ i, Nn i k = S at *
      omega
    · rw [map_mul, hGv j, aeval_chartMon, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_add, Pi.sub_apply]
      congr 1
      have h2 := hN j k
      simp only [hL]
      omega
  · push Not at hc
    obtain ⟨k0, hk0⟩ := hc
    refine ⟨fun k => 1 + ((m : ℤ) * a k).natAbs, fun k => (((1 + ((m : ℤ) * a k).natAbs : ℕ) : ℤ) +
      m * a k).toNat, fun _ => 0, fun k => ?_, fun _ => homog_zero _, fun j => ?_⟩
    · dsimp only
      generalize (m : ℤ) * a k = q
      omega
    · rw [aeval_chartMon, Finset.prod_eq_zero (Finset.mem_univ k0) (by rw [hk0]; simp)]
      simp

theorem exists_eval_ne_of_generates {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N : ℕ} {v : Fin N → Ω}
    (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * a k) v) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {d e : K → ℕ} {G : Fin N → MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * a k)
    (hG : ∀ j, IsMultiHomog (G j) e) (hGy : ∀ j, aeval y (G j) = v j * aeval y (chartMon c d))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 := by
  obtain ⟨u, hu, hsum⟩ := hgen c hc
  simp only [] at hsum
  choose δ U hU hUy using fun j => exists_form_of_mem_chartRingZ y c hc (hu j)
  have hδ : ∀ j k, δ j k ≤ ∑ i, δ i k := fun j k =>
    Finset.single_le_sum (f := fun i => δ i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set L : K → ℕ := fun k => ∑ i, δ i k with hL
  set F : MRing ι := ∑ j, U j * chartMon c (L - δ j) * G j - chartMon c (L + e) with hF
  have hFh : IsMultiHomog F (L + e) := by
    refine homog_sub (homog_sum _ fun j _ => homog_congr (homog_mul (homog_mul (hU j) (homog_chartMon c _))
      (hG j)) fun k => ?_) (homog_chartMon c _)
    have := hδ j k
    simp only [Pi.add_apply, Pi.sub_apply, hL] at this ⊢
    omega
  have hpow : ∀ k, y ⟨k, c k⟩ ^ (L k + e k) * y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)) =
      y ⟨k, c k⟩ ^ (L k + d k) := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    push_cast
    linarith [he k]
  have e1 : ∀ j, aeval y (U j * chartMon c (L - δ j) * G j) =
      (u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)))) * ∏ k, y ⟨k, c k⟩ ^ (L k + e k) := by
    intro j
    rw [map_mul, map_mul, hUy j, hGy j, aeval_chartMon, aeval_chartMon]
    have h3 : ∀ k, y ⟨k, c k⟩ ^ δ j k * y ⟨k, c k⟩ ^ (L - δ j) k * y ⟨k, c k⟩ ^ d k =
        y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)) * y ⟨k, c k⟩ ^ (L k + e k) := by
      intro k
      rw [mul_comm (y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))), hpow k, ← pow_add, ← pow_add]
      congr 1
      have := hδ j k
      simp only [Pi.sub_apply, hL] at this ⊢
      omega
    calc _ = u j * v j * ∏ k, (y ⟨k, c k⟩ ^ δ j k * y ⟨k, c k⟩ ^ (L - δ j) k * y ⟨k, c k⟩ ^ d k) := by
          simp only [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          rw [Finset.prod_congr rfl fun k _ => h3 k, Finset.prod_mul_distrib]
          ring
  have hFy : aeval y F = 0 := by
    rw [hF, map_sub, map_sum, Finset.sum_congr rfl fun j _ => e1 j, ← Finset.sum_mul, hsum, one_mul,
      aeval_chartMon]
    simp only [Pi.add_apply, sub_self]
  have hFx := vanish hx hFh hFy
  by_contra hne
  push Not at hne
  rw [hF] at hFx
  simp only [map_sub, map_sum, map_mul, hne, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero,
    eval_chartMon] at hFx
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hxc k)) hFx

end SectionNormSqExtension

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
