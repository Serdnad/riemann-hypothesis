import Formalism.GradedWeylDivisibility.StatementC

/-! # Homogeneous decomposition of leading coefficients -/

section LCpeelLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcpeel_weight_apply {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    split_ifs <;> omega
  | single v k =>
    obtain ⟨a, s⟩ := v
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, Finsupp.smul_apply,
      pairW, smul_eq_mul]
    by_cases hs : s = j <;> by_cases ht : t = l <;> by_cases htj : t = j <;> by_cases hab : a = b <;>
      simp_all [Finsupp.single_apply, Prod.ext_iff, eq_comm]

end Formalism.GradedWeylDivisibility

end

end LCpeelLemmas

section PeelHomog

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcpeel_support {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) (d : Fin r × Fin n →₀ ℕ)
    (hd : coeff d (peel l j a0 k g) ≠ 0) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ d = (m.erase (a0, l)).erase (a0, j) := by
  unfold peel at hd
  rw [coeff_sum] at hd
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  refine ⟨m, hm1, hm2, ?_⟩
  rw [coeff_monomial] at hne
  split_ifs at hne with h
  · exact h.symm
  · exact absurd rfl hne

private theorem weight_single_eq_nsmul {σ M : Type*} [AddCommMonoid M] (w : σ → M) (s : σ) (c : ℕ) :
    Finsupp.weight w (Finsupp.single s c) = c • w s := by
  first
    | (rw [Finsupp.weight_apply, Finsupp.sum_single_index]; exact zero_smul ℕ (w s))
    | simp [Finsupp.weight_apply]

private theorem eq_erase_erase_add_single_add_single {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m : Fin r × Fin n →₀ ℕ) :
    m = (m.erase (a0, l)).erase (a0, j) + Finsupp.single (a0, l) (m (a0, l)) +
      Finsupp.single (a0, j) (m (a0, j)) := by
  ext ⟨b, t⟩
  simp only [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases hb : b = a0
  · subst hb
    by_cases hl : t = l
    · subst hl
      simp [hlj, Ne.symm hlj]
    · by_cases hj : t = j
      · subst hj
        simp [hl, Ne.symm hl]
      · simp [hl, hj, Ne.symm hl, Ne.symm hj]
  · simp [hb, Ne.symm hb]

private theorem weight_pairW_apply_eq_zero_of_vanish {r n : ℕ} (l j : Fin n) (a0 : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (hl : d (a0, l) = 0) (hj : d (a0, j) = 0) :
    Finsupp.weight (pairW l j) d (a0, l) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  dsimp only
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  obtain ⟨b, t⟩ := i
  by_cases ht : t = j
  · have hne : ¬ ((b, l) = (a0, l)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rw [h.1, ht] at hi0
      exact hi0 hj
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, l) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
  · have hne : ¬ ((b, t) = (a0, l)) := by
      intro h
      rw [h] at hi0
      exact hi0 hl
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, t) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]

private theorem weight_pairW_eq_erase_of_split {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m d ω : Fin r × Fin n →₀ ℕ) (hdl : d (a0, l) = 0) (hdj : d (a0, j) = 0)
    (hsplit : m = d + Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (m (a0, j)))
    (hw : Finsupp.weight (pairW l j) m = ω) :
    Finsupp.weight (pairW l j) d = ω.erase (a0, l) := by
  have hpl : pairW (r := r) l j (a0, l) = Finsupp.single (a0, l) 1 := by
    simp [pairW, hlj]
  have hpj : pairW (r := r) l j (a0, j) = Finsupp.single (a0, l) 1 := by
    simp [pairW]
  have key : ω = Finsupp.weight (pairW l j) d +
      Finsupp.single (a0, l) (m (a0, l) + m (a0, j)) := by
    rw [← hw]
    conv_lhs => rw [hsplit]
    rw [map_add, map_add, weight_single_eq_nsmul, weight_single_eq_nsmul, hpl, hpj]
    first
      | (rw [add_assoc, ← add_smul, Finsupp.smul_single, smul_eq_mul, mul_one])
      | (ext y
         simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
         split_ifs <;> ring)
  ext x
  by_cases hx : x = (a0, l)
  · rw [hx, Finsupp.erase_same]
    exact weight_pairW_apply_eq_zero_of_vanish l j a0 d hdl hdj
  · rw [Finsupp.erase_ne hx, key, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hx),
      add_zero]

theorem sliceHomogeneous : PeelHomog := by
  intro B _ r n l j hlj a0 ω k g hg
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨m, hm, -, rfl⟩ := lcpeel_support l j a0 k g d hd
    exact weight_pairW_eq_erase_of_split l j hlj a0 m _ ω
      (by simp [Finsupp.erase_apply, hlj]) (by simp [Finsupp.erase_apply])
      (eq_erase_erase_add_single_add_single l j hlj a0 m) (hg (mem_support_iff.mp hm))
  · intro d hd
    obtain ⟨m, -, -, rfl⟩ :=
      lcpeel_support l j a0 k g d (mem_support_iff.mp hd)
    exact ⟨by simp [Finsupp.erase_apply, hlj], by simp [Finsupp.erase_apply]⟩

end Formalism.GradedWeylDivisibility

end

end PeelHomog

section PeelDecomp

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem peelDecomposition : PeelDecomp := by
  intro B _ r n l j hlj a0 ω g hg
  have key : ∀ m ∈ g.support, m (a0, l) + m (a0, j) = ω (a0, l) := by
    intro m hm
    have hw := hg (mem_support_iff.1 hm)
    have := lcpeel_weight_apply l j hlj m a0 l
    rw [hw] at this
    simpa using this.symm
  have hterm : ∀ k, X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g =
      ∑ m ∈ g.support.filter (fun m => m (a0, l) = k), monomial m (coeff m g) := by
    intro k
    unfold peel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have hkey := key m hm1
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul]
    refine congrArg (fun e => monomial e (coeff m g)) ?_
    ext ⟨b, t⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply, Prod.mk.injEq]
    rcases eq_or_ne b a0 with rfl | hb
    · rcases eq_or_ne t l with rfl | ht
      · simp only [hlj, hlj.symm, and_true, and_false, if_true, if_false]
        omega
      · rcases eq_or_ne t j with rfl | ht'
        · simp only [ht, Ne.symm ht, and_true, and_false, if_true, if_false]
          omega
        · simp [ht, ht', Ne.symm ht, Ne.symm ht']
    · simp [hb, Ne.symm hb]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hmaps : ∀ m ∈ g.support, (fun m : Fin r × Fin n →₀ ℕ => m (a0, l)) m ∈ Finset.range (ω (a0, l) + 1) := by
    intro m hm
    have := key m hm
    show m (a0, l) ∈ _
    rw [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun m => monomial m (coeff m g))
  exact (hfib.trans (as_sum g).symm).symm

end Formalism.GradedWeylDivisibility

end

end PeelDecomp
