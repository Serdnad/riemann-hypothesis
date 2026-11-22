import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.ChartForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst this
  simp

omit [Fintype K] in

theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e :=
  SectionNormSqExtension.homog_chartMon c e

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k :=
  SectionNormSqExtension.exists_form_of_mem_chartRingZ y c hc hx

theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => SectionNormSqExtension.y_ne_zero hz (hc k)
  obtain ⟨N, D, G, hg, hdeg, hval⟩ := SectionNormSqExtension.exists_chartForm y c hy
    (fun k => (n : ℤ) * a k) (hs c hy)
  refine ⟨D, N, G, SectionNormSqExtension.chartMon c N, hg, SectionNormSqExtension.homog_chartMon c N,
    fun k => (hdeg k).trans (add_comm _ _), ?_, ?_⟩
  · simpa only [SectionNormSqExtension.aeval_chartMon] using hval
  · rw [SectionNormSqExtension.eval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
