import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

/-! # Laurent monomial bases for Čech terms -/

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/-- A finite family of Laurent monomials has a common denominator. -/
theorem exists_common_laurent_numerators {ι κ : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ]
    (s : Finset ι) (a : κ → ι → ℤ) (ha : ∀ j i, i ∉ s → 0 ≤ a j i) :
    ∃ (k : ℕ) (m : κ → ι →₀ ℕ), ∀ j i, (m j i : ℤ) = a j i + if i ∈ s then (k : ℤ) else 0 := by
  let k := Finset.univ.sup fun j => Finset.univ.sup fun i => (a j i).natAbs
  refine ⟨k, fun j => Finsupp.equivFunOnFinite.symm
    (fun i => (a j i + if i ∈ s then (k : ℤ) else 0).toNat), fun j i => Int.toNat_of_nonneg ?_⟩
  by_cases hi : i ∈ s
  · have hk : (a j i).natAbs ≤ k :=
      (Finset.le_sup (f := fun i => (a j i).natAbs) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun j => Finset.univ.sup fun i => (a j i).natAbs) (Finset.mem_univ j))
    rw [if_pos hi]
    omega
  · simpa [hi] using ha j i hi

theorem exists_laurent_numerator {ι : Type} [DecidableEq ι] [Fintype ι] (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, i ∉ s → 0 ≤ a i) :
    ∃ (k : ℕ) (m : ι →₀ ℕ), ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0 := by
  obtain ⟨k, m, hm⟩ := exists_common_laurent_numerators s (fun _ : Unit => a) (fun _ => ha)
  exact ⟨k, m (), hm ()⟩

theorem linearIndependent_laurentMonomial :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ) (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → LocalizedModule.Away (xProd R s) (MvPolynomial ι R)), (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) → v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) → LinearIndependent R v := by
  intro ι _ _ R _ s n v hv
  rw [linearIndependent_iff_finset_linearIndependent]
  intro T
  obtain ⟨k, m, hm⟩ :=
    exists_common_laurent_numerators s (fun a : T => a.1.1) (fun a => a.1.2.2)
  have hinj : Function.Injective m := by
    intro a b e
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simpa only [hm, add_left_inj] using congrArg (fun d : ι →₀ ℕ => (d i : ℤ)) e
  let F := (awayFrac (MvPolynomial ι R) (xProd R s) k).restrictScalars R
  have hF : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot.mpr
    (awayFrac_injective (xProd_smul_injective s) k)
  have hrestrict : v ∘ (Subtype.val : T → _) = F ∘ (MvPolynomial.basisMonomials ι R) ∘ m :=
    funext fun a => hv a.1 k (m a) (hm a)
  rw [hrestrict]
  exact ((MvPolynomial.basisMonomials ι R).linearIndependent.comp m hinj).map' F hF

end GlobalTheory

end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem span_laurentMonomial_eq_homLoc :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ)
      (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} →
        LocalizedModule.Away (xProd R s) (MvPolynomial ι R)),
      (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) →
      Submodule.span R (Set.range v) = homLoc (polyGrading ι R) s n := by
  intro ι _ _ R _ s n v hv
  have hsum (k : ℤ) : ∑ i, (if i ∈ s then k else 0) = k * s.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hdeg (m : ι →₀ ℕ) : ((m.degree : ℕ) : ℤ) = ∑ i, (m i : ℤ) := by
    rw [Finsupp.degree_eq_sum]; push_cast; rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨k, m, hm⟩ := exists_laurent_numerator s a.1 a.2.2
    rw [hv a k m hm]
    refine awayFrac_mem_homLoc (monomial_mem_polyGrading m 1) ?_
    rw [hdeg, Finset.sum_congr rfl fun i _ => hm i, Finset.sum_add_distrib, a.2.1, hsum]
  · rintro _ ⟨k, p, hp, rfl⟩
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hd := mem_polyGrading_iff.1 hp m (mem_support_iff.1 hm)
    have e : monomial m (coeff m p) = coeff m p • (monomial m 1 : MvPolynomial ι R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul_of_tower]
    refine Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨fun i => m i - if i ∈ s then (k : ℤ) else 0, ?_, fun i hi => ?_⟩, hv _ k m fun i => ?_⟩)
    · rw [Finset.sum_sub_distrib, hsum, ← hdeg, hd, add_sub_cancel_right]
    · simp [hi]
    · simp

end GlobalTheory

end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_xProd_pow_smul_monomial {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (j : ℕ) (m : ι →₀ ℕ) :
    ∃ m' : ι →₀ ℕ, (∀ i, m' i = m i + if i ∈ s then j else 0) ∧
      xProd R s ^ j • (monomial m 1 : MvPolynomial ι R) = monomial m' 1 := by
  refine ⟨m + ∑ i ∈ s, Finsupp.single i j, fun i => ?_, ?_⟩
  · simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  · rw [smul_eq_mul, xProd, ← Finset.prod_pow, add_comm]
    simp only [X_pow_eq_monomial]
    rw [← monomial_sum_one, monomial_mul, one_mul]

theorem awayFrac_monomial_congr {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (a : ι → ℤ) {k j : ℕ} {m m' : ι →₀ ℕ}
    (hm : ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0)
    (hm' : ∀ i, (m' i : ℤ) = a i + if i ∈ s then (j : ℤ) else 0) :
    awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) =
      awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) := by
  refine awayFrac_eq_iff.2 ⟨0, ?_⟩
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R s (0 + j) m
  obtain ⟨w, hw, ew⟩ := exists_xProd_pow_smul_monomial R s (0 + k) m'
  rw [eu, ew]
  congr 2
  ext i
  have h1 := hu i
  have h2 := hw i
  have h3 := hm i
  have h4 := hm' i
  split_ifs at h1 h2 h3 h4 <;> omega

theorem exists_basis_grCube_polyGrading :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), ∃ b : ∀ s : Finset ι, Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R ((grCube ι (polyGrading ι R) n).obj s), ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s}), Cube.res (grCube ι (polyGrading ι R) n) h (b s a) = b t ⟨a.1, a.2.trans h⟩ := by
  intro ι _ _ R _ n
  have hiff : ∀ (s : Finset ι) (a : ι → ℤ),
      Finset.univ.filter (fun i => a i < 0) ⊆ s ↔ ∀ i, i ∉ s → 0 ≤ a i := by
    intro s a
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' fun i => by rw [← not_lt]; exact not_imp_not.symm
  have key : ∀ s : Finset ι, ∃ b : Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} //
      Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R (homLoc (polyGrading ι R) s n),
      ∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1.1 i + if i ∈ s then (k : ℤ) else 0) →
        (b a).1 = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) := by
    intro s
    choose k m hm using fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
      exists_laurent_numerator s a.1 a.2.2
    let v := fun a => awayFrac (MvPolynomial ι R) (xProd R s) (k a) (monomial (m a) 1)
    have hv : ∀ a (j : ℕ) (m' : ι →₀ ℕ),
        (∀ i, (m' i : ℤ) = a.1 i + if i ∈ s then (j : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) :=
      fun a j m' h => awayFrac_monomial_congr R s a.1 (hm a) h
    let e : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} ≃
        {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} :=
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, (hiff s a.1).2 a.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, (hiff s a.1.1).1 a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine ⟨((Module.Basis.span (linearIndependent_laurentMonomial ι R s n v hv)).map
      (LinearEquiv.ofEq _ _ (span_laurentMonomial_eq_homLoc ι R s n v hv))).reindex e, fun a j m' h => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      Module.Basis.span_apply]
    exact hv _ j m' h
  choose b hb using key
  refine ⟨b, fun s t h a => Subtype.ext ?_⟩
  obtain ⟨k, m, hm⟩ := exists_laurent_numerator s a.1.1 ((hiff s _).1 a.2)
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R (t \ s) k m
  change locRes X (MvPolynomial ι R) h (b s a).1 = (b t ⟨a.1, a.2.trans h⟩).1
  rw [hb s a k m hm, locRes_awayFrac X h (Finset.prod_sdiff h).symm, eu]
  refine (hb t _ k u fun i => ?_).symm
  have h1 := hu i
  have h2 := hm i
  have h3 := @h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

end GlobalTheory
