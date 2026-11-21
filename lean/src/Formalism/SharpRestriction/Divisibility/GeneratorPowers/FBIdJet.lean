import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

variable {R : Type} [CommRing R]

theorem psTrunc_eq {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) :
    psTrunc m f = MvPowerSeries.truncTotal (m + 1) f := by
  ext e
  have hle : ∀ i, e i ≤ e.degree := fun i => by
    first
    | exact Finsupp.le_degree i e
    | exact Finsupp.le_degree e i
    | (by_cases hi : e i = 0
       · omega
       · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
           (Finsupp.mem_support_iff.2 hi))
  have hdeg : (e.sum fun _ k => k) = e.degree := by
    first
    | rfl
    | simp [Finsupp.degree, Finsupp.sum]
  have hmem : e ∈ degLE m ↔ e.degree < m + 1 := by
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      omega
    · intro h
      refine ⟨⟨fun i => ⟨e i, by have := hle i; omega⟩, ?_⟩, by omega⟩
      ext i
      simp
  have hL : MvPolynomial.coeff e (psTrunc m f) =
      if e ∈ degLE m then MvPowerSeries.coeff e f else 0 := by
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    first
    | exact Finset.sum_ite_eq' (degLE m) e (fun x => MvPowerSeries.coeff x f)
    | exact Finset.sum_ite_eq (degLE m) e (fun x => MvPowerSeries.coeff x f)
    | simp
  rw [hL]
  by_cases h : e.degree < m + 1
  · rw [if_pos (hmem.2 h), MvPowerSeries.coeff_truncTotal]
    exact h
  · rw [if_neg (fun h' => h (hmem.1 h'))]
    first
    | exact (MvPowerSeries.coeff_truncTotal_eq_zero (by omega)).symm
    | exact (MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)).symm
    | (rw [MvPowerSeries.coeff_truncTotal_eq_zero]; omega)
    | exact (MvPowerSeries.coeff_truncTotal_of_le (by omega)).symm
    | simp [MvPowerSeries.truncTotal, MvPowerSeries.truncTotalFun, MvPolynomial.coeff_sum, h]
    | (simp [MvPowerSeries.truncTotal, h]; done)

theorem mk_trunc_coe {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (P : MvPolynomial ι R) :
    (Ideal.Quotient.mk (orig R ι ^ (m + 1))
      (MvPowerSeries.truncTotal (m + 1) (P : MvPowerSeries ι R))) = Ideal.Quotient.mk _ P :=
  (MvPowerSeries.truncTotalAlgHom ι R (m + 1)).commutes P

theorem psJet_mul {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f g : MvPowerSeries ι R) :
    psJet m (f * g) = psJet m f * psJet m g := by
  unfold psJet
  simp only [psTrunc_eq]
  exact map_mul (MvPowerSeries.truncTotalAlgHom ι R (m + 1)) f g

theorem psJet_one {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    psJet m (1 : MvPowerSeries ι R) = 1 := by
  unfold psJet
  simp only [psTrunc_eq]
  exact map_one (MvPowerSeries.truncTotalAlgHom ι R (m + 1))

theorem psTrunc_mem_orig {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (g : MvPowerSeries τ R)
    (hg : MvPowerSeries.constantCoeff g = 0) : psTrunc m g ∈ orig R τ := by
  unfold psTrunc
  refine Ideal.sum_mem _ fun e _ => ?_
  by_cases he : e = 0
  · subst he
    first
    | simp [hg]
    | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, map_zero]; exact Ideal.zero_mem _)
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext fun j => by simp [h j])
    have key : MvPolynomial.monomial e (MvPowerSeries.coeff e g) =
        MvPolynomial.monomial (e - Finsupp.single i 1) (MvPowerSeries.coeff e g) *
          MvPolynomial.X i := by
      have hs : e - Finsupp.single i 1 + Finsupp.single i 1 = e := by
        ext j
        by_cases h : j = i
        · subst h
          first
          | (simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]; omega)
          | (simp [Finsupp.single_apply]; omega)
          | simp [Finsupp.single_apply]
        · first
          | (simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h)]; omega)
          | simp [Finsupp.single_apply, h, Ne.symm h]
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, hs]
    rw [key]
    refine Ideal.mul_mem_left _ _ ?_
    first
    | exact Ideal.subset_span ⟨i, rfl⟩
    | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩)

theorem aeval_coe_comp {σ τ : Type} (A : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => (A i : MvPowerSeries τ R)) P =
      ((MvPolynomial.aeval A P : MvPolynomial τ R) : MvPowerSeries τ R) := by
  simpa using (MvPolynomial.comp_aeval_apply
    (MvPolynomial.coeToMvPowerSeries.algHom (R := R) (σ := τ) R) (f := A) P).symm

/-- Truncating the series and all substituted variables gives the same jet. -/
theorem psJet_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (m : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) :
    psJet m (MvPowerSeries.subst a f) =
      jetMap (fun i => psTrunc m (a i)) (fun i => psTrunc_mem_orig m (a i) (ha i)) (psJet m f) := by
  change Ideal.Quotient.mk _ (psTrunc m (MvPowerSeries.subst a f)) =
    Ideal.Quotient.mk _ (MvPolynomial.aeval (fun i => psTrunc m (a i)) (psTrunc m f))
  simp only [psTrunc_eq]
  rw [MvPowerSeries.truncTotal_subst ha, MvPowerSeries.subst_coe, aeval_coe_comp, mk_trunc_coe]

-- Retain arithmetic lemmas exported by the original proofs.
section TruncationProofCompatibility

local notation "degreeZero" =>
  @OfNat.ofNat ℕ (nat_lit 0) (@Zero.toOfNat0 ℕ (@AddZero.toZero ℕ
    (@AddZeroClass.toAddZero ℕ (@AddMonoid.toAddZeroClass ℕ
      (@AddCommMonoid.toAddMonoid ℕ Nat.instAddCommMonoid)))))

theorem psJet_mul._proof_1_1 {ι : Type} (m : ℕ) (e : ι →₀ ℕ)
    (he : Finsupp.degree e < m + 1) : (¬ Finsupp.degree e < 0 + (m + 1)) → False :=
  fun h => h (by simpa only [zero_add] using he)

theorem psJet_subst._proof_1_1 {τ : Type} (e : τ →₀ ℕ)
    (he : Finsupp.degree e < 1) : (¬ Finsupp.degree e = degreeZero) → False :=
  fun h => h (Nat.lt_one_iff.mp he)

theorem psJet_subst._proof_1_2 {σ τ : Type} (m : ℕ) (e : τ →₀ ℕ)
    (he : Finsupp.degree e < m + 1) (d : σ →₀ ℕ) (hd : ¬ Finsupp.degree d < m + 1) :
    (¬ Finsupp.degree e < Finsupp.degree d) → False :=
  fun h => h (lt_of_lt_of_le he (Nat.le_of_not_gt hd))

end TruncationProofCompatibility

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
