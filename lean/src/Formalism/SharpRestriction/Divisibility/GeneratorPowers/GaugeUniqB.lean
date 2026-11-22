import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

namespace GaugeR

variable {R ι : Type} [CommRing R]

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree :=
  GermD.monomial_mem_orig_pow e a

theorem mem_orig_pow_of_coeff (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → coeff e p = 0) :
    p ∈ orig R ι ^ n :=
  (MvPolynomial.mem_pow_idealOfVars_iff' n p).2 h

variable [Fintype ι] [DecidableEq ι]

theorem psJet_eq_mk (m : ℕ) (f : MvPowerSeries ι R) (p : MvPolynomial ι R)
    (h : ∀ e, e.degree ≤ m → coeff e p = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of_coeff
  intro e he
  rw [coeff_sub, GermFun.coeff_psTrunc m f e (by omega), h e (by omega), sub_self]

theorem psJet_mul (m : ℕ) (f g : MvPowerSeries ι R) : psJet m (f * g) = psJet m f * psJet m g :=
  FBIdJet.psJet_mul m f g

theorem psJet_one (m : ℕ) : psJet m (1 : MvPowerSeries ι R) = 1 :=
  FBIdJet.psJet_one m

theorem psJet_pow (m : ℕ) (f : MvPowerSeries ι R) (k : ℕ) : psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, psJet_one]
  | succ k ih => rw [pow_succ, pow_succ, psJet_mul, ih]

theorem aeval_scale_monomial (s : ι → R) (e : ι →₀ ℕ) (a : R) :
    aeval (fun i => C (s i) * X i) (monomial e a : MvPolynomial ι R) =
      monomial e (a * e.prod fun i k => s i ^ k) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [map_mul, map_finsuppProd, MvPolynomial.algebraMap_eq]
  ring

theorem coeff_aeval_scale (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    coeff e (aeval (fun i => C (s i) * X i) p) = (e.prod fun i k => s i ^ k) * coeff e p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e' a =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem jetMap_mk {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetSubstP_scale (m : ℕ) (s : ι → R) (f : MvPowerSeries ι R) :
    jetSubstP m (fun i => C (s i) * X i) (psJet m f) = psJet m (MvPowerSeries.rescale s f) := by
  unfold jetSubstP psJet
  rw [jetMap_mk]
  simp only [map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_zero, sub_zero]
  symm
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  rw [coeff_aeval_scale, GermFun.coeff_psTrunc m f e he, MvPowerSeries.coeff_rescale]

theorem jetTrunc_psJet (m : ℕ) (f : MvPowerSeries ι R) : jetTrunc (psJet (m + 1) f) = psJet m f := by
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = psJet m f
  exact (psJet_eq_mk m f _ (fun e he => GermFun.coeff_psTrunc (m + 1) f e (by omega))).symm

theorem jetAug_psJet (m : ℕ) (f : MvPowerSeries ι R) :
    jetAug (psJet m f) = MvPowerSeries.constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (psTrunc m f) = _
  rw [show (fun _ : ι => (0 : R)) = 0 from rfl, MvPolynomial.aeval_zero, Algebra.algebraMap_self_apply,
]
  show MvPolynomial.coeff 0 (psTrunc m f) = _
  rw [GermFun.coeff_psTrunc m f 0 (by simp)]
  rfl

theorem exists_ps_of_compat (ρ : ∀ m, Jet R ι m) (h : ∀ m, jetTrunc (ρ (m + 1)) = ρ m) :
    ∃ r : MvPowerSeries ι R, ∀ m, psJet m r = ρ m :=
  GermD.exists_ps_of_jets ρ h

-- Retain the arithmetic lemmas exported by the original jet proofs.
theorem psJet_mul._proof_1_1 {ι : Type} (m : ℕ) (e : ι →₀ ℕ)
    (x : (ι →₀ ℕ) × (ι →₀ ℕ)) (hd : Finsupp.degree x.1 + Finsupp.degree x.2 ≤ m) :
    (¬ Finsupp.degree x.1 ≤ m) → False :=
  fun h => h ((Nat.le_add_right _ _).trans hd)

theorem psJet_mul._proof_1_2 {ι : Type} (m : ℕ) (e : ι →₀ ℕ)
    (x : (ι →₀ ℕ) × (ι →₀ ℕ)) (hd : Finsupp.degree x.1 + Finsupp.degree x.2 ≤ m) :
    (¬ Finsupp.degree x.2 ≤ m) → False :=
  fun h => h ((Nat.le_add_left _ _).trans hd)

theorem exists_ps_of_compat._proof_1_1 {ι : Type} (n : ℕ) (e : ι →₀ ℕ)
    (he : Finsupp.degree e ≤ n) (k : ℕ) : (¬ Finsupp.degree e < n + k + 1) → False :=
  fun h => h (Nat.lt_succ_of_le (Nat.le_add_right_of_le he))

theorem exists_ps_of_compat._proof_1_2 {ι : Type} (m : ℕ) (e : ι →₀ ℕ)
    (he : Finsupp.degree e ≤ m) : (¬ Finsupp.degree e + (m - Finsupp.degree e) = m) → False :=
  fun h => h (Nat.add_sub_of_le he)

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
