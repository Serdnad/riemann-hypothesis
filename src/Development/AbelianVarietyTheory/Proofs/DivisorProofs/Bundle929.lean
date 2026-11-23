module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle875
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898

@[expose] public section

section

open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordSpread

open KaehlerDifferential TensorProduct

theorem fibre_bijective (B K : Type) [CommRing B] [Field K] [Algebra B K] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (d : ℕ) (v : Fin d → M)
    (hd : Module.finrank K (K ⊗[B] M) = d)
    (hli : LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] v a)) :
    Function.Bijective (Finsupp.linearCombination (RingHom.ker (algebraMap B K)).ResidueField
      (fun a => (1 : (RingHom.ker (algebraMap B K)).ResidueField) ⊗ₜ[B] v a)) := by
  classical
  set p := RingHom.ker (algebraMap B K) with hp
  let φ : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap B K) le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h => hx (RingHom.mem_ker.2 h))
  letI : Algebra p.ResidueField K := φ.toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  let e := AlgebraTensorModule.cancelBaseChange B p.ResidueField K K M
  have he : ∀ a, e ((1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a)) = (1 : K) ⊗ₜ[B] v a :=
    fun a => by simp [e, AlgebraTensorModule.cancelBaseChange_tmul]
  have hfun : (e.symm.toLinearMap ∘ fun a => (1 : K) ⊗ₜ[B] v a) =
      fun a => (1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a) := by
    funext a
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq, he]
  have hli2 : LinearIndependent K (fun a => (1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a)) :=
    hfun ▸ hli.map' e.symm.toLinearMap (LinearEquiv.ker _)
  have hli3 : LinearIndependent p.ResidueField (fun a => (1 : p.ResidueField) ⊗ₜ[B] v a) := by
    haveI : FaithfulSMul p.ResidueField K := (faithfulSMul_iff_algebraMap_injective _ K).2 φ.injective
    exact LinearIndependent.of_comp (TensorProduct.mk p.ResidueField K (p.ResidueField ⊗[B] M) 1)
      (hli2.restrict_scalars' p.ResidueField)
  have hdim : Module.finrank p.ResidueField (p.ResidueField ⊗[B] M) = d := by
    rw [← hd, ← e.finrank_eq]
    exact (Module.finrank_baseChange (R := K) (S := p.ResidueField) (M' := p.ResidueField ⊗[B] M)).symm
  refine ⟨hli3, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_finsupp_self, Fintype.card_fin]; exact hdim.symm)]
  exact hli3

theorem exists_away_etale : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  intro R B K _ _ _ _ _ _ d t hd hli
  classical
  have hbij := fibre_bijective B K Ω[B⁄R] d (fun a => D R B (t a)) hd hli
  obtain ⟨g, hg, hspan, hrel⟩ := GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective B
    Ω[B⁄R] (Fin d) (fun a => D R B (t a)) (RingHom.ker (algebraMap B K)) hbij
  refine ⟨g, fun h0 => hg (RingHom.mem_ker.2 h0), ?_⟩
  let A := Localization.Away g
  haveI : Algebra.Smooth B A := Algebra.Smooth.of_isLocalization_Away g
  haveI : Algebra.Smooth R A := Algebra.Smooth.comp R B A
  let f := KaehlerDifferential.map R R B A
  haveI : IsLocalizedModule (Submonoid.powers g) f :=
    KaehlerDifferential.isLocalizedModule_map R B A (Submonoid.powers g)
  let w : Fin d → Ω[A⁄R] := fun a => D R A (algebraMap B A (t a))
  have hfw : ∀ a, f (D R B (t a)) = w a := fun a => KaehlerDifferential.map_D R R B A (t a)
  have hunit : ∀ s ∈ Submonoid.powers g, IsUnit (algebraMap B A s) := fun s hs =>
    IsLocalization.map_units A (⟨s, hs⟩ : Submonoid.powers g)
  have hsB : ∀ (s : B) (y : Ω[A⁄R]), s • y = algebraMap B A s • y := fun s y =>
    (algebraMap_smul A s y).symm

  have hsp : ⊤ ≤ Submodule.span A (Set.range w) := by
    intro y _
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj (Submonoid.powers g) f y
    obtain ⟨n, c, hc⟩ := hspan x
    have h1 : ((g ^ n * s : B)) • y = Finsupp.linearCombination B (f ∘ fun a => D R B (t a)) c := by
      rw [mul_smul, Submonoid.smul_def] at *
      simp only at hxs
      rw [hxs, ← map_smul, hc, Finsupp.apply_linearCombination]
    have h2 : ((g ^ n * s : B)) • y ∈ Submodule.span A (Set.range w) := by
      rw [h1]
      refine Submodule.span_le_restrictScalars B A _ ?_
      rw [Finsupp.mem_span_range_iff_exists_finsupp]
      refine ⟨c, ?_⟩
      rw [Finsupp.linearCombination_apply]
      simp only [Function.comp_apply, hfw]
    rw [hsB] at h2
    obtain ⟨u, hu⟩ := hunit (g ^ n * s) (Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers g) n) s.2)
    have key : y = (↑u⁻¹ : A) • ((algebraMap B A (g ^ n * s)) • y) := by
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ h2

  have hliA : LinearIndependent A w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
      (Finset.univ : Finset (Fin d)) a
    choose c hc using fun j => hbint j (Finset.mem_univ j)

    have h1 : f (∑ j, c j • D R B (t j)) = 0 := by

      rw [map_sum]
      simp only [map_smul, hfw, hsB, hc]
      simp only [smul_assoc, ← Finset.smul_sum, ha, smul_zero]
    obtain ⟨⟨s, hs⟩, hs0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g) (f := f)
      (h1.trans (map_zero f).symm)
    rw [smul_zero] at hs0
    replace hs0 : s • (∑ j, c j • D R B (t j)) = 0 := hs0
    obtain ⟨n, hn⟩ := hrel (Finsupp.equivFunOnFinite.symm (fun j => s * c j)) (by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, mul_smul, ← Finset.smul_sum] using hs0)
    have hi : g ^ n * (s * c i) = 0 := by
      have := congrArg (fun x => x i) hn
      simpa using this
    have hci : algebraMap B A (c i) = 0 := by
      have hu := hunit (g ^ n * s) (Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers g) n) hs)
      rw [← hu.mul_right_eq_zero, ← map_mul, mul_assoc, hi, map_zero]
    rw [hc, Algebra.smul_def] at hci
    exact ((hunit b hb).mul_right_eq_zero).1 hci
  letI : Algebra (MvPolynomial (Fin d) R) A :=
    (MvPolynomial.eval₂Hom (algebraMap R A) (fun a => algebraMap B A (t a))).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin d) R) A :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R A r = MvPolynomial.eval₂Hom (algebraMap R A) _ (MvPolynomial.C r)
      simp
  refine GlobalTheory.EtaleCoordJacobian.etale_of_basis R A (Fin d) (Module.Basis.mk hliA hsp) fun i => ?_
  rw [Module.Basis.mk_apply]
  show D R A (algebraMap B A (t i)) = D R A (MvPolynomial.eval₂Hom (algebraMap R A)
    (fun a => algebraMap B A (t a)) (MvPolynomial.X i))
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

end GlobalTheory.EtaleCoordSpread
end

section

open Filter Topology

namespace GlobalTheory.PeriodFamily

section

variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]

theorem exists_prod_dvd_monomial (t : I → D) (k : ℕ) :
    ∀ m : I →₀ ℕ, k ≤ m.degree → ∃ s : Fin k → I, ∏ a, t (s a) ∣ ∏ i, t i ^ m i := by
  induction k with
  | zero => intro m _; exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro m hm
    have h : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    obtain ⟨s, hs⟩ := ih m' (by rw [map_add (f := _), Finsupp.degree_single] at hm; omega)
    refine ⟨Fin.cons i s, ?_⟩
    have h1 : ∏ j, t j ^ (Finsupp.single i 1 : I →₀ ℕ) j = t i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finsupp.add_apply, pow_add,
      Finset.prod_mul_distrib, h1]
    exact mul_dvd_mul_left _ hs

variable [Algebra ℂ D]

theorem aeval_eq_zero_of_coeff_eq_zero {N : ℕ} {t : I → D}
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (P : MvPolynomial I ℂ)
    (hP : ∀ m : I →₀ ℕ, m.degree < N + 1 → P.coeff m = 0) : MvPolynomial.aeval t P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have h : N + 1 ≤ m.degree := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hm (hP m (by omega))
  obtain ⟨s, hs⟩ := exists_prod_dvd_monomial t (N + 1) m h
  rw [ht, zero_dvd_iff] at hs
  rw [hs, mul_zero]


omit [Algebra ℂ D] [CommRing D] in
theorem coeff_sum_monomial_finsuppAntidiag (N : ℕ) (F : MvPowerSeries I ℂ) (n : I →₀ ℕ)
    (hn : n.degree < N + 1) :
    AddMonoidAlgebra.coeff (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) n = MvPowerSeries.coeff n F := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← Finsupp.degree_eq_sum, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hn)]

theorem aeval_sum_monomial_finsuppAntidiag (N : ℕ) (t : I → D) (F : MvPowerSeries I ℂ) :
    MvPolynomial.aeval t (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (t i))]

end

theorem taylor_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) =
        GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  intro I _ _ D _ _ N t ht f g hf hg
  change GlobalTheory.PeriodFamily.taylor N t (f * g) = _
  rw [GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ (hf.mul hg), GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hf, GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hg,
    GlobalTheory.taylor_mul hf hg, ← aeval_sum_monomial_finsuppAntidiag,
    ← aeval_sum_monomial_finsuppAntidiag, ← aeval_sum_monomial_finsuppAntidiag, ← map_mul,
    ← sub_eq_zero, ← map_sub]
  refine aeval_eq_zero_of_coeff_eq_zero ht _ fun m hm => ?_
  rw [MvPolynomial.coeff_sub, coeff_sum_monomial_finsuppAntidiag _ _ _ hm, MvPolynomial.coeff_mul,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, map_add (f := _)] at hm
  rw [coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega),
    coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega)]

end GlobalTheory.PeriodFamily
end

section

open Filter Topology

namespace GlobalTheory.PeriodFamily

section Alg

variable {I R D : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing D] [Algebra R D]


omit [DecidableEq I] in
theorem mvAeval_add_of_mul_eq_zero (t n : I → D) (hn : ∀ i j, n i * n j = 0)
    (P : MvPolynomial I R) :
    MvPolynomial.aeval (fun i ↦ t i + n i) P =
      MvPolynomial.aeval t P + ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * n i := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p j hp =>
    have h1 : (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * n j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hn, mul_zero]
    have h2 : ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
        (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * t j +
          MvPolynomial.aeval t p * n j := by
      have h3 : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
          MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i * t j +
            if j = i then MvPolynomial.aeval t p * n i else 0 := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add (f := _), map_mul, map_mul, MvPolynomial.aeval_X,
          MvPolynomial.pderiv_X, Pi.single_apply]
        split_ifs <;> simp <;> ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul]
    rw [map_mul, map_mul, hp, h2, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    linear_combination h1

theorem aeval_truncTotal_succ (N : ℕ) (t : I → D) (F : MvPowerSeries I R) :
    MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) F) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  have h : MvPowerSeries.truncTotal (N + 1) F =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F) := by
    ext d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Finset.sum_ite_eq,
      Finset.mem_range, Finsupp.degree_eq_sum]

  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Algebra.smul_def]


omit [Fintype I] [DecidableEq I] in
theorem ideal_pow_eq_bot_of_prod {J : Ideal D} {k : ℕ}
    (h : ∀ s : Fin k → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) : J ^ k = ⊥ := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hx
  rw [List.prod_ofFn]
  exact h _ fun a => (f a).2


omit [DecidableEq I] in
theorem aeval_pderiv_truncTotal_mul {J : Ideal D} {N : ℕ} (hJ : J ^ (N + 1) = ⊥) {t : I → D}
    (ht : ∀ i, t i ∈ J) {x : D} (hx : x ∈ J) (F : MvPowerSeries I R) (i : I) :
    MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPowerSeries.truncTotal (N + 1) F)) * x =
      MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) (MvPowerSeries.pderiv (R := R) i F)) * x := by
  classical
  rw [← sub_eq_zero, ← sub_mul, ← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : N ≤ m.degree := by
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hm ?_
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_truncTotal _
      (by rw [map_add (f := _), Finsupp.degree_single]; omega), MvPowerSeries.coeff_truncTotal _ (by omega),
      MvPowerSeries.coeff_pderiv, sub_self]
  have h1 : ∏ j, t j ^ m j ∈ J ^ N := by
    refine Ideal.pow_le_pow_right hdeg ?_
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (ht j) _
  have h2 : (∏ j, t j ^ m j) * x = 0 := by
    rw [← Ideal.mem_bot, ← hJ, pow_succ]
    exact Ideal.mul_mem_mul h1 hx
  rw [mul_assoc, h2, mul_zero]

end Alg

theorem taylor_add_of_mul_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  intro I _ _ D _ _ N t n hs hn f hf
  have key : ∀ (u : I → D) (g : (I → ℂ) → ℂ), AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N u g =
      MvPolynomial.aeval u (MvPowerSeries.truncTotal (N + 1) (GlobalTheory.taylor g)) := fun u g hg => by
    rw [aeval_truncTotal_succ, taylor_eq_sum_coeff_taylor N u g hg]
  rw [key _ _ hf, key _ _ hf, mvAeval_add_of_mul_eq_zero t n hn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key _ _ (GlobalTheory.analyticAt_fderiv_apply hf _), GlobalTheory.taylor_fderiv hf]
  exact aeval_pderiv_truncTotal_mul (ideal_pow_eq_bot_of_prod hs)
    (fun j => Ideal.subset_span (Or.inl ⟨j, rfl⟩)) (Ideal.subset_span (Or.inr ⟨i, rfl⟩)) _ i

end GlobalTheory.PeriodFamily
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allPrim_of_abelianDeRhamFree (h : GlobalTheory.Published.AbelianDeRhamFree) (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  have hdim : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    haveI := hg
    haveI : SmoothOfRelativeDimension g (pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (pullback.fst A.hom A.hom ≫ A.hom))
  obtain ⟨f1, p1, r1, -⟩ := h R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := h R (A ⊗ A) (g + g)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hdim
  have one0 : ∀ c, pullOver (dp0 R) (𝟙 _) (1 : A ⟶ A) c = 0 := fun c => by
    haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
    rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]
  have id0 : ∀ c, pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := fun c => IsMor.pullCohomologyOne_id _ c
  let Ψ := (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) (1 : A ⟶ A))).prod
    (pullOver (dp0 R) (𝟙 _) (lift (1 : A ⟶ A) (𝟙 A)))
  have hs : Function.Surjective Ψ := fun ⟨a, b⟩ =>
    ⟨pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b, by
    refine Prod.ext ?_ ?_
    · change pullOver _ _ _ _ = a
      rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, add_zero]
    · change pullOver _ _ _ _ = b
      rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, zero_add]⟩
  have hb : Function.Bijective Ψ := Module.bijective_of_surjective_of_rankAtStalk_eq hs (by
    intro m hm
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring)
  refine eq_top_iff.2 fun c _ => (mem_prim_iff _ _ _ _).2 (hb.1 ?_)
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.one_mul]
  refine Prod.ext ?_ ?_
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e1,
      one0, id0, add_zero]
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e2,
      one0, id0, zero_add]

theorem abelianDeRhamFree_toFree (h : GlobalTheory.Published.AbelianDeRhamFree) :
    GlobalTheory.Published.AbelianDeRham.Free := fun R _ A _ g hA hg =>
  ⟨allPrim_of_abelianDeRhamFree h R A g hA hg, h R A g hA hg⟩

theorem abelianDeRhamStructure_toFree (h : GlobalTheory.Published.AbelianDeRhamStructure) :
    GlobalTheory.Published.AbelianDeRham.Free :=
  abelianDeRhamFree_toFree h.1

end GlobalTheory
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.DualWeylDeg

theorem weight_colW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (t : Fin N) :
    (Finsupp.weight (colW N N) m) t = ∑ a : Fin N, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, colW, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Pi.single_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp; intro h; exact absurd h.symm hb
  · simp

theorem totalDegree_le_of_mem_dualWeyl : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  intro O _ N ν f hf
  have h1 : f ∈ weightedHomogeneousSubmodule O (colW N N) ν := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have h2 : Finsupp.weight (colW N N) m = ν := h1 (mem_support_iff.mp hm)
  have h3 : m.sum (fun _ e => e) = ∑ t, ∑ a : Fin N, m (a, t) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]
  rw [h3]
  refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
  rw [← weight_colW_apply, h2]

end GlobalTheory.DualWeylDeg
end

end

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_kaehler_basis : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  first | exact @_root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | exact _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | (intros; apply _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale <;> assumption)

end
end
