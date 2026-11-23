module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle002
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsAlgebraicIndependentRatiosOfGenericZero
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle003
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
public import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
public import Mathlib.RingTheory.MvPolynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Filter Topology MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

section Comp

variable {σ τ W : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [NormedAddCommGroup W]
  [NormedSpace ℂ W]


omit [DecidableEq σ] in
theorem hasSubst_taylorDir (u : τ → W) {φ : W → σ → ℂ} (h0 : φ 0 = 0) :
    HasSubst fun i => taylorDir u fun z => φ z i := by
  refine hasSubst_of_constantCoeff_zero fun i => ?_
  simp [h0]

private theorem fderiv_comp_apply_eq_sum_pi_single {φ : W → σ → ℂ} {f : (σ → ℂ) → ℂ} {z : W}
    (hφ : DifferentiableAt ℂ φ z) (hf : DifferentiableAt ℂ f (φ z)) (v : W) :
    fderiv ℂ (f ∘ φ) z v =
      ∑ i, fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z v := by
  have hi : ∀ i, fderiv ℂ (fun y => φ y i) z v = fderiv ℂ φ z v i := fun i => by
    rw [(hasFDerivAt_pi'.1 hφ.hasFDerivAt i).fderiv]
    rfl
  simp_rw [hi]
  rw [fderiv_comp z hf hφ, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← Finset.univ_sum_single (fderiv ℂ φ z v)]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (fderiv ℂ φ z v i) : σ → ℂ) = fderiv ℂ φ z v i • Pi.single i 1 by
    ext k; by_cases h : k = i <;> simp [h], map_smul, smul_eq_mul, mul_comm]

private theorem taylorDir_comp_eq_subst_taylor_of_analyticAt (u : τ → W) {φ : W → σ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) :
    ∀ D ∈ {D : MvPowerSeries τ ℂ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧
      D = taylorDir u (f ∘ φ) - subst (fun i => taylorDir u fun z => φ z i) (taylor f)}, D = 0 := by
  have hs : HasSubst fun i => taylorDir u fun z => φ z i := hasSubst_taylorDir u h0
  have ha0 : ∀ i, constantCoeff (taylorDir u fun z => φ z i) = 0 := fun i => by simp [h0]
  have hT : Tendsto φ (𝓝 0) (𝓝 0) := by simpa [h0] using hφ.continuousAt.tendsto
  have hφi : ∀ i, AnalyticAt ℂ (fun z => φ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt (φ 0)).comp hφ
  apply mvPowerSeries_eq_zero_of_pderiv_mem_span
  · rintro _ ⟨f, hf, rfl⟩
    rw [map_sub, FormalCalc.constantCoeff_subst_of_zero hs ha0]
    simp [h0]
  · rintro _ ⟨f, hf, rfl⟩ j
    have hfφ : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ h0
    have hg : ∀ i, AnalyticAt ℂ (fun y => fderiv ℂ f y (Pi.single i 1)) 0 := fun i =>
      analyticAt_fderiv_apply hf _
    have hev : (fun z => fderiv ℂ (f ∘ φ) z (u j)) =ᶠ[𝓝 0] fun z => ∑ i,
        fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z (u j) := by
      filter_upwards [hφ.eventually_analyticAt, hT.eventually hf.eventually_analyticAt] with z hz1 hz2
      exact fderiv_comp_apply_eq_sum_pi_single hz1.differentiableAt hz2.differentiableAt (u j)
    have hsum := taylorDir_sum u Finset.univ (F := fun i z =>
        fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z (u j))
      (fun i _ => ((hg i).comp_of_eq hφ h0).mul (analyticAt_fderiv_apply (hφi i) _))
    beta_reduce at hsum
    have key : pderiv (R := ℂ) j (taylorDir u (f ∘ φ) -
        subst (fun i => taylorDir u fun z => φ z i) (taylor f)) =
        ∑ i, (taylorDir u ((fun y => fderiv ℂ f y (Pi.single i 1)) ∘ φ) -
          subst (fun i => taylorDir u fun z => φ z i) (taylor fun y => fderiv ℂ f y (Pi.single i 1))) *
            pderiv (R := ℂ) j (taylorDir u fun z => φ z i) := by
      rw [map_sub, FormalCalc.pderiv_subst hs, ← taylorDir_fderiv u hfφ j, taylorDir_congr u hev,
        hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_mul, ← taylorDir_fderiv u (hφi i) j, taylor_fderiv hf i]
      congr 1
      exact taylorDir_mul u ((hg i).comp_of_eq hφ h0) (analyticAt_fderiv_apply (hφi i) _)
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨_, hg i, rfl⟩)

theorem taylorDir_comp (u : τ → W) {φ : W → σ → ℂ} (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0)
    {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    taylorDir u (f ∘ φ) = subst (fun i => taylorDir u fun z => φ z i) (taylor f) := by
  have hs : HasSubst fun i => taylorDir u fun z => φ z i := hasSubst_taylorDir u h0
  have hD := taylorDir_comp_eq_subst_taylor_of_analyticAt u hφ h0 (taylorDir u (f ∘ φ) -
    subst (fun i => taylorDir u fun z => φ z i) (taylor f)) ⟨f, hf, rfl⟩
  exact sub_eq_zero.1 hD

end Comp

section Points

variable {n d : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

variable (e : Fin 1 × Fin d → W) {f : W → ℂ}

variable {ι : Type} [Fintype ι]

end Points

section Curried

variable {m n d d' : ℕ}

section Algebra

variable {F G : (Fin n → Fin d → ℂ) → ℂ}

end Algebra

end Curried

end GlobalTheory
end

section

open NumberField Pointwise

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem exists_prime_dvd_natCast_mem {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) :
    ∀ N : ℕ, N ≠ 0 → (N : R) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ (p : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.CuspFormEvaluationSupplement.main
  | exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main
  | (apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main ..)

theorem span_natCast_dvd_differentIdeal_sq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (N : ℕ)
    (hN0 : 0 < N) (hN : ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E))
    (hmin : ∀ M : ℕ, 0 < M → M < N → ((M : ℕ) : 𝓞 E) ∉ differentIdeal ℤ (𝓞 E)) :
    Ideal.span {((N : ℕ) : 𝓞 E)} ∣ differentIdeal ℤ (𝓞 E) ^ 2 := by
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[ℚ] E) ℤ (𝓞 E) ℚ E
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hD0 : D ≠ 0 := differentIdeal_ne_bot
  have hspan : ∀ M : ℕ, M ≠ 0 → Ideal.span {((M : ℕ) : 𝓞 E)} ≠ 0 := fun M hM => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hM
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (hspan N hN0.ne')]
  intro P hP
  by_cases hPN : P ∣ Ideal.span {((N : ℕ) : 𝓞 E)}
  swap
  · rw [emultiplicity_eq_zero.2 hPN]
    exact zero_le
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  obtain ⟨p, hp, ⟨M, rfl⟩, hpP⟩ := exists_prime_dvd_natCast_mem hPp N hN0.ne' (Ideal.dvd_span_singleton.1 hPN)
  have hM0 : 0 < M := Nat.pos_of_mul_pos_left hN0
  have hMD := hmin M hM0 ((Nat.lt_mul_iff_one_lt_left hM0).2 hp.one_lt)
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0] at hMD
  push Not at hMD
  obtain ⟨Q, hQ, hQlt⟩ := hMD
  have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
  have hmul : Ideal.span {((p * M : ℕ) : 𝓞 E)} = Ideal.span {(p : 𝓞 E)} * Ideal.span {(M : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
  have hpQ : (p : 𝓞 E) ∈ Q := by
    by_contra h
    have h1 := emultiplicity_le_emultiplicity_of_dvd_right (a := Q) (Ideal.dvd_span_singleton.2 hN)
    have h2 : emultiplicity Q (Ideal.span {(p : 𝓞 E)}) = 0 :=
      emultiplicity_eq_zero.2 fun hh => h (Ideal.dvd_span_singleton.1 hh)
    rw [hmul, emultiplicity_mul hQ, h2, zero_add] at h1
    exact absurd hQlt (not_lt.2 h1)
  have := liesOver_span E p hp hPp hpP
  have := liesOver_span E p hp hQp hpQ
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have h3 : ∀ X : Ideal (𝓞 E), σ • X = X → emultiplicity (σ • P) X = emultiplicity P X := fun X hX => by
    conv_lhs => rw [← hX]
    exact emultiplicity_map_eq (MulSemiringAction.toRingEquiv (E ≃ₐ[ℚ] E) (Ideal (𝓞 E)) σ)
  rw [h3 _ (smul_span_nat σ M), h3 _ (smul_differentIdeal σ)] at hQlt
  have fD := FiniteMultiplicity.of_prime_left hP hD0
  have fM := FiniteMultiplicity.of_prime_left hP (hspan M hM0.ne')
  have fp := FiniteMultiplicity.of_prime_left hP (hspan p hp.ne_zero)
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  have hd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ D := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hd' := fD.le_multiplicity_of_pow_dvd hd
  rw [hmul, emultiplicity_mul hP, pow_two, emultiplicity_mul hP]
  rw [fD.emultiplicity_eq_multiplicity, fM.emultiplicity_eq_multiplicity] at hQlt ⊢
  rw [fp.emultiplicity_eq_multiplicity]
  norm_cast at hQlt ⊢
  omega

theorem exists_natCast_mem_differentIdeal_pow_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧
      ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧
      (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by
  intro E _ _ _
  classical
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have hex : ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
    refine ⟨(NumberField.discr E).natAbs, Nat.pos_of_ne_zero hd0, ?_⟩
    rw [← NumberField.absNorm_differentIdeal E (𝓞 E)]
    exact Ideal.absNorm_mem _
  obtain ⟨h0, hmem⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h0, hmem, ?_⟩
  have hdvd := span_natCast_dvd_differentIdeal_sq E _ h0 hmem
    fun M hM hlt hMD => Nat.find_min hex hlt ⟨hM, hMD⟩
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [absNorm_span_nat, map_pow, NumberField.absNorm_differentIdeal E (𝓞 E)] at h1
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero 2 hd0)) h1
  have h3 : |(NumberField.discr E : ℝ)| = ((NumberField.discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h3]
  exact_mod_cast h2

end GlobalTheory
end

section

namespace GlobalTheory


open MvPolynomial in
theorem aeval_mul_of_isHomogeneous_cone {K L ι : Type} [CommRing K] [CommRing L] [Algebra K L]
    {Q : MvPolynomial ι K} {d : ℕ} (hQ : Q.IsHomogeneous d) (c : L) (x : ι → L) :
    aeval (fun a => c * x a) Q = c ^ d * aeval x Q := by
  classical
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hQ.degree_eq_sum_deg_support hs
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hd]
  ring


open MvPolynomial in
theorem aeval_eq_pow_mul_aeval_dehomogenise {K L : Type} [CommRing K] [Field L] [Algebra K L]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (x : Fin (m + 1) → L) (hx : x 0 ≠ 0) :
    aeval x Q = x 0 ^ d * aeval (fun a : Fin m => x a.succ / x 0)
      (aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q) := by
  set y : Fin m → L := fun a => x a.succ / x 0 with hy
  have hx' : x = fun a => x 0 * (Fin.cons 1 y : Fin (m + 1) → L) a := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simp only [Fin.cons_succ, hy]
      field_simp
  have key : (fun i => aeval y ((Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) i)) =
      (Fin.cons 1 y : Fin (m + 1) → L) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  conv_lhs => rw [hx']
  rw [aeval_mul_of_isHomogeneous_cone hQ,
    aeval_eq_bind₁ (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K), aeval_bind₁, key]


open MvPolynomial in
theorem dehomogenise_ne_zero_of_isHomogeneous {K : Type} [Field K]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d) (h0 : Q ≠ 0) :
    aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin (m + 1)) K)
    (FractionRing (MvPolynomial (Fin (m + 1)) K))
  have hx0 : (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘
      X) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    exact (map_ne_zero_iff _ hinj).mpr (X_ne_zero 0)
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := FractionRing (MvPolynomial (Fin (m + 1)) K)) hQ
    (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘ X) hx0
  rw [h, map_zero, mul_zero, aeval_algebraMap_apply, aeval_X_left_apply] at e
  exact h0 (hinj (by rw [e, map_zero]))

theorem exists_coordinates_no_homogeneous_relation_of_generic_zero :
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ),
    (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N,
      ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d →
        MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  intro K _ σ m N t ζ ht hζ hrel
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain _ | N := N
  · exact absurd (funext fun j => j.elim0) hζ
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hζ
  have hj0' : ζ j0 ≠ 0 := hj0
  have hind : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    exact ht p hne hp
  obtain ⟨J, hJ⟩ := exists_algebraicIndependent_ratios_of_generic_zero K ℂ m N t ζ j0 hind hj0' hrel
  refine ⟨Fin.cons j0 J, fun Q d hQ0 hQ => ?_⟩
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := ℂ) hQ
    (fun a => ζ ((Fin.cons j0 J : Fin (m + 1) → Fin (N + 1)) a)) (by simpa using hj0')
  change MvPolynomial.aeval _ Q ≠ 0
  rw [e]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine mul_ne_zero (pow_ne_zero _ hj0') ?_
  intro h
  exact dehomogenise_ne_zero_of_isHomogeneous hQ hQ0 ((algebraicIndependent_iff.mp hJ) _ h)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  first | exact @GlobalTheory.card_exponents_and_choose_ratio_bounds | exact GlobalTheory.card_exponents_and_choose_ratio_bounds | (intros; apply GlobalTheory.card_exponents_and_choose_ratio_bounds <;> assumption)
end

section

open MeasureTheory

namespace GlobalTheory

theorem ae_eval₂_ne_zero_of_countable (K : Type) [Field K] [Countable K] (σ : K →+* ℂ)
    (ι : Type) [Fintype ι] :
    ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  have : Countable (MvPolynomial ι K) :=
    (MvPolynomial.basisMonomials ι K).repr.injective.countable
  rw [ae_all_iff]
  intro Q
  by_cases hQ : Q = 0
  · exact Filter.Eventually.of_forall fun t h => absurd hQ h
  · have hm : MvPolynomial.map σ Q ≠ 0 := by
      intro h
      exact hQ (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
    have h := ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (ι → ℂ))
      (LinearEquiv.refl ℂ (ι → ℂ)) _ hm
    filter_upwards [h] with t ht _
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact ht

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

theorem _root_.GlobalTheory.T.exists_thetaRunParameters_uniform_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ), 2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E → (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E → ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) → ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  first | exact @GlobalTheory.ThetaRunParameters.exists_par | exact GlobalTheory.ThetaRunParameters.exists_par | (intros; apply GlobalTheory.ThetaRunParameters.exists_par <;> assumption)
end
