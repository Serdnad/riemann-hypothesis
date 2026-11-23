module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_int_multiple {Ω : Type*} [Field Ω] [CharZero Ω] {β : Ω} (hβ : IsIntegral ℤ β) (h0 : β ≠ 0) :
    ∃ (n : ℤ) (γ : Ω), n ≠ 0 ∧ IsIntegral ℤ γ ∧ (n : Ω) = β * γ := by
  obtain ⟨p, hpm, hp0⟩ := id hβ
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  have haq : Polynomial.aeval β q = 0 := by
    have h1 : Polynomial.aeval β p = 0 := by rw [Polynomial.aeval_def]; exact hp0
    rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ h0)
  refine ⟨q.coeff 0, -(Polynomial.aeval β q.divX), hq0, ?_, ?_⟩
  · have hmem := adjoin_le_integralClosure hβ (Polynomial.aeval_mem_adjoin_singleton ℤ β (p := q.divX))
    exact (neg_mem hmem : _ ∈ integralClosure ℤ Ω)
  · have h2 := congrArg (Polynomial.aeval β) (Polynomial.divX_mul_X_add q)
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, haq, eq_intCast] at h2
    linear_combination h2

theorem mem_valuationSubring_of_isIntegral {Ω : Type*} [Field Ω] {x : Ω} (hx : IsIntegral ℤ x)
    (A : ValuationSubring Ω) : x ∈ A := by
  have hA : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

theorem sepInt {Ω : Type*} [Field Ω] [CharZero Ω] (s : Finset Ω) (hs : ∀ r ∈ s, IsIntegral ℤ r) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ A : ValuationSubring Ω, r - r' ∈ A.nonunits →
      (n : Ω) ∈ A.nonunits := by
  classical
  have key : ∀ q ∈ s.offDiag, ∃ (m : ℤ) (γ : Ω), m ≠ 0 ∧ IsIntegral ℤ γ ∧ (m : Ω) = (q.1 - q.2) * γ := by
    intro q hq
    rw [Finset.mem_offDiag] at hq
    exact exists_int_multiple ((hs _ hq.1).sub (hs _ hq.2.1)) (sub_ne_zero.2 hq.2.2)
  choose! m γ hm hγ hmγ using key
  refine ⟨∏ q ∈ s.offDiag, m q, Finset.prod_ne_zero_iff.2 hm, ?_⟩
  intro r hr r' hr' hne A hA
  have hq : (r, r') ∈ s.offDiag := Finset.mem_offDiag.2 ⟨hr, hr', hne⟩
  rw [Int.cast_prod, ← Finset.mul_prod_erase _ _ hq]
  rw [ValuationSubring.mem_nonunits_iff] at hA ⊢
  rw [Valuation.map_mul, hmγ _ hq, Valuation.map_mul]
  have h1 : A.valuation (γ (r, r')) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (mem_valuationSubring_of_isIntegral (hγ _ hq) A)
  have h2 : A.valuation (∏ q ∈ s.offDiag.erase (r, r'), (m q : Ω)) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (prod_mem fun q _ => intCast_mem _ _)
  calc _ ≤ A.valuation (r - r') * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h1) h2
    _ < 1 := by rw [mul_one, mul_one]; exact hA

theorem finite_places (E : Type*) [Field E] [NumberField E] {n : ℤ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 E) | (n : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

private theorem hasSum_sigma_mul_qParam_pow_modularForm_E {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (C : ℂ)
    (hC : (riemannZeta k)⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ k / ((k - 1).factorial : ℂ) = C)
    (τ : ℍ) :
    HasSum (fun m : ℕ => (if m = 0 then (1 : ℂ) else C * (ArithmeticFunction.sigma (k - 1) m : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E hk τ) := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqe : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) = q := by
    simp [hqdef, Function.Periodic.qParam]
  have hq : ‖q‖ < 1 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    refine (Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero
    have := τ.im_pos
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im, div_one]
    nlinarith
  have hσ : ∀ n : ℕ, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    calc ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (k - 1) :=
          Finset.sum_le_sum fun d hd => pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.divisor_le hd) _
      _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (k - 1) := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n
      _ = (n : ℝ) ^ k := by
          rw [← pow_succ']
          congr 1
          omega
  have hsum : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hq)) hσ
  have hsum1 : Summable fun n : ℕ =>
      ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hE := EisensteinSeries.q_expansion_riemannZeta hk hke τ
  rw [hE, hC, hqe]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one,
    add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]
  have ht : ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ (n : ℕ) =
      ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)
  convert hsum1.hasSum.mul_left C using 1 <;>
    first
    | rfl
    | (funext n <;> ring)
    | (congr 1 <;> (rw [← ht]; apply tsum_congr; intro n; simp))

theorem map_eisensteinFourInt : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  have hE : E₄ = ModularForm.E (k := 4) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1)
    (c := fun m => PowerSeries.coeff m (e4Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 4 /
      (((4 - 1).factorial : ℕ) : ℂ) = 240 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
    have hI : Complex.I ^ 4 = 1 := Complex.I_pow_four
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem map_eisensteinSixInt : e6Z.map (Int.castRingHom ℂ) = qExpansion 1 E₆ := by
  have hE : E₆ = ModularForm.E (k := 6) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₆) (h := 1)
    (c := fun m => PowerSeries.coeff m (e6Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hb6 : bernoulli 6 = 1 / 42 := by
    have h5 : bernoulli' 5 = 0 := by
      rw [bernoulli'_def]
      norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
        bernoulli'_three, bernoulli'_four, Nat.choose]
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5, Nat.choose]
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    have h6 := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show ((6 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h6, hb6]
    norm_num [Nat.factorial]
    ring
  have hC : (riemannZeta ((6 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 6 /
      (((6 - 1).factorial : ℕ) : ℂ) = -504 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hz6]
    have hI : Complex.I ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]
      norm_num
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 6) (by norm_num) (by decide) (-504) hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e6Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem aC_eq : aC = qExpansion 1 AA := by
  have h1 : AnalyticAt ℂ (cuspFunction 1 ⇑E₄) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos (by simp)
  have h2 : AnalyticAt ℂ (cuspFunction 1 (⇑E₄ * ⇑E₄)) 0 := by
    have h3 := ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos (by simp)
    rwa [ModularForm.coe_mul] at h3
  have hA : AA = ⇑E₄ * (⇑E₄ * ⇑E₄) := by
    funext τ
    simp only [AA, Pi.mul_apply]
    ring
  rw [hA, qExpansion_mul h1 h2, qExpansion_mul h1 h1, ← map_eisensteinFourInt]
  simp only [aC, aZ, map_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem latTau_snd_ne (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

theorem latTau_im_ne (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have h2 := latTau_snd_ne L
  obtain ⟨r, hr⟩ : ∃ r : ℝ, L.ω₁ / L.ω₂ = (r : ℂ) :=
    ⟨(L.ω₁ / L.ω₂).re, Complex.ext (by simp) (by simp [h])⟩
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hr, div_mul_cancel₀ _ h2]
  have h3 := (LinearIndependent.pair_iff.mp L.indep) 1 (-r)
    (by rw [Complex.real_smul, Complex.real_smul, h1]; push_cast; ring)
  norm_num at h3

theorem latTau (L : PeriodPair) : ∃ (c : ℂ) (τ : ℍ), IsTauOf L c τ := by
  have h2 := latTau_snd_ne L
  rcases lt_or_gt_of_ne (latTau_im_ne L) with hneg | hpos
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by rw [Complex.neg_im]; linarith⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨-u, v, by push_cast; field_simp; try ring⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, hpos⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨u, v, by field_simp; try ring⟩

end ReciprocityTheory.ChartRestriction.L1
end
end
