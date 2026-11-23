module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section

section

open NumberField

noncomputable section

namespace PI.OkpW

theorem norm_le_one_of_integral {F R : Type*} [NormedField F] [IsUltrametricDist F] [CommRing R]
    [Algebra R F] (hR : ∀ r : R, ‖algebraMap R F r‖ ≤ 1) (δ : F) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨f, hf, hfe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one,
    one_mul] at hfe
  have h1 : δ ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hfe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ f.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ f.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R F (f.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ f.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ f.natDegree / ‖δ‖ < ‖δ‖ ^ f.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ f.natDegree‖ = ‖δ‖ ^ f.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

theorem norm_le_one_of_integral_int {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra ℤ F]
    (δ : F) (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral (fun n => by
    rw [eq_intCast (algebraMap ℤ F) n]; exact IsUltrametricDist.norm_intCast_le_one F n) δ h

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_p_cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  rw [this, norm_algebraMap', Padic.norm_p]

variable {K : Type} [Field K] [NumberField K]

theorem norm_tau_le (τ : K →+* ℂ_[p]) (a : 𝓞 K) : ‖τ (a : K)‖ ≤ 1 :=
by
  have hI : IsIntegral ℤ (τ (a : K)) := by
    obtain ⟨f, hm, he⟩ := RingOfIntegers.isIntegral_coe a
    refine ⟨f, hm, ?_⟩
    have := congrArg τ he
    rw [Polynomial.hom_eval₂, map_zero] at this
    rwa [Subsingleton.elim (τ.comp (algebraMap ℤ K)) (algebraMap ℤ ℂ_[p])] at this
  exact norm_le_one_of_integral_int _ hI

theorem norm_tau_dvd (τ : K →+* ℂ_[p]) {a : 𝓞 K} {k : ℕ} (h : (p : 𝓞 K) ^ k ∣ a) :
    ‖τ (a : K)‖ ≤ (p : ℝ)⁻¹ ^ k := by
  obtain ⟨b, rfl⟩ := h
  have : τ (((p : 𝓞 K) ^ k * b : 𝓞 K) : K) = (p : ℂ_[p]) ^ k * τ (b : K) := by simp
  rw [this, norm_mul, norm_pow, norm_p_cp]
  exact mul_le_of_le_one_right (by positivity) (norm_tau_le τ b)

theorem span_p_ne_bot : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero

theorem isMaximal_span_p (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) :
    (Ideal.span {(p : 𝓞 K)}).IsMaximal :=
  hP.isMaximal span_p_ne_bot

theorem natCard_quot (hK : Module.finrank ℚ K = 2) :
    Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  have h := Ideal.absNorm_span_singleton (p : 𝓞 K)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h]
  have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
  simp

theorem finite_quot (hK : Module.finrank ℚ K = 2) : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quot hK]; exact (pow_pos hp.out.pos 2).ne')

theorem pow_q_sub (hK : Module.finrank ℚ K = 2) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime)
    (a : 𝓞 K) (n : ℕ) : (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have hM : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI := Ideal.Quotient.field (Ideal.span {(p : 𝓞 K)})
  haveI := finite_quot (K := K) (p := p) hK
  letI := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})
  have hc : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, natCard_quot hK]
  rw [map_pow, ← hc, FiniteField.pow_card_pow]

theorem exists_inv_mod (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K} (ha : ¬ (p : 𝓞 K) ∣ a) :
    ∃ b : 𝓞 K, (p : 𝓞 K) ∣ a * b - 1 := by
  have hM : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI := Ideal.Quotient.field (Ideal.span {(p : 𝓞 K)})
  have h0 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a)⁻¹
  refine ⟨b, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_mul, hb, map_one, mul_inv_cancel₀ h0]

end PI.OkpW
end
end

section

open NumberField

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K]

theorem c_invol (hK : Module.finrank ℚ K = 2) (c : K →+* K) (x : K) : c (c x) = x := by
  let f : K →ₐ[ℚ] K := c.toRatAlgHom
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofBijective f (AlgHom.bijective f)
  have hcard : Nat.card (K ≃ₐ[ℚ] K) ≤ 2 := by
    rw [← hK, Nat.card_congr (algEquivEquivAlgHom ℚ K).toEquiv]
    exact card_algHom_le_finrank ℚ K K
  have hpos : 0 < Nat.card (K ≃ₐ[ℚ] K) := Nat.card_pos
  have h1 : e ^ Nat.card (K ≃ₐ[ℚ] K) = 1 := pow_card_eq_one'
  have he : e ^ 2 = 1 := by
    rcases (by omega : Nat.card (K ≃ₐ[ℚ] K) = 1 ∨ Nat.card (K ≃ₐ[ℚ] K) = 2) with h | h
    · rw [h, pow_one] at h1; rw [h1, one_pow]
    · rwa [h] at h1
  have := DFunLike.congr_fun he x
  rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] at this
  exact this

theorem c_fix_rat (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) {y : K}
    (hy : c y = y) : ∃ r : ℚ, (r : K) = y := by
  let D : K →ₗ[ℚ] K := c.toRatAlgHom.toLinearMap - LinearMap.id
  have hD : ∀ z, D z = c z - z := fun z => rfl
  have hS : LinearMap.ker D ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hc
    intro h
    have hm : x ∈ LinearMap.ker D := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hD, sub_eq_zero] at hm
    exact hx hm
  have hlt : Module.finrank ℚ (LinearMap.ker D) < 2 :=
    hK ▸ Submodule.finrank_lt hS
  have hle : (ℚ ∙ (1 : K)) ≤ LinearMap.ker D := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hD, map_one, sub_self]
  have heq : (ℚ ∙ (1 : K)) = LinearMap.ker D :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton one_ne_zero]; omega)
  have hyS : y ∈ LinearMap.ker D := by rw [LinearMap.mem_ker, hD, hy, sub_self]
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨r, hr⟩ := hyS
  exact ⟨r, by rw [← hr, Rat.smul_def, mul_one]⟩

theorem add_c_int (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (a : 𝓞 K) :
    ∃ n : ℤ, a + RingOfIntegers.mapRingHom c a = (n : 𝓞 K) := by
  have hfix : c ((a : K) + c a) = (a : K) + c a := by rw [map_add (f := _), c_invol hK c, add_comm]
  obtain ⟨r, hr⟩ := c_fix_rat hK c hc hfix
  have hint : IsIntegral ℤ (algebraMap ℚ K r) := by
    rw [eq_ratCast, hr]
    have := (a + RingOfIntegers.mapRingHom c a).isIntegral_coe
    simpa [RingOfIntegers.mapRingHom_apply] using this
  rw [isIntegral_algebraMap_iff ,
    IsIntegrallyClosed.isIntegral_iff] at hint
  obtain ⟨n, hn⟩ := hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  have h2 : ((a + RingOfIntegers.mapRingHom c a : 𝓞 K) : K) = (a : K) + c a := by
    simp [RingOfIntegers.mapRingHom_apply]
  rw [h2, ← hr, ← hn]
  simp

end PI.OkpW
end
end
