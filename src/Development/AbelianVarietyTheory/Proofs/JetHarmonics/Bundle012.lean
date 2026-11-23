module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open NumberField IntermediateField Polynomial

namespace GlobalTheory


open NumberField IntermediateField Polynomial in
theorem _root_.GlobalTheory.sqrtNeg_not_mem_range {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (q : ℕ) (hq : 0 < q) (x : K) (hx : x ^ 2 = -(q : K)) : x ∉ (algebraMap ℚ K).range := by
  rintro ⟨r, rfl⟩
  have hr : r ^ 2 = -(q : ℚ) := by
    apply (algebraMap ℚ K).injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  nlinarith [sq_nonneg r]


open NumberField IntermediateField Polynomial in
theorem _root_.GlobalTheory.minpoly_eq_of_quadratic_irrational {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℚ[X]) (hm : p.Monic) (hd : p.natDegree = 2) (x : K) (hx : aeval x p = 0)
    (hr : x ∉ (algebraMap ℚ K).range) : p = minpoly ℚ x := by
  have hint : IsIntegral ℚ x := ⟨p, hm, by rwa [aeval_def] at hx⟩
  have hdvd : minpoly ℚ x ∣ p := minpoly.dvd ℚ x hx
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ x).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.1 h)
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm hdvd (by omega)


open NumberField IntermediateField Polynomial in
theorem _root_.GlobalTheory.natAbs_discr_of_sq_eq_neg_prime (K : Type*) [Field K] [NumberField K] (q : ℕ)
    (hq : q.Prime) (h4 : q % 4 = 3) (x : K) (hx : x ^ 2 = -(q : K))
    (hK : Module.finrank ℚ K = 2) : (NumberField.discr K).natAbs = q := by
  obtain ⟨B, t, n, h0, h1, hd⟩ := _root_.GlobalTheory.QuadraticZeta.exists_basis hK
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q + 1 = 4 * m := ⟨(q + 1) / 4, by omega⟩
  have hxi : IsIntegral ℤ x :=
    ⟨X ^ 2 + C (q : ℤ), monic_X_pow_add_C _ two_ne_zero, by simp [hx]⟩
  have hyi : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨X ^ 2 - X + C (m : ℤ), by monicity!, ?_⟩
    have hmK : (4 : K) * m = q + 1 := by exact_mod_cast hm.symm
    simp
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hmK
  obtain ⟨X0, hX0⟩ : ∃ X0 : 𝓞 K, algebraMap (𝓞 K) K X0 = x := ⟨⟨x, hxi⟩, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : 𝓞 K, algebraMap (𝓞 K) K Y0 = (1 + x) / 2 :=
    ⟨⟨(1 + x) / 2, hyi⟩, rfl⟩
  have hXY : X0 = (2 : ℤ) • Y0 - B 0 := by
    rw [h0, zsmul_eq_mul]
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_sub, map_mul, map_intCast, map_one, Int.cast_ofNat, map_ofNat]
    rw [hX0, hY0]
    ring
  have hsq : X0 ^ 2 = -(q : 𝓞 K) := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_neg, map_natCast]
    rw [hX0, hx]
  have hb : B.repr X0 1 = 2 * B.repr Y0 1 := by
    rw [hXY, map_sub, map_zsmul, Finsupp.sub_apply, Finsupp.smul_apply, B.repr_self,
      smul_eq_mul]
    simp
  have hX := B.sum_repr X0
  rw [Fin.sum_univ_two] at hX
  generalize B.repr X0 0 = a at hX
  generalize B.repr X0 1 = c at hX hb
  generalize B.repr Y0 1 = e at hb
  subst hb
  have hli : LinearIndependent ℤ ![B 0, B 1] := by
    convert B.linearIndependent
    ext i
    fin_cases i <;> rfl
  obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.1 hli (a ^ 2 - (2 * e) ^ 2 * n + q)
    (2 * a * (2 * e) + (2 * e) ^ 2 * t) (by
      simp only [zsmul_eq_mul] at hX ⊢
      rw [h0] at hX ⊢
      push_cast at hX ⊢
      linear_combination ((a : 𝓞 K) * 1 + 2 * (e : 𝓞 K) * B 1 + X0) * hX + hsq
        + (-(2 * (e : 𝓞 K)) ^ 2) * h1)
  have he : e ≠ 0 := by
    rintro rfl
    apply _root_.GlobalTheory.sqrtNeg_not_mem_range q hq.pos x hx
    refine ⟨(a : ℚ), ?_⟩
    have hc := congrArg (algebraMap (𝓞 K) K) hX
    simp only [zero_smul, add_zero, zsmul_eq_mul, h0, mul_one, map_intCast] at hc
    rw [hX0] at hc
    simpa using hc
  have h2 : 2 * a + 2 * e * t = 0 := by
    have h' : (2 * e) * (2 * a + 2 * e * t) = 0 := by linear_combination k2
    rcases mul_eq_zero.1 h' with h | h
    · omega
    · exact h
  have h3 : a + e * t = 0 := by linarith
  have hD : e ^ 2 * discr K = -q := by
    rw [hd]
    linear_combination (e * t - a) * h3 + k1
  have hN := congrArg Int.natAbs hD
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast] at hN
  have hdvd : e.natAbs ^ 2 ∣ q := ⟨_, hN.symm⟩
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
  · rw [h, one_mul] at hN
    exact hN
  · exfalso
    have hp : (e.natAbs * e.natAbs).Prime := by rw [← sq, h]; exact hq
    rcases Nat.prime_mul_iff.1 hp with ⟨hp', he1⟩ | ⟨hp', he1⟩ <;>
      simp [he1, Nat.not_prime_one] at hp'

theorem isGalois_finrank_discr_adjoin_sqrt_neg_prime :
    ∀ (q : ℕ) (x : ℂ), q.Prime → q % 4 = 3 → x ^ 2 = -(q : ℂ) → ∀ [NumberField ℚ⟮x⟯],
      IsGalois ℚ ℚ⟮x⟯ ∧ Module.finrank ℚ ℚ⟮x⟯ = 2 ∧ (NumberField.discr ℚ⟮x⟯).natAbs = q := by
  intro q x hq h4 hx _
  have hpm : (X ^ 2 + C (q : ℚ)).Monic := by monicity!
  have hpd : (X ^ 2 + C (q : ℚ)).natDegree = 2 := by compute_degree!
  have h0 : aeval x (X ^ 2 + C (q : ℚ)) = 0 := by simp [hx]
  have hmin := minpoly_eq_of_quadratic_irrational _ hpm hpd x h0
    (sqrtNeg_not_mem_range q hq.pos x hx)
  have hfin : Module.finrank ℚ ℚ⟮x⟯ = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) ⟨_, hpm, h0⟩
    rw [← hmin, hpd] at this
    exact this
  have : Algebra.IsQuadraticExtension ℚ ℚ⟮x⟯ := ⟨hfin⟩
  refine ⟨Algebra.IsQuadraticExtension.isGalois _ _, hfin, ?_⟩
  refine natAbs_discr_of_sq_eq_neg_prime ℚ⟮x⟯ q hq h4 (AdjoinSimple.gen ℚ x) ?_ hfin
  apply Subtype.ext
  simpa using hx

end GlobalTheory
end

section

namespace GlobalTheory

private lemma ringHom_pow_sub_mem_span {A O : Type} [CommRing A] [CommRing O] (g : ℕ)
    (hA : ∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) (σ : A →+* O) (x : A) :
    σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA x)
  exact Ideal.mem_span_singleton'.mpr
    ⟨σ c, by rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]⟩

theorem _root_.GlobalTheory.exists_separating_mod_prime_pow : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (T : Type) [Fintype T] [DecidableEq T] (σ : T → A →+* O), Function.Injective σ → ∀ (K : ℕ) (t₀ : T), ∃ e : A, ∀ t, σ t e - (if t = t₀ then 1 else 0) ∈ Ideal.span {(g : O) ^ K} := by
  intro A O _ _ _ _ g hg hgO hA T _ _ σ hσ K t₀
  have h2 : 2 ≤ g := hg.two_le
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hb : ∀ t, t ≠ t₀ → ∃ b : A, σ t b ∈ Ideal.span {(g : O)} ∧ IsUnit (σ t₀ b) := by
    intro t ht
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne A O g hg hgO hA (σ t₀) (σ t)
      (fun h => ht (hσ h).symm)
    obtain ⟨⟨i, hi⟩, -⟩ := _root_.GlobalTheory.hom_value_congruent_int_mod_prime A O g hg hgO hA (σ t) a
    refine ⟨a - (i : A), by rwa [map_sub, map_intCast], ?_⟩
    rw [map_sub, map_intCast]
    by_contra hn
    have h1 : σ t₀ a - (i : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hn)
    have h3 : σ t₀ a - σ t a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 (hspan hi)
      rwa [sub_sub_sub_cancel_right] at this
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) ha
  choose! b hb1 hb2 using hb
  obtain ⟨c, hc0, hct⟩ : ∃ c : A, IsUnit (σ t₀ c) ∧ ∀ t, t ≠ t₀ → σ t c ∈ Ideal.span {(g : O)} := by
    refine ⟨∏ t ∈ Finset.univ.erase t₀, b t, ?_, fun t ht => ?_⟩
    · rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun t ht => hb2 t (Finset.ne_of_mem_erase ht))
    · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)]
      exact Ideal.mul_mem_right _ _ (hb1 t ht)
  obtain ⟨f, hf0, hft⟩ : ∃ f : A, σ t₀ f - 1 ∈ Ideal.span {(g : O)} ∧
      ∀ t, t ≠ t₀ → σ t f ∈ Ideal.span {(g : O)} := by
    refine ⟨c ^ (g - 1), ?_, fun t ht => ?_⟩
    · rw [map_pow]
      have hz : σ t₀ c * (σ t₀ c ^ (g - 1) - 1) = σ t₀ c ^ g - σ t₀ c := by
        rw [mul_sub, mul_one, ← pow_succ']
        congr 2
        omega
      have : σ t₀ c ^ (g - 1) - 1 = (σ t₀ c ^ g - σ t₀ c) * ↑hc0.unit⁻¹ := by
        rw [← hz, mul_comm (σ t₀ c), mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (ringHom_pow_sub_mem_span g hA (σ t₀) c)
    · rw [map_pow]
      exact Ideal.pow_mem_of_mem _ (hct t ht) _ (by omega)
  refine ⟨1 - (1 - f ^ K) ^ K, fun t => ?_⟩
  rw [← Ideal.span_singleton_pow]
  split_ifs with ht
  · subst ht
    simp only [map_sub, map_one, map_pow]
    have h1 : 1 - σ t f ^ K ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hf0 ⊢
      rw [map_sub, map_one, map_pow]
      rw [map_sub, map_one, sub_eq_zero] at hf0
      rw [hf0, one_pow, sub_self]
    have : 1 - (1 - σ t f ^ K) ^ K - 1 = -((1 - σ t f ^ K) ^ K) := by ring
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow h1 K)
  · simp only [map_sub, map_one, map_pow]
    have hw : σ t f ^ K ∈ Ideal.span {(g : O)} ^ K := Ideal.pow_mem_pow (hft t ht) K
    have hgs := geom_sum_mul (1 - σ t f ^ K) K
    have : 1 - (1 - σ t f ^ K) ^ K - 0 =
        (∑ i ∈ Finset.range K, (1 - σ t f ^ K) ^ i) * σ t f ^ K := by
      linear_combination hgs
    rw [this]
    exact Ideal.mul_mem_left _ _ hw

end GlobalTheory
end
