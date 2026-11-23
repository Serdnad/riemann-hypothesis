module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Analysis.Complex.Norm
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.HDSucc
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem soutPart_pos (m₀ N : ℕ) : 0 < soutPart m₀ N := by
  unfold soutPart
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem soutPart_squarefree (m₀ N : ℕ) : Squarefree (soutPart m₀ N) := by
  unfold soutPart
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_) fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr

theorem soutPart_coprime (m₀ N : ℕ) : (soutPart m₀ N).Coprime m₀ := by
  unfold soutPart
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).mpr
      (Finset.mem_filter.mp hp).2.2

theorem soutPart_odd (m₀ N : ℕ) (h2 : 2 ∣ m₀) : Odd (soutPart m₀ N) := by
  exact Nat.coprime_two_right.mp ((soutPart_coprime m₀ N).coprime_dvd_right h2)

theorem soutPart_dvd (m₀ N : ℕ) : soutPart m₀ N ∣ N := by
  unfold soutPart
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd N)

theorem soutPart_le (m₀ N : ℕ) (hN : 0 < N) : soutPart m₀ N ≤ N := by
  exact Nat.le_of_dvd hN (soutPart_dvd m₀ N)

theorem jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, jacobiSym.mul_left, ih]

theorem jacobiSym_prod_right {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
    rw [Finset.prod_cons, Finset.prod_cons,
      jacobiSym.mul_right' _ (hf a (Finset.mem_cons.mpr (Or.inl rfl))) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

theorem recip_sign_congr (p q q' : ℕ) (h4 : q % 4 = q' % 4) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ (p / 2 * (q' / 2)) := by
  have h : (q / 2) % 2 = (q' / 2) % 2 := by omega
  calc ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ ((p / 2 * (q / 2)) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ ((p / 2 * (q' / 2)) % 2) := by rw [Nat.mul_mod, h, ← Nat.mul_mod]
    _ = (-1) ^ (p / 2 * (q' / 2)) := (neg_one_pow_eq_pow_mod_two _).symm

theorem gcd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by
  have h := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]
    exact h
  · rw [Int.gcd_natCast_natCast]
    exact h.symm

theorem jacobi_prime_in {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : p ∣ m₀) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q = jacobiSym (p : ℤ) q' := by
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  rcases hp.eq_two_or_odd' with rfl | hpo
  · have h8m : q % 8 = q' % 8 := Nat.ModEq.of_dvd h8 hqq
    have hz : (q : ZMod 8) = (q' : ZMod 8) := (ZMod.natCast_eq_natCast_iff' q q' 8).mpr h8m
    simp only [Nat.cast_ofNat]
    rw [jacobiSym.at_two hqo, jacobiSym.at_two hq'o, hz]
  · have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
    have hpm' : q % p = q' % p := Nat.ModEq.of_dvd hpm hqq
    rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o,
      recip_sign_congr p q q' h4, jacobiSym.mod_left (q : ℤ), jacobiSym.mod_left (q' : ℤ),
      ← Int.natCast_mod, ← Int.natCast_mod, hpm']

theorem jacobi_prime_out {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : ¬ p ∣ m₀) (hq : q.Prime)
    (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p = jacobiSym (p : ℤ) q' * jacobiSym (q' : ℤ) p := by
  have hp2 : p ≠ 2 := fun h => hpm (h ▸ dvd_trans (by norm_num) h8)
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hpo := hp.odd_of_ne_two hp2
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
  have s1 : jacobiSym (q : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq hpq).2
  have s2 : jacobiSym (q' : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq' hpq').2
  rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o, mul_assoc, mul_assoc,
    ← sq, ← sq, s1, s2, recip_sign_congr p q q' h4]

theorem jacobi_class_prod (m₀ N q : ℕ) (hN : 0 < N) :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      ∏ p ∈ N.primeFactors, (jacobiSym (p : ℤ) q ^ (N.factorization p) *
        (if Odd (N.factorization p) ∧ ¬ p ∣ m₀ then jacobiSym (q : ℤ) p else 1)) := by
  have hNfac : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN.ne']
    rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hNfac, jacobiSym_prod_left]
  unfold soutPart
  rw [jacobiSym_prod_right _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero,
    Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [jacobiSym.pow_left]

theorem jacobi_class_congr {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by
  rw [jacobi_class_prod m₀ N q hN, jacobi_class_prod m₀ N q' hN]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpN : p ≤ N := Nat.le_of_mem_primeFactors hp
  have hpq : p < q := by omega
  have hpq' : p < q' := by omega
  by_cases hpm : p ∣ m₀
  · rw [if_neg (fun h => h.2 hpm), if_neg (fun h => h.2 hpm), mul_one, mul_one,
      jacobi_prime_in h8 hpP hpm hq hq' hqq hpq hpq']
  · have hsq : ∀ r : ℕ, r.Prime → p < r → jacobiSym (p : ℤ) r ^ 2 = 1 := fun r hr hpr =>
      jacobiSym.sq_one (gcd_prime_lt hpP hr hpr).1
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N.factorization p)
    · have hnodd : ¬ Odd (N.factorization p) := Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      rw [if_neg (fun h => hnodd h.1), if_neg (fun h => hnodd h.1), mul_one, mul_one, hk, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow]
    · have hodd : Odd (N.factorization p) := ⟨k, hk⟩
      rw [if_pos ⟨hodd, hpm⟩, if_pos ⟨hodd, hpm⟩, hk, pow_succ, pow_succ, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow, one_mul, one_mul]
      exact jacobi_prime_out h8 hpP hpm hq hq' hqq hpq hpq'

theorem jacobi_class (m₀ a₀ N : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hN : 0 < N) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ q : ℕ, q.Prime → q % m₀ = a₀ % m₀ → N < q →
      jacobiSym (N : ℤ) q = σ * jacobiSym (q : ℤ) (soutPart m₀ N) := by
  have hcop1 : ∀ q : ℕ, q.Prime → N < q → (N : ℤ).gcd q = 1 := by
    intro q hq hNq
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => absurd (Nat.le_of_dvd hN h) (by omega)).symm
  have hcop2 : ∀ q : ℕ, q.Prime → N < q → (q : ℤ).gcd (soutPart m₀ N) = 1 := by
    intro q hq hNq
    have hle := soutPart_le m₀ N hN
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd (soutPart_pos m₀ N) h) (by omega)
  by_cases hex : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ % m₀ = a₀ % m₀ ∧ N < q₀
  · obtain ⟨q₀, hq₀, hq₀m, hNq₀⟩ := hex
    refine ⟨jacobiSym (N : ℤ) q₀ * jacobiSym (q₀ : ℤ) (soutPart m₀ N), ?_, fun q hq hqm hNq => ?_⟩
    · rcases jacobiSym.eq_one_or_neg_one (hcop1 q₀ hq₀ hNq₀) with h | h <;>
        rcases jacobiSym.eq_one_or_neg_one (hcop2 q₀ hq₀ hNq₀) with h' | h' <;> simp [h, h']
    · have hc := jacobi_class_congr h8 hN hq hq₀ (hqm.trans hq₀m.symm) hNq hNq₀
      have hsq : jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 = 1 := jacobiSym.sq_one (hcop2 q hq hNq)
      rw [← hc]
      calc jacobiSym (N : ℤ) q = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 := by
            rw [hsq, mul_one]
        _ = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) * jacobiSym (q : ℤ) (soutPart m₀ N) := by
            ring
  · exact ⟨1, Or.inl rfl, fun q hq hqm hNq => absurd ⟨q, hq, hqm, hNq⟩ hex⟩

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem prodLower (n : ℕ) (z : Fin n → ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ξ : ℂ) (hξ : ‖ξ‖ = ρ⁻¹) :
    ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| ≤ ‖∏ i, (1 - z i * ξ)‖ := by
  have hfac : ∀ i, ρ⁻¹ * |ρ - ‖z i‖| ≤ ‖1 - z i * ξ‖ := by
    intro i
    have h1 : ρ⁻¹ * (ρ - ‖z i‖) = 1 - ‖z i‖ * ρ⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hρ.ne']; ring
    have h2 : ρ⁻¹ * |ρ - ‖z i‖| = |1 - ‖z i‖ * ρ⁻¹| := by
      rw [← h1, abs_mul, abs_of_pos (inv_pos.mpr hρ)]
    rw [h2]
    calc |1 - ‖z i‖ * ρ⁻¹| = |‖(1 : ℂ)‖ - ‖z i * ξ‖| := by rw [norm_one, norm_mul, hξ]
      _ ≤ ‖1 - z i * ξ‖ := abs_norm_sub_norm_le _ _
  calc ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| = ∏ i, (ρ⁻¹ * |ρ - ‖z i‖|) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, ‖1 - z i * ξ‖ :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg (inv_nonneg.mpr hρ.le) (abs_nonneg _))
          (fun i _ => hfac i)
    _ = ‖∏ i, (1 - z i * ξ)‖ := (norm_prod Finset.univ _).symm

theorem turan2Main (n m : ℕ) (z : Fin n → ℂ) (hn : 1 ≤ n) (hz : ∀ i, ‖z i‖ ≤ 1) (hz1 : ∃ i, ‖z i‖ = 1) :
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + n ∧ ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n ≤ ‖∑ i, z i ^ k‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hz1
  set B : ℝ := ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n with hBdef
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hM : (0 : ℝ) < (m : ℝ) + n := by linarith
  have hnM : (n : ℝ) ≤ (m : ℝ) + n := by linarith
  have hq1 : m + 1 ≤ (m + n) / n * n := by
    have h1 := Nat.div_add_mod (m + n) n
    have h2 := Nat.mod_lt (m + n) (show n > 0 by omega)
    rw [Nat.mul_comm] at h1
    generalize (m + n) / n * n = Q at h1 ⊢
    generalize (m + n) % n = t at h1 h2
    omega
  have hq2 : (((m + n) / n : ℕ) : ℝ) * (n : ℝ) ≤ (m : ℝ) + n := by
    exact_mod_cast Nat.div_mul_le_self (m + n) n
  set q : ℕ := (m + n) / n with hqdef
  set M : ℝ := (m : ℝ) + n with hMdef
  set r : ℝ := (n : ℝ) / (6 * M) with hr
  have hr0 : 0 < r := div_pos (by linarith) (by linarith)
  have hr6 : r ≤ 1 / 6 := by
    rw [hr, div_le_iff₀ (by linarith)]; linarith
  obtain ⟨ρ, hρc, hP⟩ := prodDist (fun i : Fin n => ‖z i‖) Finset.univ (1 - 2 * r) r hr0
  have hP' : (r / 25) ^ n ≤ ∏ j : Fin n, |ρ - ‖z j‖| := by
    have h := hP
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  set P : ℝ := ∏ j : Fin n, |ρ - ‖z j‖| with hPdef
  have hρlo : 1 - 3 * r ≤ ρ := by have := (abs_le.mp hρc).1; linarith
  have hρhi : ρ ≤ 1 - r := by have := (abs_le.mp hρc).2; linarith
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hP0 : 0 < P := lt_of_lt_of_le (pow_pos (div_pos hr0 (by norm_num)) n) hP'
  have hρq : (1 : ℝ) / 2 ≤ ρ ^ q := by
    have hb := one_add_mul_le_pow (a := ρ - 1) (by linarith) q
    have he : 1 + (ρ - 1) = ρ := by ring
    rw [he] at hb
    have h3 : (q : ℝ) * (3 * r) ≤ 1 / 2 := by
      have he2 : (q : ℝ) * (3 * r) = ((q : ℝ) * n) / (2 * M) := by rw [hr]; ring_nf
      rw [he2, div_le_iff₀ (by linarith)]; linarith
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - ρ ≤ 3 * r by linarith) hq0]
  have hρm : (1 / 2 : ℝ) ^ n ≤ ρ ^ (m + 1) := by
    calc (1 / 2 : ℝ) ^ n ≤ (ρ ^ q) ^ n := pow_le_pow_left₀ (by norm_num) hρq n
      _ = ρ ^ (q * n) := (pow_mul ρ q n).symm
      _ ≤ ρ ^ (m + 1) := pow_le_pow_of_le_one hρ0.le hρ1.le hq1
  have hkey : (n : ℝ) * (2 ^ n * B) < ρ ^ (m + 1) * P := by
    have hlow : ((n : ℝ) / (300 * M)) ^ n ≤ ρ ^ (m + 1) * P := by
      calc ((n : ℝ) / (300 * M)) ^ n = (1 / 2 : ℝ) ^ n * (r / 25) ^ n := by
            rw [← mul_pow]; congr 1; rw [hr]; ring_nf
        _ ≤ ρ ^ (m + 1) * P :=
            mul_le_mul hρm hP' (pow_pos (div_pos hr0 (by norm_num)) n).le (pow_pos hρ0 _).le
    have hB : (n : ℝ) * (2 ^ n * B) = n * ((3 / 8 : ℝ) ^ n * ((n : ℝ) / (300 * M)) ^ n) := by
      rw [hBdef, ← mul_pow, ← mul_pow]; congr 2; ring_nf
    have hY : 0 < ((n : ℝ) / (300 * M)) ^ n := pow_pos (div_pos (by linarith) (by linarith)) n
    have hsmall : (n : ℝ) * (3 / 8 : ℝ) ^ n < 1 := by
      have hb := one_add_mul_le_pow (a := (5 / 3 : ℝ)) (by norm_num) n
      have h83 : (1 + 5 / 3 : ℝ) = 8 / 3 := by norm_num
      rw [h83] at hb
      have hone : (3 / 8 : ℝ) ^ n * (8 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
      have hpos : (0 : ℝ) < (3 / 8) ^ n := pow_pos (by norm_num) n
      nlinarith [mul_le_mul_of_nonneg_left hb hpos.le]
    calc (n : ℝ) * (2 ^ n * B) = n * ((3 / 8 : ℝ) ^ n * ((n : ℝ) / (300 * M)) ^ n) := hB
      _ = (n * (3 / 8 : ℝ) ^ n) * ((n : ℝ) / (300 * M)) ^ n := by ring
      _ < 1 * ((n : ℝ) / (300 * M)) ^ n := mul_lt_mul_of_pos_right hsmall hY
      _ = ((n : ℝ) / (300 * M)) ^ n := one_mul _
      _ ≤ ρ ^ (m + 1) * P := hlow
  set ξ : ℂ := ((ρ⁻¹ : ℝ) : ℂ) with hξdef
  have hξ : ‖ξ‖ = ρ⁻¹ := by
    rw [hξdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
  have hρinv1 : 1 < ρ⁻¹ := by
    have hc : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith [inv_pos.mpr hρ0]
  have hzρ : ∀ i, ‖z i‖ * ρ⁻¹ ≠ 1 := by
    intro i h
    have hzi : ‖z i‖ = ρ := by
      have h' : ‖z i‖ * ρ⁻¹ * ρ = 1 * ρ := by rw [h]
      rwa [mul_assoc, inv_mul_cancel₀ hρ0.ne', mul_one, one_mul] at h'
    have hP00 : P = 0 := by
      rw [hPdef]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hzi])
    linarith
  set y : Fin n → ℂ := fun i => z i * ξ with hydef
  have hyn : ∀ i, ‖y i‖ = ‖z i‖ * ρ⁻¹ := fun i => by
    show ‖z i * ξ‖ = _
    rw [norm_mul, hξ]
  have hy : ∀ i, ‖y i‖ ≠ 1 := fun i => by rw [hyn]; exact hzρ i
  have hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ B := fun k h1 h2 => (hcon k h1 h2).le
  have hRP : 0 < ρ ^ (m + 1) * P := mul_pos (pow_pos hρ0 _) hP0
  set K : ℝ := ((n : ℝ) * (2 ^ n * B)) / (ρ ^ (m + 1) * P) with hK
  have hKlt : K < 1 := by rw [hK, div_lt_one hRP]; exact hkey
  have hbound : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ (m + 1) / (1 - y i * ζ)‖ ≤ K := by
    intro ζ hζ
    have hnζ' : ‖ξ * ζ‖ = ρ⁻¹ := by rw [norm_mul, hξ, hζ, mul_one]
    have hsum : ∑ i, (y i * ζ) ^ (m + 1) / (1 - y i * ζ)
        = ∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hyz : y i * ζ = z i * (ξ * ζ) := by
        show z i * ξ * ζ = z i * (ξ * ζ)
        ring
      rw [hyz]
    rw [hsum]
    have hne : ∀ i, 1 - z i * (ξ * ζ) ≠ 0 := by
      intro i h
      have h1 : z i * (ξ * ζ) = 1 := (sub_eq_zero.mp h).symm
      have h2 : ‖z i * (ξ * ζ)‖ = 1 := by rw [h1, norm_one]
      rw [norm_mul, hnζ'] at h2
      exact hzρ i h2
    have hA := prodLower n z ρ hρ0 (ξ * ζ) hnζ'
    have hmain := Tbound n m hn z hz B hβ (ξ * ζ) (by rw [hnζ']; exact hρinv1.le) hne
    rw [hnζ'] at hmain
    have hS0 : 0 ≤ ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ := norm_nonneg _
    have h1 : ρ⁻¹ ^ n * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
        ≤ ρ⁻¹ ^ n * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) := by
      calc ρ⁻¹ ^ n * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
            = (ρ⁻¹ ^ n * P) * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ := by ring
        _ ≤ ‖∏ i, (1 - z i * (ξ * ζ))‖ * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ :=
            mul_le_mul_of_nonneg_right hA hS0
        _ ≤ ρ⁻¹ ^ (m + 1) * (n * (ρ⁻¹ ^ n * (2 ^ n * B))) := hmain
        _ = ρ⁻¹ ^ n * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) := by ring
    have h2 : P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖
        ≤ ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B)) :=
      le_of_mul_le_mul_left h1 (pow_pos (inv_pos.mpr hρ0) n)
    have h3 : ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
        ≤ n * (2 ^ n * B) := by
      calc ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
            ≤ ρ ^ (m + 1) * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) :=
            mul_le_mul_of_nonneg_left h2 (pow_pos hρ0 _).le
        _ = (ρ * ρ⁻¹) ^ (m + 1) * (n * (2 ^ n * B)) := by rw [mul_pow]; ring
        _ = n * (2 ^ n * B) := by rw [mul_inv_cancel₀ hρ0.ne', one_pow, one_mul]
    rw [hK, le_div_iff₀ hRP]
    calc ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ * (ρ ^ (m + 1) * P)
          = ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖) := by ring
      _ ≤ n * (2 ^ n * B) := h3
  have hcard := avgLimit y hy (m + 1) (by omega) K hbound
  have hmem : i0 ∈ Finset.univ.filter (fun i => 1 < ‖y i‖) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hyn, hi0, one_mul]
    exact hρinv1
  have hpos : 0 < (Finset.univ.filter (fun i => 1 < ‖y i‖)).card := Finset.card_pos.mpr ⟨i0, hmem⟩
  have hone : (1 : ℝ) ≤ ((Finset.univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by exact_mod_cast hpos
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end
