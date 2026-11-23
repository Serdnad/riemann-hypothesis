module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.FinWeil

noncomputable def ofPrimeValues (u : ℕ → ℂ) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun q k => u q ^ k
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Nat.factorization_mul ha hb,
      Finsupp.prod_add_index' (by simp) (fun q k l => pow_add _ _ _)]

theorem ofPrimeValues_prime (u : ℕ → ℂ) {q : ℕ} (hq : q.Prime) : ofPrimeValues u q = u q := by
  show (if q = 0 then 0 else q.factorization.prod fun q k => u q ^ k) = u q
  rw [if_neg hq.ne_zero, hq.factorization, Finsupp.prod_single_index (by simp), pow_one]

theorem sqrt_pow_nat (q f : ℕ) : ((Real.sqrt q : ℝ) : ℂ) ^ f = (Real.sqrt ((q ^ f : ℕ) : ℝ) : ℂ) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, ih, pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

theorem exists_lam (S : ℕ → Prop) (f : ℕ → ℕ) :
    ∃ lam : ℕ →* ℂ, (∀ n, n ≠ 0 → lam n ≠ 0) ∧
      (∀ q, q.Prime → f q ≠ 0 → S q → lam (q ^ f q) = -(Real.sqrt ((q ^ f q : ℕ) : ℝ) : ℂ)) ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → S q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  let u : ℕ → ℂ := fun q =>
    (Real.sqrt q : ℂ) * if S q then Complex.exp (Real.pi * Complex.I / f q) else 1
  refine ⟨ofPrimeValues u, fun n => ?_, fun q hq hf hS => ?_, fun n => ?_⟩
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _
      rw [ofPrimeValues_prime u hq]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hq.pos)).ne'
      · split_ifs
        · exact Complex.exp_ne_zero _
        · exact one_ne_zero
    | mul a b ha hb =>
      intro h
      rw [map_mul]
      exact mul_ne_zero (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  · rw [map_pow, ofPrimeValues_prime u hq]
    simp only [u, if_pos hS]
    have hf' : (f q : ℂ) ≠ 0 := by exact_mod_cast hf
    rw [mul_pow, sqrt_pow_nat, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hf', Complex.exp_pi_mul_I]
    ring
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _ h
      have hS : ¬ S q := fun hS => h q hq hS dvd_rfl
      rw [ofPrimeValues_prime u hq]
      simp only [u, if_neg hS, mul_one]
    | mul a b ha hb =>
      intro h h'
      rw [map_mul, ha (left_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_right _),
        hb (right_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_left _), Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

theorem exists_card_eq_pow {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ P ∧
      (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) ≠ 0 ∧
      Nat.card (𝓞 E ⧸ P) = q ^ (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) := by
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨p, hp, hPp⟩ :=
    (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have h1 := Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (E ≃ₐ[ℚ] E)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have : (p : ℤ) ∈ P.under ℤ := hPp ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this
  · rw [h1]; exact (Ideal.inertiaDeg_pos P ℤ).ne'
  · rw [h1, Ideal.pow_inertiaDeg p P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem exists_goodNorm : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  intro D
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  obtain ⟨lam, h0, h1, h2⟩ := exists_lam (InertQ D)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 D.host.E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨q, hq, hqP, hf, hc⟩ := exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · rw [hc]
    by_cases hI : InertQ D q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · have hfix : D.host.conj • P = P := by
      have hP' : (D.host.conj • P).IsMaximal := by
        rcases Ideal.map_eq_top_or_isMaximal_of_surjective (sgO D)
          (MulAction.surjective D.host.conj) hP with h | h
        · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) D.host.conj).ne_top
        · exact h
      exact hP'.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.2 fun r hr => h r hr)
    have hI : InertQ D q := fun Q hQ _ hqQ =>
      GlobalTheory.SelectIdem.smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ hqP hqQ hfix
    rw [hc]
    exact h1 q hq hf hI
  · have := D.host.der.unramEF P hP.isPrime hP0
    push Not at this
    exact this

end GlobalTheory.FinWeil
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertResidue

theorem card_of_involution {k : Type} [Field k] [Finite k] {q : ℕ} [Fact q.Prime] [CharP k q] (s : k →+* k)
    (hs : ∀ x, s (s x) = x) {r : k} {m : ℤ} (hr : r ^ 2 = m) (hsr : s r = -r) (hne : -r ≠ r) :
    (∃ f, Odd f ∧ Nat.card k = q ^ (2 * f)) ∧ ¬ IsSquare (m : ZMod q) := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  haveI := Fintype.ofFinite k
  let σ : k ≃ₐ[ZMod q] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs, map_mul' := map_mul s, map_add' := map_add s,
      commutes' := fun c => RingHom.congr_fun (Subsingleton.elim (s.comp (algebraMap (ZMod q) k)) _) c }
  have hσ : ∀ x, σ x = s x := fun _ => rfl
  constructor
  · obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) k).2 σ
    set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k with hφ
    change φ ^ j = σ at e
    have ho : orderOf φ = Module.finrank (ZMod q) k := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod q) k
    have h2 : φ ^ (2 * j) = 1 := by
      rw [two_mul, pow_add, e]; ext x; exact hs x
    have hsq : (φ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr, map_intCast]
    have hev : ∀ i, (φ ^ (2 * i)) r = r := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [mul_add, pow_add, AlgEquiv.mul_apply, mul_one, sq, AlgEquiv.mul_apply]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
        · rw [h, h, ih]
        · rw [h, map_neg, h, neg_neg, ih]
    have hodd : Odd j := by
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · exact absurd (by rw [← hsr, ← hσ, ← e, hev]) hne
      · exact ⟨i, rfl⟩
    refine ⟨j, hodd, ?_⟩
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at hd
    have hn : Module.finrank (ZMod q) k = 2 * j := by
      obtain ⟨c, hc⟩ := hd
      have hj0 := hodd.pos
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith [Nat.zero_le (Module.finrank (ZMod q) k * c)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), hn, Nat.card_zmod]
  · rintro ⟨c, hc⟩
    have h1 : r ^ 2 = (algebraMap (ZMod q) k c) ^ 2 := by rw [hr, sq, ← map_mul, ← hc, map_intCast]
    apply hne
    rw [← hsr, ← hσ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp

theorem exists_root (D : D7) (n : ℕ) (b : D.host.E) (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ r : 𝓞 D.host.E, r ^ 2 = ((-(n : ℤ) : ℤ) : 𝓞 D.host.E) ∧ D.host.conj • r = -r := by
  have hint : IsIntegral ℤ b := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hb]
    exact (isIntegral_natCast n).neg
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  refine ⟨⟨b, hint⟩, RingOfIntegers.ext ?_, RingOfIntegers.ext hconj⟩
  have : (((-(n : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) = ((-(n : ℤ) : ℤ) : D.host.E) :=
    map_intCast (algebraMap (𝓞 D.host.E) D.host.E) _
  rw [this]
  push_cast
  exact hb

theorem two_not_mem (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsPrime) (hsP : ∀ x ∈ P, D.host.conj • x ∈ P) :
    (2 : 𝓞 D.host.E) ∉ P := by
  intro h2
  have hw : D.host.conj • (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := by
    rw [← Formalism.L2.Pj.conj_w0E D]
    exact RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D (Formalism.L2.Pj.w0E D)).symm
  have hsq := Formalism.L2.Pj.w0E_sq D
  obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
    have h1 := D.host.hyp.2.2.2.1
    have h3 := Formalism.L2.Pj.mE_spec D
    exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
  rw [hk] at hsq
  push_cast at hsq
  set w := Formalism.L2.Pj.w0E D
  have hm : w * (1 - w) ∈ P := by
    have : w * (1 - w) = k * 2 := by linear_combination -hsq
    rw [this]; exact P.mul_mem_left _ h2
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hP.mem_or_mem hm with h | h
  · have h' := hsP _ h
    rw [hw] at h'
    simpa using P.add_mem h h'
  · have h' := hsP _ h
    rw [smul_sub, smul_one, hw] at h'
    simpa using P.add_mem h h'

theorem card_of_root (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hfix : D.host.conj • P = P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 D.host.E) ∈ P) (n : ℕ) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    (∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f)) ∧ ¬ IsSquare (-(n : ZMod q)) := by
  have hsP : ∀ x ∈ P, D.host.conj • x ∈ P := fun x hx => by
    rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  obtain ⟨r, hr, hsr⟩ := exists_root D n b hb
  haveI := Fact.mk hq
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI : CharP (𝓞 D.host.E ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hqP)
  let c := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj
  let s : 𝓞 D.host.E ⧸ P →+* 𝓞 D.host.E ⧸ P := Ideal.quotientMap P c hsP
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (D.host.conj • x) := fun _ => rfl
  have h := card_of_involution (q := q) s (r := Ideal.Quotient.mk P r) (m := -(n : ℤ))
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, smul_smul, VacInt.conj_mul_self, one_smul])
    (by rw [← map_pow, hr, map_intCast]) (by rw [hs, hsr, map_neg])
    (fun h => by
      rw [← map_neg, Ideal.Quotient.eq] at h
      have h2 : 2 * r ∈ P := by
        have := P.neg_mem h
        convert this using 1
        ring
      have h3 := (hP.isPrime.mem_or_mem h2).resolve_left (two_not_mem D hP.isPrime hsP)
      have hnP : (n : 𝓞 D.host.E) ∈ P := by
        have := P.neg_mem (hr ▸ P.pow_mem_of_mem h3 2 two_pos)
        simpa using this
      obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2
        (huv ▸ P.add_mem (P.mul_mem_left u hqP) (P.mul_mem_left v hnP))))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast at h
  exact h

theorem exists_prime (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    ∃ q n : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ Ideal.absNorm P = q ^ n := by
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ P)
  obtain ⟨q, hc, n, hq, hn⟩ := FiniteField.card' (𝓞 D.host.E ⧸ P)
  refine ⟨q, n, hq, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]

theorem norm_prime : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  intro D P hP
  obtain ⟨q, n, hq, hqP, hn⟩ := exists_prime D hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  by_cases hfix : D.host.conj • P = P
  · have hin : InertQ D q := by
      by_contra h
      exact VacInt.conj_smul_ne D hq h P hP.isPrime hqP hfix
    obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
    have hd' : q ≠ D.host.d → _ := fun h => card_of_root D hP hfix hq hqP D.host.d
      ((Nat.coprime_primes hq hd).2 h) (D.host.sqd)
      (D.host.sqd_sq)
    obtain ⟨f, hf, hN⟩ : ∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f) := by
      by_cases h : q = D.host.d
      · exfalso
        haveI := hP.isPrime
        haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := by
          refine ⟨Ideal.IsMaximal.eq_of_le
            (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible)
            (Ideal.IsPrime.ne_top inferInstance) ?_⟩
          rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
          exact hqP
        exact D.host.der.decompConj q hq (h ▸ Dvd.intro_left _ rfl) P (MulAction.mem_stabilizer_iff.2 hfix)
      · exact (hd' h).1
    refine ⟨?_, fun _ => ⟨?_, q, f, hq, hin, ?_, hqP, hf, hN, fun h => (hd' h).2⟩, fun h => absurd hfix h⟩
    · intro p _ _
      rw [hN, Nat.factorization_pow]
      simp [Nat.even_mul]
    · have hf0 : 2 * f ≠ 0 := by have := hf.pos; omega
      rw [hN, sgn, hlf, Nat.primeFactors_prime_pow hf0 hq, Finset.filter_singleton, if_pos hin,
        Finset.sum_singleton, Nat.factorization_pow_self hq, Nat.mul_div_cancel_left _ two_pos, hf.neg_one_pow]
    · rintro rfl
      exact two_not_mem D hP.isPrime
        (fun x hx => by rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx) (by exact_mod_cast hqP)
  · have hall : ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ P → ¬ InertQ D p := fun p hp h => hfix (h P hP.isPrime hP0 hp)
    have h0 : ∀ p : ℕ, InertQ D p → (Ideal.absNorm P).factorization p = 0 := fun p hp => by
      rw [hn, hq.factorization_pow, Finsupp.single_eq_of_ne]
      rintro rfl
      exact hall _ hqP hp
    refine ⟨fun p _ hp => by rw [h0 p hp]; exact Even.zero, fun h => absurd h hfix, fun _ => ⟨?_, fun p _ hp => hall p hp⟩⟩
    rw [← sgn_one (D := D)]
    exact sgn_congr fun p _ hp => by rw [h0 p hp]; simp

end GlobalTheory.InertResidue
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LatticeProjection

theorem isLocalizedModule_subtype {O E V : Type*} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (B : Submodule O V) (hB : Submodule.span E (B : Set V) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) B.subtype := by
  refine ⟨fun s => ?_, fun v => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  · exact (isLocalizedModule_id (nonZeroDivisors O) V E).map_units s
  · have hv : v ∈ Submodule.span E (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E (B : Set V) v hv
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨t • v, ht⟩, t), rfl⟩

theorem exists_linear_projection {O E V : Type*} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (L₁ L₃ : Submodule O V) (h₁ : L₁.FG) (h₃ : L₃.FG)
    (hB : Submodule.span E ((L₁ ⊔ L₃ : Submodule O V) : Set V) = ⊤) :
    ∃ π : V →ₗ[E] V, ∀ v ∈ L₁ ⊔ L₃, π v ∈ L₁ ∧ v - π v ∈ L₃ := by
  set B := L₁ ⊔ L₃ with hBdef
  haveI : Module.Finite O B := Module.Finite.iff_fg.2 (h₁.sup h₃)
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O E V
  haveI : Module.FinitePresentation O B := Module.finitePresentation_of_finite O B
  haveI : Module.Flat O B := inferInstance
  haveI : Module.Projective O B := Module.Flat.projective_of_finitePresentation
  let p : (L₁ × L₃) →ₗ[O] B := LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hp : Function.Surjective p := by
    rintro ⟨v, hv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  let f : B →ₗ[O] V := L₁.subtype ∘ₗ LinearMap.fst O L₁ L₃ ∘ₗ s
  haveI := isLocalizedModule_subtype (E := E) B hB
  have hu := (isLocalizedModule_id (nonZeroDivisors O) V E).map_units
  let g : V →ₗ[O] V := IsLocalizedModule.lift (nonZeroDivisors O) B.subtype f hu
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun v hv => ?_⟩
  have hg : g v = ((s ⟨v, hv⟩).1 : V) := IsLocalizedModule.lift_apply (nonZeroDivisors O) B.subtype f hu ⟨v, hv⟩
  have hsum : ((s ⟨v, hv⟩).1 : V) + ((s ⟨v, hv⟩).2 : V) = v :=
    congrArg Subtype.val (LinearMap.congr_fun hs ⟨v, hv⟩)
  rw [LinearMap.extendScalarsOfIsLocalization_apply', hg]
  refine ⟨(s ⟨v, hv⟩).1.2, ?_⟩
  rw [sub_eq_of_eq_add' hsum.symm]
  exact (s ⟨v, hv⟩).2.2

theorem exists_matrix_projection : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ →
    ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧
      ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  intro D n L₁ L₃ h₁ h₃
  obtain ⟨f₁, s₁, -⟩ := (sd_iff D L₁).1 h₁
  obtain ⟨f₃, -, -⟩ := (sd_iff D L₃).1 h₃
  obtain ⟨π, hπ⟩ := exists_linear_projection (E := D.host.E) L₁ L₃ f₁ f₃
    (top_le_iff.1 (s₁ ▸ Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)))
  refine ⟨LinearMap.toMatrix' π, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>
    rw [LinearMap.toMatrix'_mulVec]
  · exact (hπ v hv).1
  · simpa using L₃.sub_mem hv (hπ v (Submodule.mem_sup_right hv)).2
  · exact (hπ v (Submodule.mem_sup_left hv)).2

end GlobalTheory.LatticeProjection
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) → (∀ j, Differentiable ℂ (g' j)) → (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) → (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) → CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c)) (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  first | exact @GlobalTheory.ThetaConj.ProdLin.cjF_prod | exact GlobalTheory.ThetaConj.ProdLin.cjF_prod | (intros; apply GlobalTheory.ThetaConj.ProdLin.cjF_prod <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  first | exact @GlobalTheory.ThetaConj.corr_lattice | exact GlobalTheory.ThetaConj.corr_lattice | (intros; apply GlobalTheory.ThetaConj.corr_lattice <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaIntertwiner_pair_eq_sum_corresponding_representatives : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (A₁ A₂ A₁' A₂' : AddSubgroup (VC D N N')) (F F' : VC D N N' → ℂ) (R : VC D N N' → VC D N N' → Prop), (A₁.addSubgroupOf A₂).FiniteIndex → RepInd D T A₁ A₂ F → RepInd D T' A₁' A₂' F' → (∀ x ∈ A₂, ∃ x' ∈ A₂', R x x') → (∀ x' ∈ A₂', ∃ x ∈ A₂, R x x') → (∀ x x' y y', R x x' → R y y' → (x - y ∈ A₁ ↔ x' - y' ∈ A₁')) → ∃ (n : ℕ) (x x' : Fin n → VC D N N'), (∀ i, x i ∈ A₂ ∧ x' i ∈ A₂' ∧ R (x i) (x' i)) ∧ Iop D T A₁ A₂ F = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) ∧ Iop D T' A₁' A₂' F' = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T' (x' i) F' z) := by
  first | exact @GlobalTheory.ThetaConj.IopRepr.iop_pair | exact GlobalTheory.ThetaConj.IopRepr.iop_pair | (intros; apply GlobalTheory.ThetaConj.IopRepr.iop_pair <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.twistedTranslateClassInvariant_of_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N')) (F : VC D N N' → ℂ), (∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) → F ∈ ThSp D T A₁ → RepInd D T A₁ A₂ F := by
  first | exact @GlobalTheory.ThetaConj.repInd_of_thSp | exact GlobalTheory.ThetaConj.repInd_of_thSp | (intros; apply GlobalTheory.ThetaConj.repInd_of_thSp <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.oddThetaFunction_existence_uniqueness : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  first | exact @GlobalTheory.OddTheta.sgStar_laws | exact GlobalTheory.OddTheta.sgStar_laws | (intros; apply GlobalTheory.OddTheta.sgStar_laws <;> assumption)
end
