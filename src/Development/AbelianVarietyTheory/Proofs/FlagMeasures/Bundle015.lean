module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GlobalTheory.LocalGenerators

theorem local_gen {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ (0 : R) ∧ ∃ s ∉ P.asIdeal, ∀ y ∈ J, ∃ o : R, s * y = o * d := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : ¬ J ≤ J * P.asIdeal := by
    intro h
    have heq : J * P.asIdeal = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
    exact hP (mul_left_cancel₀ hJ heq)
  obtain ⟨d, hdJ, hdn⟩ := SetLike.not_le_iff_exists.mp hlt
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hdn (Submodule.zero_mem _)
  have hdvd : J ∣ Ideal.span {d} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  obtain ⟨K, hK⟩ := hdvd
  have hKP : ¬ K ≤ P.asIdeal := by
    intro h
    apply hdn
    have : Ideal.span {d} ≤ J * P.asIdeal := hK ▸ Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self d)
  obtain ⟨s, hsK, hsP⟩ := SetLike.not_le_iff_exists.mp hKP
  refine ⟨d, hdJ, hd0, s, hsP, ?_⟩
  intro y hy
  have hm : s * y ∈ Ideal.span {d} := by
    rw [hK, mul_comm s y]; exact Ideal.mul_mem_mul hy hsK
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨o, ho.symm⟩

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (J : Ideal (NumberField.RingOfIntegers E)), J ≠ ⊥ →
    ∃ d ∈ J, d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∃ s ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal P, ∀ y ∈ J,
        ∃ (o : NumberField.RingOfIntegers E), s * y = o * d := by
  intro E _ _ P J hJ
  exact local_gen P J hJ

end GlobalTheory.LocalGenerators
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_add_mul_notMem_of_maximal_ge {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J : Ideal R) (hJ : J ≠ 0) (n x : R)
    (h : ∀ p : Ideal R, p.IsMaximal → J ≤ p → n ∈ p → x ∉ p) :
    ∃ s : R, ∀ p : Ideal R, p.IsMaximal → J ≤ p → x + n * s ∉ p := by
  classical
  haveI : Fintype {p : Ideal R // p ∣ J} := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  let ι := {p : Ideal R // p.IsMaximal ∧ J ≤ p}
  haveI : Finite ι := Finite.of_injective
    (fun p : ι => (⟨p.1, Ideal.dvd_iff_le.2 p.2.2⟩ : {p : Ideal R // p ∣ J}))
    (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hc : Pairwise fun i j : ι => IsCoprime i.1 j.1 := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne i.2.1 j.2.1 (fun e => hij (Subtype.ext e))
  obtain ⟨s, hs⟩ := Ideal.pi_quotient_surjective (I := fun i : ι => i.1) hc
    (fun i => Ideal.Quotient.mk i.1 (if x ∈ i.1 then 1 else 0))
  refine ⟨s, fun p hp hJp hmem => ?_⟩
  have h1 := Ideal.Quotient.eq.1 (hs ⟨p, hp, hJp⟩)
  by_cases hx : x ∈ p
  · simp only [hx, if_true] at h1
    have h2 : n * s ∈ p := by simpa using p.sub_mem hmem hx
    have h3 : n ∈ p := by
      have := p.sub_mem h2 (p.mul_mem_left n h1)
      have e : n * s - n * (s - 1) = n := by ring
      rwa [e] at this
    exact h p hp hJp h3 hx
  · simp only [hx, if_false, sub_zero] at h1
    apply hx
    simpa using p.sub_mem hmem (p.mul_mem_left n h1)

theorem exists_unimodular_lift_of_unimodular_mod :
    ∀ (F : Type) [Field F] [NumberField F] (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), b ≠ 0 → ∀ (n x₀ : 𝓞 F) (y₀ : F), n ≠ 0 → y₀ ∈ b → (∀ p : Ideal (𝓞 F), p.IsMaximal → n ∈ p → ¬ (x₀ ∈ p ∧ y₀ ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b)) → ∃ (s : 𝓞 F) (t : F), t ∈ b ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → ¬ (x₀ + n * s ∈ p ∧ y₀ + (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b) := by
  intro F _ _ b hb n x₀ y₀ hn hy₀ H
  have hnF : (n : F) ≠ 0 := by
    intro e
    exact hn (RingOfIntegers.ext e)
  obtain ⟨t, ht, hy⟩ : ∃ t : F, t ∈ b ∧ y₀ + (n : F) * t ≠ 0 := by
    by_cases h0 : y₀ = 0
    · obtain ⟨t, ht, ht0⟩ : ∃ t : F, t ∈ b ∧ t ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hb (FractionalIdeal.eq_zero_iff.2 hcon)
      exact ⟨t, ht, by rw [h0, zero_add]; exact mul_ne_zero hnF ht0⟩
    · exact ⟨0, b.zero_mem, by simpa using h0⟩
  set y := y₀ + (n : F) * t with hydef
  have hyb : y ∈ b := by
    have h1 : n • t ∈ (b : Submodule (𝓞 F) F) := Submodule.smul_mem _ n ht
    exact Submodule.add_mem (b : Submodule (𝓞 F) F) hy₀ h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y * b⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hb]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hyb) _
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJb : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hy
    rw [← FractionalIdeal.spanSingleton_eq_zero_iff (S := nonZeroDivisors (𝓞 F)), ← hJb]
    simp
  have key : ∀ p : Ideal (𝓞 F),
      y ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b ↔ J ≤ p := by
    intro p
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_le_coeIdeal F]
    constructor
    · intro h
      have := mul_le_mul_left h b⁻¹
      rwa [mul_assoc, mul_inv_cancel₀ hb, mul_one, ← hJ] at this
    · intro h
      rw [← hJb]
      exact mul_le_mul_left h b
  obtain ⟨s, hs⟩ := exists_add_mul_notMem_of_maximal_ge J hJ0 n x₀ (by
    intro p hp hJp hnp hx
    refine H p hp hnp ⟨hx, ?_⟩
    have h1 := (key p).2 hJp
    have h2 : (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hnp) ht
    have h3 := Submodule.sub_mem
      (((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b : FractionalIdeal _ F) : Submodule (𝓞 F) F) h1 h2
    have e : y - (n : F) * t = y₀ := by rw [hydef]; ring
    rw [e] at h3
    exact h3)
  exact ⟨s, t, ht, fun p hp h => hs p hp ((key p).1 h.2) h.1⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_mem_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K) (hc : c ≠ 0)
    (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ b : K, b ∈ c ∧ b ∉ (P : FractionalIdeal (nonZeroDivisors R) K) * c := by
  by_contra h
  push_neg at h
  have h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c := fun b hb => h b hb
  have h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹ := by
    gcongr
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact hP (top_le_iff.mp h2)

theorem exists_mem_forall_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K)
    (hc : c ≠ 0) (S : Finset (Ideal R)) (hS : ∀ Q ∈ S, Q.IsMaximal) :
    ∃ a : K, a ∈ c ∧ ∀ Q ∈ S, a ∉ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, c.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨a, ha, haS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP : P.IsMaximal := hS P (Finset.mem_insert_self _ _)
    by_cases haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c
    swap
    · refine ⟨a, ha, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact haP
      · exact haS Q hQ
    obtain ⟨b, hb, hbP⟩ := exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top
    have hnle : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      have : Q = P := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP
      exact hPS (this ▸ hQ)
    obtain ⟨e, heS, heP⟩ := SetLike.not_le_iff_exists.mp hnle
    have key : ∀ (Q : Ideal R) (x : R), x ∈ Q →
        x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
      intro Q x hx
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb
    refine ⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb),
      fun Q hQ h => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · obtain ⟨y, p, hp, hy⟩ := hP.exists_inv heP
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      have h1 : e • b ∈ J := (J.add_mem_iff_right haP).mp h
      have h2 : y • (e • b) + p • b ∈ J := J.add_mem (J.smul_mem y h1) (key Q p hp)
      rw [smul_smul, ← add_smul, hy, one_smul] at h2
      exact hbP h2
    · have heQ : e ∈ Q := (Finset.inf_le (f := id) hQ) heS
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      exact haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)

theorem exists_mem_fractionalIdeal_generator_at_primes_over :
    ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q →
        a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro E _ _ c hc N hN
  have hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E)) := by
    simpa using hN
  have hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite := by
    refine ((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_
    rintro Q ⟨hQ, hNQ⟩
    have h0 : Q ≠ ⊥ := by
      rintro rfl
      exact hN (by simpa using hNQ)
    refine ⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩
    simpa [Ideal.dvd_iff_le] using hNQ
  obtain ⟨a, ha, h⟩ := exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset
    (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)
  exact ⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  intro E _ _ p hp h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0
  rw [← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    simp [Ideal.map_span]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hmem : (p : 𝓞 E) ∈ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem] at hle
    exact hle
  have hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  obtain ⟨hN, hsq⟩ := h P hPm hmem
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff hle).mp hne
    rw [hmap, Ideal.span_singleton_le_iff_mem] at this
    exact hsq this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
    rw [hN] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end GlobalTheory
end

section

namespace GlobalTheory.IntSubMemPow

theorem exists_int_sub_mem {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (P : Ideal R)
    (hP : P ≠ ⊤) (hc : Nat.card (R ⧸ P) = p) (a : R) : ∃ m : ℤ, a - (m : R) ∈ P := by
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  have : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)

  have hord : addOrderOf (1 : R ⧸ P) = p := by
    have hdvd : addOrderOf (1 : R ⧸ P) ∣ p := hc ▸ addOrderOf_dvd_natCard 1
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) one_ne_zero
    · exact h1

  have htop : AddSubgroup.zmultiples (1 : R ⧸ P) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hc]
  have hmem : Ideal.Quotient.mk P a ∈ AddSubgroup.zmultiples (1 : R ⧸ P) := by
    rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hm, zsmul_one, sub_self]

theorem span_sup_sq_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R)
    (hP : P.IsMaximal) (h0 : P ≠ ⊥) (x : R) (hx : x ∈ P) (hx2 : x ∉ P ^ 2) :
    Ideal.span {x} ⊔ P ^ 2 = P := by
  have hprime : Prime P := Ideal.prime_of_isPrime h0 hP.isPrime
  have hle : Ideal.span {x} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hx) (Ideal.pow_le_self two_ne_zero)

  have hdvd : Ideal.span {x} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime 2).mp hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · exfalso
    rw [pow_zero, Ideal.one_eq_top] at hassoc
    exact hP.ne_top (top_le_iff.mp (hassoc ▸ hle))
  · simpa using hassoc
  · exfalso
    exact hx2 (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))

private lemma pow_le_span_pow_sup_pow_succ {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    P ^ k ≤ Ideal.span {x ^ k} ⊔ P ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (ih hr)
    have hs' := hs
    rw [← h] at hs'
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hs'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hd
    have hsplit : (c * x ^ k + b) * (c' * x + e) =
        (c * c') * x ^ (k + 1) + (c * (x ^ k * e) + b * (c' * x + e)) := by ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) ?_
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
    · have : x ^ k * e ∈ P ^ k * P ^ 2 := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx k) he
      rwa [← pow_add] at this
    · have : b * (c' * x + e) ∈ P ^ (k + 1) * P := Ideal.mul_mem_mul hb hs
      rwa [← pow_succ] at this

theorem exists_sub_mul_pow_mem {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    ∀ y ∈ P ^ k, ∃ c : R, y - c * x ^ k ∈ P ^ (k + 1) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (pow_le_span_pow_sup_pow_succ P x hx h k hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  exact ⟨c, by simpa using hb⟩

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p)
    (P : Ideal (NumberField.RingOfIntegers E)) (hP : Ideal.IsMaximal P)
    (hpP : (p : NumberField.RingOfIntegers E) ∈ P) (hN : Ideal.absNorm P = p)
    (hp2 : (p : NumberField.RingOfIntegers E) ∉ P ^ (2 : ℕ)) (k : ℕ)
    (a : NumberField.RingOfIntegers E) :
    ∃ m : ℤ, a - (m : NumberField.RingOfIntegers E) ∈ P ^ k := by
  have h0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  have hcard : Nat.card (NumberField.RingOfIntegers E ⧸ P) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hgen : Ideal.span {(p : NumberField.RingOfIntegers E)} ⊔ P ^ 2 = P := span_sup_sq_eq P hP h0 _ hpP hp2
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih

    obtain ⟨c, hc⟩ := exists_sub_mul_pow_mem P _ hpP hgen k _ hm
    obtain ⟨n, hn⟩ := exists_int_sub_mem hp P hP.ne_top hcard c
    refine ⟨m + n * (p : ℤ) ^ k, ?_⟩
    have hrest : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P ^ (k + 1) := by
      have : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P * P ^ k :=
        Ideal.mul_mem_mul hn (Ideal.pow_mem_pow hpP k)
      rwa [← pow_succ'] at this
    have heq : a - ((m + n * (p : ℤ) ^ k : ℤ) : NumberField.RingOfIntegers E) =
        (a - (m : NumberField.RingOfIntegers E) - c * (p : NumberField.RingOfIntegers E) ^ k) + (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k := by
      push_cast; ring
    rw [heq]
    exact Ideal.add_mem _ hc hrest

end GlobalTheory.IntSubMemPow
end

section

open NumberField

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

variable {E : Type} [Field E] [NumberField E]

def reV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).re

def imV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).im

end GlobalTheory.SnMass.SkewVol
end
end
