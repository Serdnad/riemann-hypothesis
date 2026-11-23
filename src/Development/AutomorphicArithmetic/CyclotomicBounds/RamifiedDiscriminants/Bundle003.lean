module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle008
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle009
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle002
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open UpperTheory.HF

open NumberField Ideal
open scoped Pointwise

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem mem_ramI_iff {p : ℕ} (hp : p.Prime) : p ∈ H.toHostRaw.ramI ↔ p ∣ H.QS * H.q := by
  have h0 : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  rw [Formalism.HC.HostRaw.ramI, Finset.mem_erase, Formalism.HC.HostRaw.ram, Nat.mem_primeFactors, H.dvd_natAbs_discr_iff hp]
  constructor
  · rintro ⟨hd, -, h, -⟩
    exact ((Nat.Prime.dvd_mul hp).1 h).resolve_right fun h' =>
      hd ((Nat.prime_dvd_prime_iff_eq hp H.toHostRaw.d_prime).1 h')
  · intro h
    refine ⟨?_, hp, h.mul_right _, h0⟩
    rintro rfl
    exact H.toHostRaw.d_not_dvd_QSq h

private theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) : P.LiesOver (span {(p : ℤ)}) :=
  ⟨Ideal.IsMaximal.eq_of_le
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible)
    (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]; exact h)⟩

private theorem dvd_absNorm_of {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P J : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) (hJ : P ∣ J) : p ∣ absNorm J := by
  by_contra hn
  obtain ⟨u, v, huv⟩ : IsCoprime (p : 𝓞 E) ((absNorm J : ℕ) : 𝓞 E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).cast
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2
    (huv ▸ P.add_mem (P.mul_mem_left u h) (P.mul_mem_left v (Ideal.le_of_dvd hJ (Ideal.absNorm_mem J)))))

theorem half_ne_bot : H.𝔟 ≠ ⊥ := fun h => by
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem prime_dvd_absNorm_half_iff {p : ℕ} (hp : p.Prime) : p ∣ absNorm H.𝔟 ↔ p ∣ H.QS * H.q := by
  have hs := (UpperTheory.HF.half_supp H.toHostAx H.𝔟 H.𝔟_spec.1 H.𝔟_spec.2).1
  constructor
  · intro h
    obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h
    haveI := hP.isPrime
    obtain ⟨l, hl, ho⟩ := (hs P).1.1 (Or.inl hd)
    have hlp : l.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
    have e : span {(l : ℤ)} = span {(p : ℤ)} := ho.over.trans hu
    have : p ∣ l := by
      have := Ideal.mem_span_singleton.1 (e ▸ Ideal.mem_span_singleton_self (l : ℤ))
      exact_mod_cast this
    rw [(Nat.prime_dvd_prime_iff_eq hp hlp).1 this]
    exact (H.mem_ramI_iff hlp).1 hl
  · intro h
    have h1 : p ∣ absNorm (span {(p : 𝓞 H.E)}) := by
      rw [Ideal.absNorm_span_natCast]
      exact dvd_pow_self _ Module.finrank_pos.ne'
    obtain ⟨P, hP, -, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1
    haveI := hP.isPrime
    have hm : (p : 𝓞 H.E) ∈ P := Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
    rcases (hs P).1.2 ⟨p, (H.mem_ramI_iff hp).2 h, liesOver_of_mem hp P hm⟩ with h2 | h2
    · exact dvd_absNorm_of hp P _ hm h2
    · have hm' : (p : 𝓞 H.E) ∈ H.toHostRaw.conj • P := by
        have := Ideal.smul_mem_pointwise_smul H.toHostRaw.conj _ _ hm
        rwa [show H.toHostRaw.conj • (p : 𝓞 H.E) = p from map_natCast (MulSemiringAction.toRingHom _ (𝓞 H.E) H.toHostRaw.conj) p] at this
      exact dvd_absNorm_of hp _ _ hm' h2

theorem four_ord_le_condN : 4 * R.toFrame.ord ≤ H.QS * H.q * H.d := by
  have h := UpperTheory.HF.cond_rd H.toHostAx
  have h2 := UpperTheory.HF.ram_eq H.toHostAx
  refine h.2.2.2.2.2.2.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero) ?_)
  rw [h2.2.2.2.1]
  refine Nat.mul_dvd_mul_right (Nat.mul_dvd_mul h2.2.2.2.2.1 ?_) _
  split_ifs
  exacts [dvd_rfl, one_dvd _]

end Formalism.BasicNotions.Host
end

section

open Formalism.BasicNotions

theorem UpperTheory.Ram.two_fm_le_rdE :
    ∀ (R : Ranks) (H : Host R), 2 * (R.f : ℝ) * R.m ≤ H.rdE ∧ 4 * (R.t : ℝ) * R.r + 1 ≤ H.rdE := by
  intro R H
  obtain ⟨hq, hd⟩ := H.qd_big
  obtain ⟨-, -, hsq, -⟩ := UpperTheory.KR.log_qd_le_rd H.toHostAx H.flPS
  have hrd : H.toHostAx.rd = H.rdE := rfl
  have hq' : H.toHostAx.q = H.q := rfl
  have hd' : H.toHostAx.d = H.d := rfl
  rw [hrd, hq', hd'] at hsq
  set X : ℝ := 4 * (R.t : ℝ) * R.r + 1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hqX : X < (H.q : ℝ) := by
    have : ((4 * R.t * R.r + 1 : ℕ) : ℝ) < (H.q : ℝ) := by exact_mod_cast hq
    simpa [hX] using this
  have hdX : X < (H.d : ℝ) := by
    have : ((4 * R.t * R.r + 1 : ℕ) : ℝ) < (H.d : ℝ) := by exact_mod_cast hd
    simpa [hX] using this
  have hprod : X * X < (H.q : ℝ) * H.d := mul_lt_mul'' hqX hdX hX0 hX0
  have hsqrt : X < √((H.q : ℝ) * H.d) := by
    rw [show X = √(X * X) from (Real.sqrt_mul_self hX0).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hprod
  have hmain : X ≤ H.rdE := le_trans hsqrt.le hsq
  refine ⟨?_, hmain⟩
  have hf : R.f ≤ R.k := by
    have := R.f_le_k
    simp only [Ranks.f, Ranks.n]
    omega
  have hm := R.two_le_m
  have hr : R.k + 1 ≤ R.r := by
    simp only [Ranks.r]
    omega
  have hmt : R.m ≤ R.t := by
    have := R.three_m_lt_t
    omega
  have hnat : 2 * R.f * R.m ≤ 4 * R.t * R.r + 1 := by
    have h1 : R.f ≤ R.r := by omega
    calc 2 * R.f * R.m ≤ 2 * R.r * R.t := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) hmt
      _ ≤ 4 * R.t * R.r + 1 := by nlinarith
  have : (2 * (R.f : ℝ) * R.m) ≤ X := by
    rw [hX]
    exact_mod_cast hnat
  linarith
end

section

open Formalism.BasicNotions

theorem UpperTheory.Ram.cond_le_four_n_sq :
    ∀ (R : Ranks) (H : Host R), (H.QS : ℝ) * H.q * H.d ≤ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ∧ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ≤ ((H.QS : ℝ) * H.q * H.d) ^ 2 ∧ (R.f : ℝ) ≤ H.QS := by
  intro R H
  have hQS : H.QS ≤ R.n ^ 2 := H.QS_le
  have h2 : 2 * R.ord ≤ H.QS := (UpperTheory.Ram.ord_le_totient_QS H.toHostAx).2
  have hf : (R.f : ℝ) = 2 * (R.n : ℝ) := by
    simp only [Ranks.f]
    push_cast
    ring
  have hn : (R.n : ℝ) = (R.ord : ℝ) := by simp [Ranks.n]
  have hq1 : (1 : ℝ) ≤ H.q := by
    have := H.qd_big.1
    exact_mod_cast (by omega : 1 ≤ H.q)
  have hd1 : (1 : ℝ) ≤ H.d := by
    have := H.qd_big.2
    exact_mod_cast (by omega : 1 ≤ H.d)
  have hQSr : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast hQS
  have h2r : 2 * (R.n : ℝ) ≤ H.QS := by
    rw [hn]; exact_mod_cast h2
  have hn0 : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
  have hqd : (0 : ℝ) ≤ (H.q : ℝ) * H.d := by positivity
  have hqd1 : (1 : ℝ) ≤ (H.q : ℝ) * H.d := by nlinarith
  rw [hf]
  refine ⟨?_, ?_, h2r⟩
  · have : (H.QS : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hqd
    nlinarith
  · have hsq : 4 * (2 * (R.n : ℝ) / 2) ^ 2 ≤ (H.QS : ℝ) ^ 2 := by nlinarith
    have hqq : (H.q : ℝ) * H.d ≤ ((H.q : ℝ) * H.d) ^ 2 := by nlinarith
    have hA : (0 : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by positivity
    calc 4 * (2 * (R.n : ℝ) / 2) ^ 2 * H.q * H.d = 4 * (2 * (R.n : ℝ) / 2) ^ 2 * ((H.q : ℝ) * H.d) := by ring
      _ ≤ (H.QS : ℝ) ^ 2 * ((H.q : ℝ) * H.d) ^ 2 := mul_le_mul hsq hqq hqd (by positivity)
      _ = ((H.QS : ℝ) * H.q * H.d) ^ 2 := by ring
end
