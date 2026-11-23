module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [valuation_of_mk'] at ht
  set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn
  have hvb : v.intValuation b = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hb0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b := by
    rw [hvb]; exact WithZero.exp_pos
  have hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hvb]; exact (div_le_one₀ hpos).1 ht
  have haI : a ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem a n).1 hva
  have hbI : b ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem b n).1 hvb.le
  have hbI' : b ∉ v.asIdeal ^ (n + 1) := by
    intro h
    have := (v.intValuation_le_pow_iff_mem b (n + 1)).2 h
    rw [hvb] at this
    have h2 := WithZero.exp_le_exp.1 this
    push_cast at h2
    omega
  have hdvd : v.asIdeal ^ n ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)
  obtain ⟨B', hB'⟩ := hdvd
  have hB'p : ¬ B' ≤ v.asIdeal := by
    intro hle
    apply hbI'
    have : Ideal.span {b} ≤ v.asIdeal ^ (n + 1) := by
      rw [hB', pow_succ]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self b)
  obtain ⟨s, hsB, hsp⟩ := Set.not_subset.1 hB'p
  refine ⟨s, hsp, ?_⟩
  have hmem : a * s ∈ Ideal.span {b} := by
    rw [hB']; exact Ideal.mul_mem_mul haI hsB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨r, ?_⟩
  show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r
  rw [IsFractionRing.mk'_eq_div]
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]; exact hb0
  rw [mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

theorem mul_mem_of_trace_mem {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by
  intro d hd
  have hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx b
  have hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal (𝓞 K) K] at hdd
  have hm := FractionalIdeal.mul_mem_mul hxd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_approx_idempotent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    ∃ z : 𝓞 L, z ∉ la.asIdeal ∧ ∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la →
      la'.asIdeal.under (𝓞 K) = p.asIdeal → z ∈ la'.asIdeal ^ N := by
  set S : Set (HeightOneSpectrum (𝓞 L)) := {la' | la' ≠ la ∧ la'.asIdeal.under (𝓞 K) = p.asIdeal}
  haveI := p.isMaximal
  have hfin : S.Finite := by
    refine ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L)).preimage
      (f := HeightOneSpectrum.asIdeal) ?_).subset ?_
    · intro a _ b _ h; exact HeightOneSpectrum.ext h
    · intro la' h
      exact ⟨la'.isPrime, ⟨h.2.symm⟩⟩
  haveI := la.isPrime
  have hw : ∀ la' ∈ S, ∃ w : 𝓞 L, w ∈ la'.asIdeal ^ N ∧ w ∉ la.asIdeal := by
    intro la' h
    by_contra hc
    push_neg at hc
    have h1 : la'.asIdeal ^ N ≤ la.asIdeal := fun w hw => hc w hw
    have h2 := Ideal.IsPrime.le_of_pow_le h1
    exact h.1 (HeightOneSpectrum.ext (la'.isMaximal.eq_of_le la.isPrime.ne_top h2))
  choose! w hwN hwla using hw
  refine ⟨∏ la' ∈ hfin.toFinset, w la', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, hi, hmem⟩
    exact hwla i (hfin.mem_toFinset.1 hi) hmem
  · intro la' h1 h2
    have hS : la' ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨h1, h2⟩
    rw [← Finset.mul_prod_erase _ _ hS]
    exact Ideal.mul_mem_right _ _ (hwN la' ⟨h1, h2⟩)

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem valuation_mul_different_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)),
    la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L,
      (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal →
        b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) →
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  intro K L _ _ _ _ _ la p hp y ⟨N, hN⟩ d hd
  obtain ⟨z, hzla, hzN⟩ := exists_approx_idempotent (K := K) la p N
  set x : L := (z : L) * y with hxdef
  have hx : ∀ b : 𝓞 L, p.valuation K (Algebra.trace K L ((b : L) * x)) ≤ 1 := by
    intro b
    have h := hN (b * z) (fun la' h1 h2 => Ideal.mul_mem_left _ _ (hzN la' h1 h2))
    rw [hxdef, ← mul_assoc]
    simpa using h
  set bs := RingOfIntegers.basis L
  have hloc : ∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K s * Algebra.trace K L ((bs i : L) * x) = algebraMap (𝓞 K) K r :=
    fun i => exists_not_mem_mul_mem p _ (hx (bs i))
  choose s hsp r hr using hloc
  set s0 : 𝓞 K := ∏ i, s i with hs0
  haveI := p.isPrime
  have hs0p : s0 ∉ p.asIdeal := by
    rw [hs0, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, _, hi⟩
    exact hsp i hi
  have hgen : ∀ b : 𝓞 L,
      algebraMap (𝓞 K) K s0 * Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have hb : b ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      rw [hs0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap _ _ (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      have : ((b + c : 𝓞 L) : L) * x = (b : L) * x + (c : L) * x := by push_cast; ring
      rw [this, map_add (f := _), mul_add]
      exact add_mem hb hc
    | smul n b _ hb =>
      have : ((n • b : 𝓞 L) : L) * x = n • ((b : L) * x) := by
        rw [← smul_mul_assoc]; congr 1
      rw [this, map_zsmul, mul_smul_comm]
      exact zsmul_mem hb n
  set x' : L := algebraMap (𝓞 K) L s0 * x with hx'def
  have htr : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x') ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have : (b : L) * x' = (algebraMap (𝓞 K) K s0) • ((b : L) * x) := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hx'def]; ring
    rw [this, map_smul, smul_eq_mul]
    exact hgen b
  obtain ⟨c, hc⟩ := mul_mem_of_trace_mem x' htr d hd
  have hcle : la.valuation L (c : L) ≤ 1 := la.valuation_le_one c
  have hs0la : la.valuation L (algebraMap (𝓞 K) L s0) = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hs0p ?_)
    rw [la.valuation_lt_one_iff_mem] at h
    rw [← hp]
    exact h
  have hzla' : la.valuation L (z : L) = 1 := by
    refine le_antisymm (la.valuation_le_one z) (not_lt.1 fun h => hzla ?_)
    exact (la.valuation_lt_one_iff_mem z).1 h
  have : (c : L) = (algebraMap (𝓞 K) L s0 * (z : L)) * (y * (d : L)) := by
    rw [hc, hx'def, hxdef]; ring
  rw [this, map_mul, map_mul, hs0la, hzla', one_mul, one_mul] at hcle
  exact hcle

end GlobalTheory.InvDiffLocal
end

section

namespace GlobalTheory.NatCastNotMemPrimeIdeal

theorem natCast_notMem_of_prime_ne {L : Type} [Field L] [NumberField L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p)
    (hqw : (q : NumberField.RingOfIntegers L) ∈ w.asIdeal) :
    (p : NumberField.RingOfIntegers L) ∉ w.asIdeal := by
  intro hpw
  have hc : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : NumberField.RingOfIntegers L) * (q : NumberField.RingOfIntegers L)
      + (b : NumberField.RingOfIntegers L) * (p : NumberField.RingOfIntegers L) = 1 := by
    have := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers L) hab
    push_cast at this
    exact this
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hqw) (w.asIdeal.mul_mem_left _ hpw)

end GlobalTheory.NatCastNotMemPrimeIdeal
end

section

namespace GlobalTheory.CoprimeAbsNorm

open NumberField IsDedekindDomain

theorem coprime_absNorm_of_natCast_notMem {E : Type} [Field E] [NumberField E]
    {P : HeightOneSpectrum (RingOfIntegers E)} {m : ℕ}
    (hm : (m : RingOfIntegers E) ∉ P.asIdeal) :
    Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpN
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0 :=
    (mul_eq_zero.mp hpx).resolve_right hx0
  have hpP : (p : RingOfIntegers E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  obtain ⟨k, rfl⟩ := hpm
  apply hm
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.CoprimeAbsNorm
end

section

open NumberField Polynomial

namespace GlobalTheory.KummerUnits

theorem exists_finite_galois_mem_of_pow_eq_unit : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  intro E F Ω _ _ _ _ _ _ _ _ _ M hM ⟨ζ, hζ⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  obtain ⟨S, hS⟩ := Monoid.exists_of_isMulFG (𝓞 E)ˣ
  let c : (𝓞 E)ˣ → F := fun u => algebraMap E F ((u : 𝓞 E) : E)
  let p : F[X] := ∏ s ∈ S, (X ^ M - C (c s))
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => X_pow_sub_C_ne_zero hM _
  let L := IntermediateField.adjoin F (p.rootSet Ω)
  have hsp : p.IsSplittingField F L :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI := Polynomial.IsSplittingField.finiteDimensional L p
  haveI := Normal.of_isSplittingField (F := F) (E := L) p
  refine ⟨L, inferInstance, ⟨⟩, ?_⟩
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M := hζ.map_of_injective (algebraMap F Ω).injective
  have hroot : ∀ ξ : Ω, ξ ^ M = 1 → ξ ∈ L := by
    intro ξ hξ
    obtain ⟨i, -, rfl⟩ := hζΩ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (L.algebraMap_mem ζ) i
  let φ : (𝓞 E)ˣ →* Ω :=
    ((algebraMap E Ω).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom).comp (Units.coeHom _)
  have hφ : ∀ u, φ u = algebraMap E Ω ((u : 𝓞 E) : E) := fun u => rfl
  have hφc : ∀ u, φ u = algebraMap F Ω (c u) := fun u => IsScalarTower.algebraMap_apply E F Ω _
  have hφ0 : ∀ u, φ u ≠ 0 := fun u => ((Group.isUnit u).map φ).ne_zero
  intro u
  simp only [← hφ]
  have hall : u ∈ Submonoid.closure (S : Set (𝓞 E)ˣ) := by rw [hS]; trivial
  induction hall using Submonoid.closure_induction with
  | mem s hs =>
    intro w hw
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    simp only [p, map_prod]
    refine Finset.prod_eq_zero hs ?_
    simp [hw, hφc]
  | one =>
    intro w hw
    exact hroot w (by rw [hw, map_one])
  | mul a b _ _ ha hb =>
    intro w hw
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (φ a) hM
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (φ b) hM
    have hxy : x * y ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rintro rfl; exact hφ0 a (by rw [← hx, zero_pow hM.ne'])
      · rintro rfl; exact hφ0 b (by rw [← hy, zero_pow hM.ne'])
    rw [← div_mul_cancel₀ w hxy]
    refine mul_mem (hroot _ ?_) (mul_mem (ha x hx) (hb y hy))
    rw [div_pow, mul_pow, hx, hy, hw, map_mul, div_self (mul_ne_zero (hφ0 a) (hφ0 b))]

end GlobalTheory.KummerUnits
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

namespace GlobalTheory.UnramSquare

theorem not_sq_mul_unit (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsMaximal] :
    Algebra.IsUnramifiedAt ℤ Q → ∀ p : ℕ, p.Prime → (p : 𝓞 K) ∈ Q → ∀ y u : 𝓞 K, u ∉ Q →
      y ^ 2 = (p : 𝓞 K) * u → False := by
  intro h p hp hpQ y u hu hyu
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hPr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hPr.isMaximal (by simpa using hpZ.ne_zero)
  haveI hQp : Q.IsPrime := inferInstance
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpQ
  letI := Localization.AtPrime.algebraOfLiesOver (Ideal.span {(p : ℤ)}) Q
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {(p : ℤ)}) Q).1 h).2
  have hyQ : y ∈ Q := hQp.mem_of_pow_mem 2 (by rw [hyu]; exact Q.mul_mem_right _ hpQ)
  have h3 : algebraMap (𝓞 K) (Localization.AtPrime Q) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q y).2 hyQ
  rw [← h2, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h3
  obtain ⟨w, hw⟩ := h3
  obtain ⟨⟨z, t⟩, hzt⟩ := IsLocalization.surj Q.primeCompl w
  have htz : (t : 𝓞 K) * y = p * z := by
    apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
    simp only at hzt
    rw [map_mul, map_mul, ← hw, ← hzt]
    simp only [map_natCast, eq_intCast, Int.cast_natCast]
    ring
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4 : (t : 𝓞 K) ^ 2 * u = p * z ^ 2 := by
    apply mul_left_cancel₀ hp0
    calc (p : 𝓞 K) * ((t : 𝓞 K) ^ 2 * u) = (t : 𝓞 K) ^ 2 * y ^ 2 := by rw [hyu]; ring
      _ = ((t : 𝓞 K) * y) ^ 2 := by ring
      _ = p * (p * z ^ 2) := by rw [htz]; ring
  have h5 : (t : 𝓞 K) ^ 2 * u ∈ Q := by rw [h4]; exact Q.mul_mem_right _ hpQ
  rcases hQp.mem_or_mem h5 with h6 | h6
  · exact t.2 (hQp.mem_of_pow_mem 2 h6)
  · exact hu h6

end GlobalTheory.UnramSquare
end

section

open NumberField

namespace GlobalTheory

theorem addValuation_nonneg_of_ringOfIntegers :
    ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L),
      0 ≤ v (a : L) := by
  intro L _ _ v a
  have hZ : ∀ m : ℤ, 0 ≤ v (m : L) := by
    intro m
    induction m using Int.induction_on with
    | zero => simp [AddValuation.map_zero]
    | succ k ih =>
      rw [Int.cast_add, Int.cast_one]
      exact AddValuation.map_le_add v ih (by rw [AddValuation.map_one])
    | pred k ih =>
      rw [Int.cast_sub, Int.cast_one]
      exact AddValuation.map_le_sub v ih (by rw [AddValuation.map_one])
  by_contra hneg
  push_neg at hneg
  obtain ⟨f, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  set x : L := (a : L) with hx
  have hxtop : v x ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hxtop
  have hk0 : k < 0 := by
    rw [← hk] at hneg
    exact_mod_cast hneg
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c = 1 := by
      have h1 := hm.leadingCoeff
      rwa [Polynomial.leadingCoeff_C] at h1
    subst hc
    simp at hf
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun v at hf
  rw [AddValuation.map_neg, AddValuation.map_pow, ← hk] at hf
  have hlt : ((f.natDegree • k : ℤ) : WithTop ℤ) <
      v (∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ L) (f.coeff i) * x ^ i) := by
    apply AddValuation.map_lt_sum v (WithTop.coe_ne_top)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hk, eq_intCast]
    calc ((f.natDegree • k : ℤ) : WithTop ℤ) < ((i • k : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_lt_coe, nsmul_eq_mul, nsmul_eq_mul]
          have : (i : ℤ) < f.natDegree := by exact_mod_cast hi
          nlinarith
      _ = i • (k : WithTop ℤ) := by rw [WithTop.coe_nsmul]
      _ ≤ v ((f.coeff i : ℤ) : L) + i • (k : WithTop ℤ) := le_add_of_nonneg_left (hZ _)
  rw [WithTop.coe_nsmul, hf] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory
end
