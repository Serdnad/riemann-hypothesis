module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.Order.SuccPred.ENat
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

section

namespace GlobalTheory.SpanPowerSupremum

theorem span_sup_sq_eq {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Q.IsPrime]
    (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ 2) :
    Ideal.span {π} ⊔ Q ^ 2 = Q := by
  have hp : Prime Q := Ideal.prime_of_isPrime hQ ‹_›
  have hle : Ideal.span {π} ⊔ Q ^ 2 ≤ Q :=
    sup_le ((Ideal.span_singleton_le_iff_mem Q).mpr h1) (Ideal.pow_le_self two_ne_zero)
  have hdvd : Ideal.span {π} ⊔ Q ^ 2 ∣ Q ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hp 2).mp hdvd
  have heq : Ideal.span {π} ⊔ Q ^ 2 = Q ^ i := associated_iff_eq.mp hassoc
  interval_cases i
  ·
    rw [pow_zero, Ideal.one_eq_top] at heq
    rw [heq, top_le_iff] at hle
    exact (Ideal.IsPrime.ne_top ‹_› hle).elim
  · rw [pow_one] at heq
    exact heq
  ·
    have hmem : π ∈ Ideal.span {π} ⊔ Q ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
    rw [heq] at hmem
    exact (h2 hmem).elim

theorem pow_le_span_pow_sup {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A}
    [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ (2 : ℕ)) (m : ℕ) :
    Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + (1 : ℕ)) := by
  have hπ : Ideal.span {π} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr h1
  induction m with
  | zero => simp
  | succ m ih =>
    have hπm : Ideal.span {π ^ m} ≤ Q ^ m := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono hπ m
    calc Q ^ (m + 1) = Q ^ m * Q := pow_succ Q m
      _ ≤ (Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) * (Ideal.span {π} ⊔ Q ^ 2) :=
          Ideal.mul_mono ih (span_sup_sq_eq hQ h1 h2).ge
      _ ≤ Ideal.span {π ^ (m + 1)} ⊔ Q ^ (m + 1 + 1) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_left
          · refine le_sup_of_le_right ?_
            calc Ideal.span {π ^ m} * Q ^ 2 ≤ Q ^ m * Q ^ 2 := Ideal.mul_mono_left hπm
              _ = Q ^ (m + 1 + 1) := by rw [← pow_add]
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Ideal.span {π} ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right hπ
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Q ^ 2 ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right (Ideal.pow_le_self two_ne_zero)
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm

end GlobalTheory.SpanPowerSupremum
end

section

namespace GlobalTheory.AlgebraicIntegerNormBound

theorem main : ∀ {A : Type} [inst : CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Ideal.IsPrime Q], Q ≠ ⊥ → ∀ {π : A}, π ∈ Q → π ∉ Q ^ (2 : ℕ) → ∀ (m : ℕ), π ^ m ∉ Q ^ (m + (1 : ℕ)) := by
  intro A _ _ Q hQ hQ0 π h1 h2 m hm
  have hP : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  rw [← Ideal.dvd_span_singleton] at h1 h2 hm
  obtain ⟨J, hJ⟩ := h1
  have hJQ : ¬ Q ∣ J := by
    rintro ⟨K, hK⟩
    apply h2
    exact ⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩
  rw [← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ] at hm
  have hQm : Q ^ m ≠ 0 := pow_ne_zero _ hQ0
  rw [mul_dvd_mul_iff_left hQm] at hm
  exact hJQ (hP.dvd_of_dvd_pow hm)

end GlobalTheory.AlgebraicIntegerNormBound
end

section

open IsLocalRing

namespace GlobalTheory.PrimeElement

variable {R : Type*} [CommRing R] {π : R}

theorem isPrime_span (hπ : Prime π) : (Ideal.span {π}).IsPrime :=
  (Ideal.span_singleton_prime hπ.ne_zero).2 hπ

theorem mem_primeCompl_span [(Ideal.span {π}).IsPrime] {b : R} :
    b ∈ (Ideal.span {π}).primeCompl ↔ ¬ π ∣ b := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]

section AtPrime

variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]

theorem maximalIdeal_eq_span [IsLocalRing S] :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) S, Ideal.map_span,
    Set.image_singleton]

include π in
theorem algebraMap_atPrime_injective [IsDomain R] : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

include π in
theorem isDomain_atPrime [IsDomain R] : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

theorem isDiscreteValuationRing [IsDomain R] [IsNoetherianRing R] [IsDomain S] (hπ : π ≠ 0) :
    IsDiscreteValuationRing S := by
  have := IsLocalization.AtPrime.isLocalRing S (Ideal.span {π})
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl S inferInstance
  have hne : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_atPrime_injective (π := π) S)).2 hπ
  have hf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span (π := π) S, Ideal.span_singleton_eq_bot]
    exact hne
  refine ((IsDiscreteValuationRing.TFAE S hf).out 1 5).2 ?_
  exact ⟨⟨_, maximalIdeal_eq_span (π := π) S⟩⟩

theorem irreducible_algebraMap [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Irreducible (algebraMap R S π) := by
  have := isDomain_atPrime (π := π) S
  have := isDiscreteValuationRing (π := π) S hπ
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span S)

end AtPrime

theorem exists_eq_of_pow_mul_of_mul {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]
    [FaithfulSMul R K] (hπ : Prime π) {x : K} {n : ℕ} {a b c : R}
    (ha : algebraMap R K (π ^ n) * x = algebraMap R K a) (hb : ¬ π ∣ b)
    (hc : algebraMap R K b * x = algebraMap R K c) : ∃ r : R, algebraMap R K r = x := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have := hinj.isDomain
  have h : b * a = π ^ n * c := hinj <| by
    rw [map_mul, map_mul, ← ha, ← hc]; ring
  obtain ⟨r, rfl⟩ : π ^ n ∣ a := hπ.pow_dvd_of_dvd_mul_left n hb ⟨c, h⟩
  refine ⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hπ.ne_zero)) ?_⟩
  rw [ha, map_mul]

section Inter

variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]

theorem range_inf_range (hπ : π ≠ 0) :
    (algebraMap A K).range ⊓ (algebraMap S K).range = (algebraMap R K).range := by
  have hp : Prime π := (Ideal.span_singleton_prime hπ).1 inferInstance
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers π) y
    obtain ⟨⟨c, ⟨b, hb⟩⟩, h₂⟩ := IsLocalization.surj (Ideal.span {π}).primeCompl z
    refine exists_eq_of_pow_mul_of_mul hp (n := n) (a := a) (c := c) ?_
      (mem_primeCompl_span.1 hb) ?_
    · rw [IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R A K a, ← h₁,
        map_mul, hy, mul_comm]
    · rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K c, ← h₂,
        map_mul, hz, mul_comm]
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A K r).symm⟩,
      ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩⟩

omit [(Ideal.span {π}).IsPrime] in
theorem algebraMap_away_injective (hπ : π ≠ 0) : Function.Injective (algebraMap A K) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hinj := FaithfulSMul.algebraMap_injective R K
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers π) y
  have h := congrArg (algebraMap A K) (IsLocalization.mk'_spec A a s)
  rw [map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply, eq_comm,
    map_eq_zero_iff _ hinj] at h
  simp [h]


variable {A S} in
theorem exists_algebraMap_eq (hπ : π ≠ 0) {y : A} {z : S}
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, algebraMap R A r = y := by
  obtain ⟨r, hr⟩ : algebraMap A K y ∈ (algebraMap R K).range := by
    rw [← range_inf_range A S K hπ]
    exact ⟨⟨y, rfl⟩, ⟨z, h.symm⟩⟩
  exact ⟨r, algebraMap_away_injective A K hπ (by rw [← IsScalarTower.algebraMap_apply, hr])⟩


variable {A S} in
theorem exists_unit_algebraMap_eq (hπ : π ≠ 0) {y : A} (hy : IsUnit y) {z : S} (hz : IsUnit z)
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  have h' : algebraMap A K (y⁻¹ : Aˣ) = algebraMap S K (z⁻¹ : Sˣ) := by
    refine mul_left_cancel₀ (y.isUnit.map (algebraMap A K)).ne_zero ?_
    rw [← map_mul, Units.mul_inv, map_one, h, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨r, hr⟩ := exists_algebraMap_eq (A := A) (S := S) (K := K) hπ h
  obtain ⟨r', hr'⟩ := exists_algebraMap_eq (A := A) (S := S) (K := K) hπ h'
  refine ⟨r, IsUnit.of_mul_eq_one r' (FaithfulSMul.algebraMap_injective R K ?_), hr⟩
  rw [IsScalarTower.algebraMap_apply R A K, map_mul, hr, hr', Units.mul_inv, map_one, map_one]

end Inter

section Valuation

variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]

end Valuation

theorem existsUnique_zpow_mul_eq_unit {S K : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] {ϖ : S}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃! a : ℤ, ∃ u : S, IsUnit u ∧ algebraMap S K u = algebraMap S K ϖ ^ a * x := by
  have hinj := IsFractionRing.injective S K
  have h0 : algebraMap S K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ (a b : ℤ) (u v : S), IsUnit v → algebraMap S K u = algebraMap S K ϖ ^ a * x →
      algebraMap S K v = algebraMap S K ϖ ^ b * x → b ≤ a := by
    intro a b u v hv h₁ h₂
    by_contra! hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + (n + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
    have : v = ϖ * (ϖ ^ n * u) := hinj <| by
      rw [h₂, hn, zpow_add₀ h0, zpow_natCast, map_mul, map_mul, map_pow, h₁]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hv))
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine existsUnique_of_exists_of_unique ⟨(n : ℤ) - m, (u * v⁻¹ : Sˣ), Units.isUnit _, ?_⟩ ?_
  · have hv : algebraMap S K v ≠ 0 := (v.isUnit.map _).ne_zero
    rw [zpow_sub₀ h0]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_natCast]
    field_simp
  · rintro a b ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩
    exact le_antisymm (key b a v u hu h₂ h₁) (key a b u v hv h₁ h₂)

end GlobalTheory.PrimeElement
end

section

open Real NumberField
namespace GlobalTheory

theorem absNorm_map_ringEquiv_self {R : Type} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] (e : R ≃+* R) (J : Ideal R) :
    Ideal.absNorm (J.map e.toRingHom) = Ideal.absNorm J := by
  letI : Infinite R := Module.Free.infinite ℤ R
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv J (J.map e.toRingHom) e rfl).toEquiv).symm

end GlobalTheory
end

section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem powerSeries_pow_eq_expand_zmod (p : ℕ) [hp : Fact p.Prime] (g : PowerSeries (ZMod p)) :
    g ^ p = PowerSeries.expand p hp.out.ne_zero g := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) (f := g) p hp.out.ne_zero
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

theorem powerSeries_eq_sum_X_pow_mul_pow (p : ℕ) [hp : Fact p.Prime] (F : PowerSeries (ZMod p)) :
    ∃ G : Fin p → PowerSeries (ZMod p),
      F = ∑ j : Fin p, PowerSeries.X ^ (j : ℕ) * G j ^ p := by
  have hp0 : 0 < p := hp.out.pos
  refine ⟨fun j => PowerSeries.mk fun i => PowerSeries.coeff (p * i + j) F, ?_⟩
  ext n

  rw [map_sum]
  simp_rw [powerSeries_pow_eq_expand_zmod, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_expand]
  rw [Finset.sum_eq_single (⟨n % p, Nat.mod_lt n hp0⟩ : Fin p)]
  · have h1 : n % p ≤ n := Nat.mod_le n p
    have h2 : p ∣ n - n % p := Nat.dvd_sub_mod n
    simp only [h1, h2, if_true, PowerSeries.coeff_mk]
    congr 1
    rw [Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro j _ hj
    split_ifs with h1 h2
    · exfalso
      apply hj
      ext
      simp only
      have hj' : (j : ℕ) < p := j.2
      obtain ⟨c, hc⟩ := h2
      have : n = p * c + j := by omega
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj']
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem laurentSeries_eq_sum_single_mul_pow :
    ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p),
      f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  intro p hp f
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set N : ℕ := f.order.natAbs with hN
  set m : ℕ := (f.order + p * N).toNat with hm
  have hm' : ((m : ℕ) : ℤ) = f.order + p * N := by
    rw [hm, Int.toNat_of_nonneg]
    have : (f.order.natAbs : ℤ) = |f.order| := Int.natCast_natAbs _
    rw [hN, this]
    have h2 : -f.order ≤ |f.order| := neg_le_abs _
    have h3 : 0 ≤ |f.order| := abs_nonneg _
    nlinarith
  obtain ⟨G, hG⟩ := powerSeries_eq_sum_X_pow_mul_pow p (PowerSeries.X ^ m * f.powerSeriesPart)
  refine ⟨fun j => HahnSeries.single (-(N : ℤ)) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ _ (G j), ?_⟩
  have key : f = HahnSeries.single (-(p * N : ℤ)) (1 : ZMod p) *
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.X ^ m * f.powerSeriesPart) := by
    conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart f]
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, hm',
      mul_one]
    congr 2
    ring

  rw [key, hG, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, map_pow, mul_pow, HahnSeries.single_pow, one_pow]
  have : (p • (-(N : ℤ))) = -(p * N : ℤ) := by rw [nsmul_eq_mul]; ring
  rw [this]
  ring

end GlobalTheory
end

section

namespace GlobalTheory

open IsLocalRing

section

variable {B : Type*} [CommRing B] [IsDomain B]

variable [IsNoetherianRing B] [IsLocalRing B]

theorem prime_eq_bot_or_maximalIdeal_of_forall_mem {f : B} (hf : f ≠ 0)
    (H : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → f ∈ p) {p : Ideal B} (hp : p.IsPrime) :
    p = ⊥ ∨ p = maximalIdeal B := by
  classical
  refine or_iff_not_imp_left.mpr fun hp0 => ?_
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hmin : ∀ q : Ideal B, q.IsPrime → q ≠ ⊥ →
      ∃ P ∈ (Ideal.span {f}).minimalPrimes, P ≤ q := fun q hq hq0 =>
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem q).mpr (H q hq hq0))

  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (hfin.toFinset : Set (Ideal B)), ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.Finite.coe_toFinset, id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := hmin p hp hp0
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem (maximalIdeal B)).mpr hx)
    haveI hQp : Q.IsPrime := hQ.1.1
    have hxQ : x ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mp hQ.1.2
    have hQ0 : Q ≠ ⊥ := fun h => hx0 (by simpa [h] using hxQ)
    have hQ1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
    obtain ⟨P, hP, hPQ⟩ := hmin Q hQp hQ0
    haveI hPp : P.IsPrime := hP.1.1
    have hfP : f ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
    refine ⟨P, hP, ?_⟩
    rcases hPQ.eq_or_lt with h | h
    · exact h ▸ hxQ
    · have h1 : P.height < 1 := (Ideal.height_strict_mono_of_isPrime h).trans_le hQ1
      rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      exact absurd (by simpa [h1] using hfP) hf
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime (⊥ : Ideal B) ⊥ fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).mp hP).1.1).mp hcover
  have hP' := (Set.Finite.mem_toFinset hfin).mp hP
  have hpm : p ≤ maximalIdeal B := le_maximalIdeal hp.ne_top
  exact le_antisymm hpm (hmP.trans (hP'.2
    ⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr (H p hp hp0)⟩ (hpm.trans hmP)))

end

end GlobalTheory
end

section

namespace GlobalTheory

open Finset


open Finset in
theorem _root_.GlobalTheory.splitHeight_summable_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} {f : ∀ i, α i → ℝ}
    (h0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) :
    Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i (n i)) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image fun n : (∀ i, α i) => n i, ∏ i, f i (n i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
          Finset.prod_nonneg fun i _ => h0 i (n i)
        intro n hn
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i, ∑ x ∈ s.image fun n : (∀ i, α i) => n i, f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' x, f i x := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

end GlobalTheory
end
