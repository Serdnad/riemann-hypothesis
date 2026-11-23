module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem chi_of_pow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (k : ℕ) (h : g ζ = ζ ^ k) :
    ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 := IsPrimitiveRoot.autToPow_spec F hζ g
  have h2 : ζ ^ (k % p) = ζ ^ k := by
    conv_lhs => rw [hζ.eq_orderOf]
    exact pow_mod_orderOf ζ k
  rw [h, ← h2] at h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ hp) h1
  rw [← ZMod.natCast_mod k p, ← h3, ZMod.natCast_val, ZMod.cast_id', id]

private theorem chi_one {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (h : g ζ = ζ) : hζ.autToPow F g = 1 := by
  apply Units.ext
  rw [chi_of_pow hζ g 1 (by rw [pow_one, h]), Nat.cast_one, Units.val_one]

private theorem exists_prim {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

private theorem chi_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (j : Ω →+* ℂ) (c : G F Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    hζ.autToPow F c = -1 := by
  have hp : p.Prime := Fact.out
  have hjζ : IsPrimitiveRoot (j ζ) p := hζ.map_of_injective j.injective
  have hn : ‖j ζ‖ = 1 := hjζ.norm'_eq_one hp.ne_zero
  have hne : j ζ ≠ 0 := hjζ.ne_zero hp.ne_zero
  have h1 : c ζ = ζ ^ (p - 1) := by
    apply j.injective
    rw [hc, ← Complex.inv_eq_conj hn, map_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hjζ.pow_eq_one]
  apply Units.ext
  rw [chi_of_pow hζ c _ h1, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, Units.val_neg, Units.val_one]

private theorem good_ker {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ}
    [Fact p.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (lam : (ZMod p)ˣ →* ℂˣ) (h1 : lam (-1) = 1) :
    Good (lam.comp (hζ.autToPow F)).ker := by
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  refine ⟨?_, Abelianization.commutator_subset_ker _, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (G F Ω) ζ) ?_
      (stabilizer_isOpen_of_isIntegral (K := F) ζ)
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_one hζ g hg, map_one]
  · intro j c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_conj hζ j c hc, h1]

private theorem normV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    1 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hc : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hc]; exact Ideal.absNorm_mem _
  refine ⟨?_, hmem⟩
  have hne : normV v ≠ 0 := by
    rw [hc]; exact Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : normV v ≠ 1 := by
    rw [hc]
    intro h
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ}
    (hq : (q : 𝓞 F) ∈ v.asIdeal) (h : Nat.Coprime q p) : (p : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have hb := Nat.gcd_eq_gcd_ab q p
  rw [h] at hb
  have : ((1 : ℤ) : 𝓞 F) = (q : 𝓞 F) * ((q.gcdA p : ℤ) : 𝓞 F) + (p : 𝓞 F) * ((q.gcdB p : ℤ) : 𝓞 F) := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hb
    push_cast at this ⊢
    exact this
  rw [Int.cast_one] at this
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hq) (Ideal.mul_mem_right _ _ hp)

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrCharPP :
    OrdPrime → CharOrd → DecPow → UnrCharPP := by
  intro hOrd hChar hDec ℓ k hℓ E Ω _ _ _ _ _ _ v
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨hq1, hqv⟩ := normV_mem v
  obtain ⟨p, hp, hBp, hdvd, hsplit⟩ := hOrd E Ω ℓ (k + 1) (normV v) (max (normV v) 2) hℓ hq1
  haveI : Fact p.Prime := ⟨hp⟩
  have hqp : normV v < p := lt_of_le_of_lt (le_max_left _ _) hBp
  have hcop : Nat.Coprime (normV v) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) hqp)).symm
  have hpv : ((p : ℕ) : 𝓞 (maximalRealSubfield E)) ∉ v.asIdeal := not_mem_of_coprime v hqv hcop
  set a : (ZMod p)ˣ := ZMod.unitOfCoprime (normV v) hcop with ha
  have hao : ℓ ^ (k + 1) ∣ orderOf a := by
    rw [← orderOf_units]
    simpa [ha] using hdvd
  obtain ⟨lam, hlam1, hlamo⟩ := hChar p ℓ k a hℓ hao
  obtain ⟨ζ, hζ⟩ := exists_prim (F := maximalRealSubfield E) (Ω := Ω) p
  refine ⟨lam.comp (hζ.autToPow _), good_ker hζ lam hlam1, ?_, fun A hA => ⟨?_, fun φ hφ => ?_⟩⟩
  · intro t A hA
    by_cases hpt : ((p : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ t.asIdeal
    · right
      intro g hg x
      have hval : A.valuation (p : Ω) < 1 := by
        have := (hA (p : 𝓞 (maximalRealSubfield E))).2 hpt
        simpa using this
      exact hsplit A hval g.toRingEquiv (fun z => apply_mem_iff_of_mem_Dec hg z) x
    · left
      intro τ hτ
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        chi_one hζ τ ((hDec _ Ω A t hA p hp hpt ζ hζ).2 τ hτ), map_one]
  · intro τ hτ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      chi_one hζ τ ((hDec _ Ω A v hA p hp hpv ζ hζ).2 τ hτ), map_one]
  · have hN : ¬ A.valuation (p : Ω) < 1 := by
      simpa using not_valuation_lt_one_of_isPlaceOver hpv hA 1
    have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
    have hv : A.valuation ζ ≤ 1 := by
      have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
      exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
    have hφζ : φ ζ = ζ ^ normV v := by
      refine eq_of_pow_eq_one A hN ?_ ?_ (hφ.2 ζ hv)
      · rw [← map_pow, hz1, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
    have h1 : hζ.autToPow (maximalRealSubfield E) φ = a := by
      apply Units.ext
      rw [chi_of_pow hζ φ _ hφζ, ha, ZMod.coe_unitOfCoprime]
    rw [MonoidHom.comp_apply, h1]
    exact hlamo
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.kumMove :
    MoveRoot → NormVal → KumMove := by
  intro hMR hNV Ω _ _ _ U hU ℓ q hℓ hq
  obtain ⟨b, σ0, hσ0U, hσ0⟩ := hMR Ω U hU ℓ hℓ
  obtain ⟨D, hDpos, hD⟩ := hNV Ω U hU q hq
  obtain ⟨e, D', hD'ℓ, hDe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hDpos.ne' ℓ hℓ.one_lt.ne'
  refine ⟨b + e, fun k hk ζ y hζ hy => ?_⟩
  by_contra hcon
  push_neg at hcon
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hpow : ∀ τ : G ℚ Ω, ∃ a, τ ζ = ζ ^ a := by
    intro τ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  have hact : ∀ (τ : G ℚ Ω) (a : ℕ), τ ζ = ζ ^ a → ∀ ω : Ω, ω ^ (ℓ ^ k) = 1 → τ ω = ω ^ a := by
    intro τ a ha ω hω
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hω
    rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]
  have comm : ∀ σ ∈ U, ∀ τ ∈ U, σ (τ y) = τ (σ y) := by
    intro σ hσ τ hτ
    obtain ⟨a, ha⟩ := hpow σ
    obtain ⟨c, hc⟩ := hpow τ
    have h1 : ((τ * σ)⁻¹ * (σ * τ)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
        AlgEquiv.mul_apply, hc, ha, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, mul_comm]
    have h2 := hcon _ (U.mul_mem (U.inv_mem (U.mul_mem hτ hσ)) (U.mul_mem hσ hτ)) h1
    rwa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply] at h2
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hy
    exact hq0 hy.symm
  obtain ⟨a0, ha0⟩ := hpow σ0
  obtain ⟨a, ha, ha1⟩ : ∃ a, σ0 ζ = ζ ^ a ∧ 1 ≤ a :=
    ⟨a0 + ℓ ^ k, by rw [ha0, pow_add, hζ.pow_eq_one, mul_one],
      by have := Nat.one_le_pow k ℓ hℓ.pos; omega⟩
  have hjk : ℓ ^ (b + e) ∣ ℓ ^ k := pow_dvd_pow ℓ hk
  have hzfix : ∀ τ ∈ U, τ (σ0 y / y ^ a) = σ0 y / y ^ a := by
    intro τ hτ
    have hτy : (τ y) ^ (ℓ ^ (b + e)) = y ^ (ℓ ^ (b + e)) := by
      rw [← map_pow, hy, map_natCast]
    obtain ⟨χ, hτy'⟩ : ∃ χ, τ y = y * χ := ⟨τ y / y, by field_simp⟩
    have hχj : χ ^ ℓ ^ (b + e) = 1 := by
      rw [hτy', mul_pow] at hτy
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) (hτy.trans (mul_one _).symm)
    have hχ1 : χ ^ (ℓ ^ k) = 1 := by
      obtain ⟨m, hm⟩ := hjk
      rw [hm, pow_mul, hχj, one_pow]
    have hχ0 : χ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hχ1
      exact zero_ne_one hχ1
    rw [map_div₀, map_pow, comm τ hτ σ0 hσ0U, hτy', map_mul, hact σ0 a ha χ hχ1, mul_pow]
    exact mul_div_mul_right _ _ (pow_ne_zero _ hχ0)
  have hzeq : (σ0 y / y ^ a) ^ (ℓ ^ (b + e)) * (q : Ω) ^ (a - 1) = 1 := by
    have hσy : (σ0 y) ^ (ℓ ^ (b + e)) = q := by rw [← map_pow, hy, map_natCast]
    rw [div_pow, hσy, ← pow_mul', pow_mul, hy]
    have hqa : (q : Ω) ^ a = (q : Ω) ^ (a - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel ha1]
    rw [hqa]
    field_simp
  have hdiv := hD _ (ℓ ^ (b + e)) (a - 1) hzfix hzeq
  have hb : ℓ ^ b ∣ a - 1 := by
    rw [pow_add, hDe] at hdiv
    have h' : ℓ ^ b * ℓ ^ e ∣ ((a - 1) * D') * ℓ ^ e := by
      have : (a - 1) * (ℓ ^ e * D') = ((a - 1) * D') * ℓ ^ e := by ring
      rwa [this] at hdiv
    have h'' := Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos e) h'
    exact (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hD'ℓ)).dvd_of_dvd_mul_right h''
  obtain ⟨t, ht⟩ := hb
  have hbk : b ≤ k := by omega
  have hξ : IsPrimitiveRoot (ζ ^ ℓ ^ (k - b)) (ℓ ^ b) := by
    have := hζ.pow_of_dvd (p := ℓ ^ (k - b)) (pow_ne_zero _ hℓ.ne_zero)
      (pow_dvd_pow ℓ (Nat.sub_le k b))
    rwa [Nat.pow_div (Nat.sub_le k b) hℓ.pos, Nat.sub_sub_self hbk] at this
  apply hσ0 _ hξ
  rw [map_pow, ha, ← pow_mul]
  have h1 : a = 1 + ℓ ^ b * t := by rw [← ht]; omega
  have h2 : a * ℓ ^ (k - b) = ℓ ^ (k - b) + ℓ ^ k * t := by
    rw [h1, add_mul, one_mul, mul_comm (ℓ ^ b) t, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hbk, mul_comm t]
  rw [h2, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_mem_asIdeal_of_normV_eq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    (hN : normV u = p) : ((p : 𝓞 F)) ∈ u.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hN]
  unfold Formalism.ConjugateSelfDual.normV
  simpa using card_nsmul_eq_zero' (G := 𝓞 F ⧸ u.asIdeal) (x := 1)

private theorem valuation_le_one_of_pow_eq_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (y : Ω) (n : ℕ) (hn : 0 < n)
    (h : y ^ n = 1) : A.valuation y ≤ 1 := by
  have h1 : A.valuation y ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_le_one_iff hn.ne').mp h1.le

private theorem not_valuation_natCast_lt_one_of_prime_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p n : ℕ) (hp : Nat.Prime p)
    (hpn : ¬ p ∣ n) (hvp : A.valuation (p : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro hvn
  have hc : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  have hb : ((Nat.gcd p n : ℤ)) = p * Nat.gcdA p n + n * Nat.gcdB p n := Nat.gcd_eq_gcd_ab p n
  rw [hc.gcd_eq_one] at hb
  have hb' : (1 : Ω) = (p : Ω) * (Nat.gcdA p n : Ω) + (n : Ω) * (Nat.gcdB p n : Ω) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hb
  have hA : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have h1 : A.valuation ((p : Ω) * (Nat.gcdA p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvp (hA _)
  have h2 : A.valuation ((n : Ω) * (Nat.gcdB p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvn (hA _)
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hb', map_one] at h3
  exact lt_irrefl _ h3

open Polynomial in
private theorem exists_zmod_castHom_eq_of_pow_char_eq_self {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (z : K)
    (hz : z ^ p = z) : ∃ k : ZMod p, (ZMod.castHom (dvd_refl p) K) k = z := by
  set f := ZMod.castHom (dvd_refl p) K
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [hcard] at this
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast hp.out.one_lt
  have hdeg : (X ^ p - X : (ZMod p)[X]).roots.card = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, Polynomial.natDegree_X_pow_sub_X hp.out.one_lt]
    simp [hcard]
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hdeg
  have hev := congrArg (fun P => (P.map f).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, eval_sub, eval_X, eval_C,
    eval_pow, hz, sub_self] at hev
  obtain ⟨w, -, hw0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)
  exact ⟨w, (sub_eq_zero.mp hw0).symm⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.rootMod :
    RootMod := by
  intro F Ω _ _ _ _ _ A u hu p hp hN y n hn hfix
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hu
  have hfy : σ y = y := hfix σ hσD
  have hvp : A.valuation (p : Ω) < 1 := by
    have h := (hu (p : 𝓞 F)).mpr (natCast_mem_asIdeal_of_normV_eq u p hN)
    simpa using h
  refine ⟨fun m hm => ?_, fun hprim hpn => ?_⟩
  · have hvy : A.valuation y ≤ 1 := by
      have h1 : A.valuation y ^ n ≤ 1 := by
        rw [← map_pow, hm]; exact valuation_natCast_le_one A m
      exact (pow_le_one_iff hn.ne').mp h1
    have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hvy
    set yA : A := ⟨y, hyA⟩
    set r := IsLocalRing.residue A
    have hp0 : ((p : IsLocalRing.ResidueField A)) = 0 := by
      rw [← map_natCast r, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simpa using hvp
    have hch : ringChar (IsLocalRing.ResidueField A) = p :=
      (hp.eq_one_or_self_of_dvd _ (ringChar.dvd hp0)).resolve_left (CharP.ringChar_ne_one)
    haveI := ringChar.of_eq hch
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hry : r yA ^ p = r yA := by
      have h0 : r (yA - yA ^ p) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        simpa using hlt
      rw [map_sub, map_pow, sub_eq_zero] at h0
      exact h0.symm
    obtain ⟨k, hk⟩ := exists_zmod_castHom_eq_of_pow_char_eq_self p (r yA) hry
    have hyn : yA ^ n = (m : A) := by
      apply Subtype.ext
      simpa using hm
    have hkm : (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (k ^ n) =
        (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (m : ZMod p) := by
      rw [map_pow, hk, ← map_pow, hyn, map_natCast, map_natCast]
    exact ⟨k, (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).injective hkm⟩
  · have hyn : y ^ n = 1 := hprim.pow_eq_one
    have hvy := valuation_le_one_of_pow_eq_one' A y n hn hyn
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hvn := not_valuation_natCast_lt_one_of_prime_not_dvd A p n hp hpn hvp
    have hyp : y = y ^ p := by
      refine eq_of_pow_eq_one A hvn hyn ?_ hlt
      rw [← pow_mul, mul_comm, pow_mul, hyn, one_pow]
    have hy0 : y ≠ 0 := hprim.ne_zero hn.ne'
    have hp1 : y ^ (p - 1) = 1 := by
      have h2 : y ^ (p - 1) * y = 1 * y := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_le]
        exact hyp.symm
      exact mul_right_cancel₀ hy0 h2
    exact hprim.dvd_of_pow_eq_one _ hp1
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.moveRoot :
    MoveRoot := by
  intro Ω _ _ _ U hU ℓ hℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 (hU.mem_nhds U.one_mem)
  haveI := hEfin
  set b := Module.finrank ℚ E + 2 with hb
  have hn : 0 < ℓ ^ b := pow_pos hℓ.pos b
  haveI : NeZero ((ℓ ^ b : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ0, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ b) Ω)
    (Polynomial.degree_cyclotomic_pos _ Ω hn).ne'
  have hprim : IsPrimitiveRoot ζ0 (ℓ ^ b) := Polynomial.isRoot_cyclotomic_iff.1 hζ0
  have hnot : ζ0 ∉ E := by
    intro hmem
    have h0 := minpoly.natDegree_le (A := ℚ) (⟨ζ0, hmem⟩ : E)
    have h0' := IntermediateField.minpoly_eq (K := ℚ) (S := E) ⟨ζ0, hmem⟩
    have h1 : (minpoly ℚ ζ0).natDegree ≤ Module.finrank ℚ E := h0' ▸ h0
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim hn,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hℓ (by omega)] at h1
    have h2 : b - 1 < ℓ ^ (b - 1) := Nat.lt_pow_self hℓ.one_lt
    have h3 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    have h4 : ℓ ^ (b - 1) ≤ Module.finrank ℚ E :=
      (Nat.le_mul_of_pos_right _ h3).trans h1
    generalize ℓ ^ (b - 1) = N at h2 h4
    omega
  have hex : ∃ σ ∈ E.fixingSubgroup, σ ζ0 ≠ ζ0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    exact hcon
  obtain ⟨σ, hσE, hσ⟩ := hex
  refine ⟨b, σ, hEsub hσE, fun ζ hζ hfix => hσ ?_⟩
  haveI : NeZero (ℓ ^ b) := ⟨hn.ne'⟩
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  rw [← hm, map_pow, hfix]
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_injective_char (p : ℕ) [Fact p.Prime] :
    ∃ lam0 : (ZMod p)ˣ →* ℂˣ, Function.Injective lam0 :=
  _root_.UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char p

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.charOrd : CharOrd := by
  intro p _ ℓ k a hℓ hdvd
  obtain ⟨lam0, hinj⟩ := exists_injective_char p
  have hm0 : 0 < orderOf (a ^ 2) := orderOf_pos _
  have h2m : orderOf a ∣ 2 * orderOf (a ^ 2) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  have hlk : ℓ ^ k ∣ orderOf (a ^ 2) := by
    have h1 : ℓ ^ (k + 1) ∣ 2 * orderOf (a ^ 2) := hdvd.trans h2m
    by_cases h2 : ℓ = 2
    · subst h2
      rw [pow_succ, mul_comm] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    · have hc : Nat.Coprime (ℓ ^ (k + 1)) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr h2)
      exact (Dvd.intro _ (pow_succ ℓ k).symm).trans (hc.dvd_of_dvd_mul_left h1)
  obtain ⟨e, he⟩ := hlk
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      omega
    · exact h
  have hlpos : 0 < ℓ ^ k := pow_pos hℓ.pos k
  refine ⟨lam0 ^ (2 * e), ?_, ?_⟩
  · rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    simp
  · have h1 : (lam0 ^ (2 * e)) a = (lam0 (a ^ 2)) ^ e := by
      rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    have h2 : orderOf (lam0 (a ^ 2)) = ℓ ^ k * e := by
      rw [orderOf_injective lam0 hinj, he]
    rw [h1, orderOf_pow' _ hepos.ne', h2, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ hepos]
end
