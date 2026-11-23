module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ClsIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ImgRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem not_over_odd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (h2 : A.valuation ((2 : ℕ) : Ω) < 1) {n : ℕ}
    (hn : Odd n) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨k, rfl⟩ := hn
  have h1 : A.valuation (((2 : ℕ) : Ω) * (k : Ω)) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le h2 ((A.valuation_le_one_iff _).2 (natCast_mem A k))
  have h3 := A.valuation.map_sub_lt h h1
  have e : ((2 * k + 1 : ℕ) : Ω) - ((2 : ℕ) : Ω) * (k : Ω) = 1 := by push_cast; ring
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

private theorem neg_mem_range (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ∈ (proj 2 (2 ^ n)).range := by
  rw [(projFacts (2 ^ n) 2 Nat.prime_two).2.2.2.2.2.1, MonoidHom.mem_ker]
  have e : ordCompl[2] (2 ^ n) = 1 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  have : Subsingleton (ZMod (ordCompl[2] (2 ^ n))) := by rw [e]; infer_instance
  exact Subsingleton.elim _ _

theorem UpperTheory.V.Ws.large₂.eltTwo :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∃ g ∈ D.Ip 2, D.ξ g = -1 ∧ D.ψ g = 1 ∧ D.om g = 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, -, -, -, -, ⟨-, -, hodd, -⟩, -, hψ, -, hp, ξ', ξ₀, -, hξ', -, hξ⟩
  have hA := hG.pl_over 2 Nat.prime_two
  have hlo : Odd l := hl.out.odd_of_ne_two hG.l_odd
  have hpo : Odd (pOne h.chi) :=
    Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) (pK_pOne_prime_conditions h.chi).2.1.2.2)
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hG.om_bar σ⟩
  have h1 : D.Ip 2 ≤ D.om.ker := ((omT Ω l c).2 D.om hom).2.2.2.2.2.1 _ (not_over_odd _ hA hlo)
  have h2 : D.Ip 2 ≤ (Chr.cls ℚ Ω (pOne h.chi)).ker :=
    (Chr.clsFacts ℚ Ω (pOne h.chi)).2.2.2.2 _ (not_over_odd _ hA hpo)
  obtain ⟨g, hg, hc⟩ : (-1 : (ZMod (2 ^ h.nIII l ψ))ˣ) ∈ (D.Ip 2).map (Chr.cls ℚ Ω (2 ^ h.nIII l ψ)) := by
    rw [(compIne Ω (2 ^ h.nIII l ψ) 2 Nat.prime_two _ hA).1]
    exact neg_mem_range _ _
  have h3 : D.ξ g = -1 := by
    have h4 : Chr.cls ℚ Ω (pOne h.chi) g = 1 := h2 hg
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, h4, hc, map_one, one_mul]
    ext1
    rw [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, hξ', Units.val_neg, Units.val_one]
  refine ⟨g ^ orderOf ψ, pow_mem hg _, by rw [map_pow, h3, hodd.neg_one_pow], ?_, h1 (pow_mem hg _)⟩
  rw [hψ, Chr.dirG, MonoidHom.comp_apply, map_pow, map_pow]
  ext1
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem dirG_pow_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {m : ℕ} (h : χ ^ m = 1) : UpperTheory.V.Chr.dirG ℚ Ω χ ^ m = 1 := by
  ext g
  have hg := congrArg (fun ψ : DirichletCharacter O N => ψ ((UpperTheory.V.Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N)) h
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hg
  simp [UpperTheory.V.Chr.dirG, hg]

private theorem dirG_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ} (hA : A.valuation (v : Ω) < 1) (hN : v.Coprime N)
    {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) : UpperTheory.V.Chr.dirG ℚ Ω χ g = 1 := by
  have hnot : ¬ A.valuation (N : Ω) < 1 := by
    intro hNv
    have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one (⟨z, by simp⟩ : A)
    have hgcd := Nat.gcd_eq_gcd_ab v N
    rw [hN] at hgcd
    have h1 : ((1 : ℤ) : Ω) = (v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω) := by
      exact_mod_cast hgcd
    have hlt : A.valuation ((v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hA (hint _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hNv (hint _)
    rw [← h1] at hlt
    simp at hlt
  have hker := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 A hnot hg
  rw [MonoidHom.mem_ker] at hker
  simp [UpperTheory.V.Chr.dirG, hker]

private theorem not_dvd_card {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (φ : Γ →* Oˣ) {m l : ℕ} [Fact l.Prime]
    (hm : m ≠ 0) (hl : l.Coprime m) (h : φ ^ m = 1) (H : Subgroup Γ) : ¬ l ∣ Nat.card (H.map φ) := by
  intro hdvd
  haveI : NeZero m := ⟨hm⟩
  have hle : H.map φ ≤ rootsOfUnity m O := by
    rintro _ ⟨x, -, rfl⟩
    rw [mem_rootsOfUnity]
    have := congrArg (fun f => f x) h
    simpa [MonoidHom.pow_apply] using this
  haveI : Finite (H.map φ) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H.map φ) l hdvd
  have hym : orderOf y ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨x, -, hx⟩ := y.2
    apply Subtype.ext
    have := congrArg (fun f => f x) h
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    simp [← hx, this]
  rw [hy] at hym
  have := Nat.Coprime.eq_one_of_dvd hl hym
  exact (Fact.out : l.Prime).one_lt.ne' this

theorem UpperTheory.V.Ws.large₂.host3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → 5 ≤ l ∧ l - 1 ∣ 2 * D.e ∧ D.Sb = ∅ ∧ (∃ m : ℕ, Odd m ∧ l.Coprime m ∧ D.ψ ^ m = 1) ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.ξ.ker ⊓ D.ψ.ker := by
  intro Ω _ _ _ l _ c D h3
  obtain ⟨hG, h, t, e, ψ, hBig, he0, het, hX, hIII, hA⟩ := h3
  obtain ⟨he, hψ, hS, hx⟩ := hA
  obtain ⟨_, ξ', ξ₀, -, -, -, hξ⟩ := hx
  obtain ⟨hlB, hle, hodd, -⟩ := hIII
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := hG.l_odd
  obtain ⟨-, -, -, -, hB⟩ := bchiFacts h t hBig
  obtain ⟨h5, hno, -, -, -, hl1, -, hfin⟩ := hB l hlp hl2 hlB
  have hlN : ¬ l ∣ h.N := (hfin e he0 het hle).2.2
  have hchar := ((Host.mem_X h).1 hX).1
  have hdo := ((hostOdd h c.O ψ hchar).1 hodd).1
  have hcop : l.Coprime (orderOf ψ) := by
    rw [Nat.Prime.coprime_iff_not_dvd hlp]
    intro hd
    exact hno (hd.trans (hdo.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ _))))
  have hpow : D.ψ ^ orderOf ψ = 1 := by
    rw [hψ]; exact dirG_pow_one ψ (pow_orderOf_eq_one ψ)
  have hm0 : orderOf ψ ≠ 0 := by
    intro h0; rw [h0] at hodd; exact Nat.not_odd_zero hodd
  refine ⟨h5, he ▸ hle, ?_, ⟨orderOf ψ, hodd, hcop, hpow⟩, ?_⟩
  · rw [GradeZeroInterpolatingElement.Raw.Sb, Finset.filter_eq_empty_iff]
    rintro p - ⟨-, hd⟩
    exact not_dvd_card D.ψ hm0 hcop hpow _ hd
  · intro A hA g hg
    have hcN : l.Coprime h.N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
    have hc1 : l.Coprime (UpperTheory.V.pOne h.chi) :=
      (Nat.coprime_primes hlp (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1).2 hl1
    have hc2 : l.Coprime (2 ^ h.nIII l ψ) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hl2)
    refine ⟨?_, ?_⟩
    · show g ∈ D.ξ.ker
      rw [MonoidHom.mem_ker, hξ, MonoidHom.mul_apply, dirG_unr ξ₀ hA hc1 hg, dirG_unr ξ' hA hc2 hg, mul_one]
    · show g ∈ D.ψ.ker
      rw [MonoidHom.mem_ker, hψ, dirG_unr ψ hA hcN hg]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem pow_two_pow (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ^ 2 ^ n = 1 := by
  have h : Nat.totient (2 ^ n) ∣ 2 ^ n := by
    rcases n with _ | n
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simpa using pow_dvd_pow 2 (Nat.le_succ n)
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one (ZMod.pow_totient u)).trans h)

private theorem pow_ord {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (a : (ZMod N)ˣ) :
    ψ.toUnitHom a ^ orderOf ψ = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one]

private theorem half {Γ : Type} [CommGroup Γ] {y : Γ} {m : ℕ} (hm : Odd m) (hy : y ^ m = 1) :
    ∃ x : Γ, x ^ 2 = y ∧ x ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  refine ⟨y ^ (k + 1), ?_, ?_⟩
  · rw [← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, hy, one_mul]
  · rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]

theorem UpperTheory.V.Ws.large₂.eltOdd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∀ s : ℤ, s = 1 ∨ s = -1 → ∃ (g : G ℚ Ω) (m : ℕ), Odd m ∧ l.Coprime m ∧ D.om g = 1 ∧ D.ξ g ^ 2 = D.ψ g ^ s ∧ D.ξ g ^ m = 1 ∧ D.ξ g ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, hB, he, het, hX, ⟨hlB, hle, hodd, hne⟩, hO⟩ s hs
  obtain ⟨-, hψ, -, _, ξ', ξ₀, -, -, hord, hξ⟩ := hO
  have lp : l.Prime := hl.out
  obtain ⟨-, -, -, hpN, hb⟩ := bchiFacts h t hB
  obtain ⟨-, hlo, -, -, -, hlp, -, hb⟩ := hb l lp hG.l_odd hlB
  obtain ⟨-, -, hlN⟩ := hb e he het hle
  obtain ⟨-, ⟨pp, -, pc⟩, -⟩ := UpperTheory.V.pK_pOne_prime_conditions h.chi
  have hdo : orderOf ψ ∣ h.o :=
    (((hostOdd h c.O ψ (h.mem_X.1 hX).1).1 hodd).1).trans (Nat.ordCompl_dvd _ _)
  have hlm : l.Coprime (orderOf ψ) := lp.coprime_iff_not_dvd.2 fun hd => hlo (hd.trans hdo)
  haveI : NeZero l := ⟨lp.ne_zero⟩
  generalize UpperTheory.V.pOne h.chi = p at *
  generalize h.nIII l ψ = n at *
  have hom : ∀ g, Chr.cls ℚ Ω l g = 1 → D.om g = 1 := by
    have hT : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
      have := hG.om_bar σ
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      exact sub_eq_zero.2 this⟩
    intro g hg
    have hk := ((omT Ω l c).2 D.om hT).2.1
    rw [← MonoidHom.mem_ker, hk]
    exact hg
  obtain ⟨a, ha⟩ : ∃ a : (ZMod h.N)ˣ, ψ.toUnitHom a ≠ 1 := by
    by_contra hc
    push Not at hc
    apply hne
    ext a
    rw [MulChar.one_apply_coe, ← MulChar.coe_toUnitHom, hc a, Units.val_one]
  haveI : NeZero (l * p) := ⟨mul_ne_zero lp.ne_zero pp.ne_zero⟩
  have c1 : h.N.Coprime (l * p) :=
    Nat.Coprime.mul_right (lp.coprime_iff_not_dvd.2 hlN).symm (pp.coprime_iff_not_dvd.2 hpN).symm
  obtain ⟨u, hu, hu'⟩ := UpperTheory.V.Ws.large₂.clsIndep (Ω := Ω) h.N (l * p) c1 a
  have hy : (ψ.toUnitHom a ^ 2 ^ n) ^ s ≠ 1 := by
    have h1 : ψ.toUnitHom a ^ 2 ^ n ≠ 1 := by
      intro h2
      apply ha
      have hc : (2 ^ n).Coprime (orderOf ψ) := (Nat.coprime_two_left.2 hodd).pow_left _
      have := pow_gcd_eq_one.2 ⟨h2, pow_ord ψ a⟩
      rwa [hc.gcd_eq_one, pow_one] at this
    rcases hs with rfl | rfl
    · simpa using h1
    · simpa using h1
  have hym : ((ψ.toUnitHom a ^ 2 ^ n) ^ s) ^ orderOf ψ = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm, pow_mul, pow_ord, one_pow,
      one_zpow]
  obtain ⟨x, hx2, hxm⟩ := half hodd hym
  obtain ⟨b, hb⟩ := UpperTheory.V.Ws.large₂.imgRoots p ξ₀ x (hord ▸ hxm)
  haveI : NeZero (h.N * l * 2 ^ n) := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne _) lp.ne_zero) (by positivity)⟩
  have c2 : p.Coprime (h.N * l * 2 ^ n) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (pp.coprime_iff_not_dvd.2 hpN) ?_) (Nat.Coprime.pow_right _ ?_)
    · exact (Nat.coprime_primes pp lp).2 hlp.symm
    · exact Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) pc
  obtain ⟨v, hv, hv'⟩ := UpperTheory.V.Ws.large₂.clsIndep (Ω := Ω) p (h.N * l * 2 ^ n) c2 b
  have e1 : D.ξ (u ^ 2 ^ n * v) = x := by
    have f1 : Chr.cls ℚ Ω p (u ^ 2 ^ n * v) = b := by
      rw [map_mul, map_pow, hu' p (dvd_mul_left _ _), hv, one_pow, one_mul]
    have f2 : Chr.cls ℚ Ω (2 ^ n) (u ^ 2 ^ n * v) = 1 := by
      rw [map_mul, map_pow, hv' (2 ^ n) (dvd_mul_left _ _), pow_two_pow, one_mul]
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, f1, f2, map_one, mul_one, hb]
  have e2 : D.ψ (u ^ 2 ^ n * v) = ψ.toUnitHom a ^ 2 ^ n := by
    rw [hψ, Chr.dirG, MonoidHom.comp_apply, map_mul, map_pow, hu, hv' h.N ((dvd_mul_right _ _).mul_right _), mul_one,
      map_pow]
  refine ⟨u ^ 2 ^ n * v, orderOf ψ, hodd, hlm, hom _ ?_, by rw [e1, e2, hx2], by rw [e1, hxm], ?_⟩
  · rw [map_mul, map_pow, hu' l (dvd_mul_right _ _), hv' l ((dvd_mul_left _ _).mul_right _), one_pow, one_mul]
  · rw [e1]
    rintro rfl
    exact hy (by rw [← hx2, one_pow])
end
