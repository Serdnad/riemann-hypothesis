module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle001
public import Development.AutomorphicArithmetic.QuadraticCharacters.GaussRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem lcm_le_mul' {a b c d : ℕ} (hc : a ≤ c) (hd : b ≤ d) (ha : 0 < a) (hb : 0 < b) :
    Nat.lcm a b ≤ c * d := by
  exact (Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))).trans
    (Nat.mul_le_mul hc hd)

private theorem descend {E : Type} [Field E] [NumberField E] {N L : ℕ} [NeZero N]
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N) (hL : L ∣ N)
    (H : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      a ≡ 1 [MOD L] → ∀ x : E, τ (j x) = j x) :
    Nonempty (E →ₐ[ℚ] CyclotomicField L ℚ) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact hN0 (Nat.eq_zero_of_zero_dvd hL)
  haveI : NeZero L := ⟨hL0⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN0⟩
  haveI : NeZero ((L : ℕ) : ℚ) := ⟨by exact_mod_cast hL0⟩
  obtain ⟨M, hNLM⟩ := hL
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [hNLM, mul_zero])
  have hMdvd : M ∣ N := ⟨L, by rw [hNLM, mul_comm]⟩
  have hk : N / M = L := by
    rw [hNLM, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM0)]
  have hη : IsPrimitiveRoot (ζ ^ M) L := by
    have := hζ.pow_of_dvd hM0 hMdvd
    rwa [hk] at this
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsCyclotomicExtension {L} ℚ (CyclotomicField L ℚ) :=
    CyclotomicField.isCyclotomicExtension L ℚ
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.finiteDimensional {N} ℚ _
  let F : IntermediateField ℚ (CyclotomicField N ℚ) := IntermediateField.adjoin ℚ {ζ ^ M}
  haveI : IsCyclotomicExtension {L} ℚ F := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hmem : ∀ x : E, j x ∈ F := by
    intro x
    rw [← IsGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hτη : τ (ζ ^ M) = ζ ^ M := hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    have hpow : (τ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, hζa⟩ := hζ.eq_pow_of_pow_eq_one hpow
    apply H τ a hζa.symm
    have h1 : ζ ^ (a * M) = ζ ^ (1 * M) := by
      rw [pow_mul, hζa, ← map_pow, hτη, one_mul]
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have h2 : a * M ≡ 1 * M [MOD N] := by
      unfold Nat.ModEq
      apply hζ.pow_inj (Nat.mod_lt _ hNpos) (Nat.mod_lt _ hNpos)
      have e1 := pow_mod_orderOf ζ (a * M)
      have e2 := pow_mod_orderOf ζ (1 * M)
      rw [← hζ.eq_orderOf] at e1 e2
      rw [e1, e2, h1]
    rw [hNLM] at h2
    exact Nat.ModEq.mul_right_cancel' hM0 h2
  exact ⟨(IsCyclotomicExtension.algEquiv {L} ℚ F (CyclotomicField L ℚ)).toAlgHom.comp
    (j.codRestrict F.toSubalgebra hmem)⟩

private theorem finrank_le {E : Type} [Field E] [NumberField E] {c : ℕ} (hc : 0 < c)
    (j : E →ₐ[ℚ] CyclotomicField c ℚ) : Module.finrank ℚ E ≤ c := by
  haveI : NeZero c := ⟨hc.ne'⟩
  haveI : NeZero ((c : ℕ) : ℚ) := ⟨by exact_mod_cast hc.ne'⟩
  haveI : IsCyclotomicExtension {c} ℚ (CyclotomicField c ℚ) := CyclotomicField.isCyclotomicExtension c ℚ
  haveI : FiniteDimensional ℚ (CyclotomicField c ℚ) := IsCyclotomicExtension.finiteDimensional {c} ℚ _
  calc Module.finrank ℚ E ≤ Module.finrank ℚ (CyclotomicField c ℚ) :=
        LinearMap.finrank_le_finrank_of_injective (f := j.toLinearMap) j.toRingHom.injective
    _ = c.totient := IsCyclotomicExtension.finrank _ (Polynomial.cyclotomic.irreducible_rat hc)
    _ ≤ c := Nat.totient_le c

theorem UpperTheory.V.conductor_bounds_of_isChiField :
    ∀ (ψ : PChar) (e q d : ℕ), 0 < q → 0 < d → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
      1 ≤ condF E ∧ condF E ≤ 2 ^ (e + 2) * ψ.N * q * d ∧ Module.finrank ℚ E ≤ condF E := by
  intro ψ e q d hq hd E _ _ hE
  obtain ⟨N, hNZ, j, ζ, h2, hψ, hqN, hdN, hζ, hτ⟩ := hE
  haveI := hNZ
  haveI := ψ.ne
  have hψpos : 0 < ψ.N := NeZero.pos ψ.N
  have hApos : 0 < 2 ^ (e + 2) := pow_pos two_pos _
  have hLN : Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d ∣ N :=
    Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h2 hψ) hqN) hdN
  have d1 : 2 ^ (e + 2) ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  have dψ : ψ.N ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  have dq : q ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)
  have dd : d ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d := Nat.dvd_lcm_right _ _
  have jac : ∀ (a m : ℕ), a ≡ 1 [MOD m] → jacobiSym (a : ℤ) m = 1 := by
    intro a m h
    have hm : (a : ℤ) % (m : ℤ) = 1 % (m : ℤ) := by
      unfold Nat.ModEq at h
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) h
    rw [jacobiSym.mod_left, hm, ← jacobiSym.mod_left, jacobiSym.one_left]
  have hemb := descend j hζ hLN (by
    intro τ a hτa ha x
    refine ((hτ τ a hτa).mpr ⟨Or.inl (ha.of_dvd d1), ?_, jac a q (ha.of_dvd dq), jac a d (ha.of_dvd dd)⟩) x
    show ψ.χ (a : ZMod ψ.N) = 1
    have h' : ((a : ℕ) : ZMod ψ.N) = ((1 : ℕ) : ZMod ψ.N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (ha.of_dvd dψ)
    rw [h', Nat.cast_one, MulChar.map_one])
  have hLpos : 0 < Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    Nat.pos_of_dvd_of_pos hLN (NeZero.pos N)
  unfold condF
  have hset : Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d ∈
      {N | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} := ⟨hLpos, hemb⟩
  have hmem := Nat.sInf_mem ⟨_, hset⟩
  refine ⟨hmem.1, (Nat.sInf_le hset).trans ?_, ?_⟩
  · have hY := lcm_le_mul' (le_refl (2 ^ (e + 2))) (le_refl ψ.N) hApos hψpos
    have hX := lcm_le_mul' hY (le_refl q) (Nat.lcm_pos hApos hψpos) hq
    exact lcm_le_mul' hX (le_refl d) (Nat.lcm_pos (Nat.lcm_pos hApos hψpos) hq) hd
  · obtain ⟨hpos, ⟨j'⟩⟩ := hmem
    exact finrank_le hpos j'
end

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.exists_numberField_isAbField_finrank_eq_deg :
    ∀ A : AbF, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsAbField A L ∧ Module.finrank ℚ L = A.deg := by
  intro A
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : NeZero ((A.m : ℚ)) := ⟨by exact_mod_cast A.pos.ne'⟩
  haveI hcyc : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
    CyclotomicField.isCyclotomicExtension A.m ℚ
  haveI : IsGalois ℚ (CyclotomicField A.m ℚ) :=
    IsCyclotomicExtension.isGalois {A.m} ℚ (CyclotomicField A.m ℚ)
  have hirr := Polynomial.cyclotomic.irreducible_rat A.pos
  let e := IsCyclotomicExtension.autEquivPow (CyclotomicField A.m ℚ) hirr
  let G : Subgroup Gal(CyclotomicField A.m ℚ/ℚ) := A.H.comap e.toMonoidHom
  let F := IntermediateField.fixedField G
  refine ⟨F, inferInstance, inferInstance, ?_, ?_⟩
  · have hζ := IsCyclotomicExtension.zeta_spec A.m ℚ (CyclotomicField A.m ℚ)
    refine ⟨A.m, inferInstance, F.val, IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ),
      dvd_rfl, hζ, ?_⟩
    intro τ a hτ
    have hspec := IsPrimitiveRoot.autToPow_spec ℚ hζ τ
    have he : ((e τ : (ZMod A.m)ˣ) : ZMod A.m) = a := by
      have h1 : IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ) ^ ((e τ : (ZMod A.m)ˣ) : ZMod A.m).val
          = IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ) ^ a := by
        rw [← hτ, ← hspec]
        rfl
      have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζ.pow_eq_one⟩
      rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
      rw [← ZMod.natCast_zmod_val ((e τ : (ZMod A.m)ˣ) : ZMod A.m)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    have hfix : (∀ x : F, τ (F.val x) = F.val x) ↔ τ ∈ G := by
      rw [← IntermediateField.fixingSubgroup_fixedField G, IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hker : τ ∈ G ↔ A.ker a := by
      rw [Subgroup.mem_comap]
      constructor
      · intro h
        exact ⟨e τ, h, he⟩
      · rintro ⟨u, hu, hua⟩
        have hue : u = e τ := Units.ext (hua.trans he.symm)
        have hmem : e τ ∈ A.H := hue ▸ hu
        exact hmem
    exact hfix.trans hker
  · have h1 := Module.finrank_mul_finrank ℚ F (CyclotomicField A.m ℚ)
    rw [IntermediateField.finrank_fixedField_eq_card,
      ← IsGalois.card_aut_eq_finrank ℚ (CyclotomicField A.m ℚ),
      ← Subgroup.index_mul_card G] at h1
    have hpos : 0 < Nat.card G := Nat.card_pos
    have h2 : Module.finrank ℚ F = G.index := Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h2]
    exact Subgroup.index_comap_of_surjective _ e.surjective
end

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem act_root {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ x : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) (hx : x ^ N = 1) : σ x = x ^ a := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hσ, pow_right_comm]

private theorem coprime_of {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) : a.Coprime N := by
  have h1 : IsPrimitiveRoot (ζ ^ a) N := by
    rw [← hσ]
    exact hζ.map_of_injective σ.injective
  exact (hζ.pow_iff_coprime (NeZero.pos N) a).1 h1

private theorem sqrt_iff {K : Type} [Field K] [CharZero K] {N : ℕ} [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hd : q ∣ N)
    {α : K} (hα : α ^ 2 = -(q : K)) : σ α = α ↔ jacobiSym (a : ℤ) q = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hd
  have hω : IsPrimitiveRoot (ζ ^ k) q := hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])
  obtain ⟨G, hG, hs⟩ := HostParam.SlopeTestRemainingChoices.GaussRoot.exists_gauss h4 hω
  have hc : a.Coprime q := (coprime_of hζ σ hσ).coprime_dvd_right ⟨k, hk⟩
  have h1 := hs σ a hc (by rw [map_pow, hσ, pow_right_comm])
  have h2 : σ α = ((quadraticChar (ZMod q) (a : ZMod q) : ℤ) : K) * α := by
    rcases HostParam.SlopeTestRemainingChoices.GaussRoot.eq_or_neg hα hG with rfl | rfl
    · exact h1
    · rw [map_neg, h1, mul_neg]
  have h3 : jacobiSym (a : ℤ) q = quadraticChar (ZMod q) (a : ZMod q) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]
  rw [h3, h2, mul_left_eq_self₀, or_iff_left (HostParam.SlopeTestRemainingChoices.GaussRoot.ne_zero hq hα), Int.cast_eq_one]

private theorem trace_iff {K : Type} [Field K] {n : ℕ} (hn : n ≠ 0) {η : K} (hη : IsPrimitiveRoot η n) (a : ℕ) :
    η ^ a + (η ^ a)⁻¹ = η + η⁻¹ ↔ (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) := by
  have h0 : η ≠ 0 := hη.ne_zero hn
  have h1 : η ^ a ≠ 0 := pow_ne_zero _ h0
  have hfin : IsOfFinOrder η := hη.isOfFinOrder hn
  have e1 : a ≡ 1 [MOD n] ↔ η ^ a = η := by
    rw [hη.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
  have e2 : a + 1 ≡ 0 [MOD n] ↔ η ^ a * η = 1 := by
    rw [hη.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_zero, pow_succ]
  rw [e1, e2]
  generalize η ^ a = y at h1
  have key : y + y⁻¹ - (η + η⁻¹) = (y - η) * (y * η - 1) / (y * η) := by
    field_simp
    ring
  rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left (mul_ne_zero h1 h0), mul_eq_zero, sub_eq_zero,
    sub_eq_zero]

private theorem exists_pow {N : ℕ} [NeZero N] {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) : ∃ a : ℕ, τ ζ = ζ ^ a := by
  obtain ⟨i, -, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  exact ⟨i, h.symm⟩

private theorem mem_fix {E K : Type} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] (j : E →ₐ[ℚ] K)
    (τ : K ≃ₐ[ℚ] K) : τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ x : E, τ (j x) = j x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

private theorem range_le {M L : Type} [Field M] [Field L] [Algebra ℚ M] [Algebra ℚ L] [Normal ℚ M]
    (g₁ g₂ : M →ₐ[ℚ] L) (x : M) : ∃ y : M, g₂ y = g₁ x := by
  letI : Algebra M L := g₂.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ M L := IsScalarTower.of_algebraMap_eq fun r => (g₂.commutes r).symm
  exact ⟨g₁.restrictNormal M x, g₁.restrictNormal_commutes M x⟩

private theorem exists_lift {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ L]
    (f : K →ₐ[ℚ] L) (τ : K ≃ₐ[ℚ] K) : ∃ σ : L ≃ₐ[ℚ] L, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨τ.liftNormal L, fun x => τ.liftNormal_commutes L x⟩

private theorem exists_res {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ K]
    (f : K →ₐ[ℚ] L) (σ : L ≃ₐ[ℚ] L) : ∃ τ : K ≃ₐ[ℚ] K, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨σ.restrictNormal K, fun x => (σ.restrictNormal_commutes K x).symm⟩

private theorem indep (A : AbF) {M : Type} [Field M] [NumberField M] (hM : IsAbField A M) {N : ℕ} [NeZero N]
    (hm : A.m ∣ N) (i : M →ₐ[ℚ] CyclotomicField N ℚ) {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ) (hτ : τ ζ = ζ ^ a) :
    (∀ x : M, τ (i x) = i x) ↔ A.ker a := by
  obtain ⟨N', hN', j, ζ', hm', hζ', H⟩ := hM
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  haveI : IsAbelianGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isAbelianGalois {N'} ℚ _
  haveI : IsAbelianGalois ℚ M := IsAbelianGalois.of_algHom j
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    first
      | exact @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _
      | convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _
  let f : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f' : CyclotomicField N' ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨σ, hσ⟩ := exists_lift f τ
  obtain ⟨τ', hσ'⟩ := exists_res f' σ
  obtain ⟨b, hb⟩ := exists_pow hζ' τ'
  obtain ⟨k, hk⟩ := id hm
  obtain ⟨k', hk'⟩ := id hm'
  have hω : IsPrimitiveRoot (f (ζ ^ k)) A.m :=
    (hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])).map_of_injective f.injective
  have hω' : IsPrimitiveRoot (f' (ζ' ^ k')) A.m :=
    (hζ'.pow (NeZero.pos N') (by rw [hk', mul_comm])).map_of_injective f'.injective
  have h1 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ a := by
    rw [hσ, map_pow τ, hτ, pow_right_comm, map_pow f]
  have h2 : σ (f' (ζ' ^ k')) = f' (ζ' ^ k') ^ b := by
    rw [hσ', map_pow τ', hb, pow_right_comm, map_pow f']
  have h3 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ b :=
    act_root hω' (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) h2 hω.pow_eq_one
  have hab : a ≡ b [MOD A.m] := by
    have := ((hω.isOfFinOrder A.pos.ne').pow_eq_pow_iff_modEq).1 (h1.symm.trans h3)
    rwa [← hω.eq_orderOf] at this
  have h4 : A.ker b ↔ A.ker a := ⟨ker_congr A hab, ker_congr A hab.symm⟩
  rw [← h4, ← H τ' b hb]
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := range_le (f'.comp j) (f.comp i) x
    have hy' : f (i y) = f' (j x) := hy
    apply f'.injective
    show f' (τ' (j x)) = f' (j x)
    rw [← hσ', ← hy', hσ, h]
  · intro h x
    obtain ⟨y, hy⟩ := range_le (f.comp i) (f'.comp j) x
    have hy' : f' (j y) = f (i x) := hy
    apply f.injective
    show f (τ (i x)) = f (i x)
    rw [← hσ, ← hy', hσ', h]

private theorem core (A : AbF) {M : Type} [Field M] [NumberField M] (hM : IsAbField A M)
    {e q d : ℕ} (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {N : ℕ} [NeZero N] (i : M →ₐ[ℚ] CyclotomicField N ℚ)
    {ζ η α β : CyclotomicField N ℚ} (h2 : 2 ^ (e + 2) ∣ N) (hm : A.m ∣ N) (hqN : q ∣ N)
    (hdN : d ∣ N) (hζ : IsPrimitiveRoot ζ N) (hη : IsPrimitiveRoot η (2 ^ (e + 2)))
    (hα : α ^ 2 = -(q : CyclotomicField N ℚ)) (hβ : β ^ 2 = -(d : CyclotomicField N ℚ))
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ) (hτ : τ ζ = ζ ^ a) :
    τ ∈ (IntermediateField.adjoin ℚ {α, β, η + η⁻¹} ⊔ i.fieldRange).fixingSubgroup ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1 := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  have hτ' : (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ) ζ = ζ ^ a := hτ
  have e1 : τ α = α ↔ jacobiSym (a : ℤ) q = 1 := sqrt_iff hζ _ hτ' hq hq4 hqN hα
  have e2 : τ β = β ↔ jacobiSym (a : ℤ) d = 1 := sqrt_iff hζ _ hτ' hd hd4 hdN hβ
  have hηa : τ η = η ^ a := act_root hζ _ hτ' ((hη.pow_eq_one_iff_dvd N).2 h2)
  have e3 : τ (η + η⁻¹) = η + η⁻¹ ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
    rw [map_add (f := _), map_inv₀, hηa]
    exact trace_iff (pow_ne_zero _ two_ne_zero) hη a
  have e4 : τ ∈ (IntermediateField.adjoin ℚ {α, β, η + η⁻¹}).fixingSubgroup ↔
      τ α = α ∧ τ β = β ∧ τ (η + η⁻¹) = η + η⁻¹ := by
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
    have hm : ∀ x : CyclotomicField N ℚ, x ∈ IntermediateField.fixedField (Subgroup.zpowers τ) ↔ τ x = x := by
      intro x
      rw [IntermediateField.mem_fixedField_iff]
      refine ⟨fun h => h τ (Subgroup.mem_zpowers τ), fun h f hf => ?_⟩
      have : Subgroup.zpowers τ ≤ MulAction.stabilizer _ x := Subgroup.zpowers_le.2 h
      exact this hf
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, hm]
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, mem_fix,
    e4, e1, e2, e3, indep A hM hm i hζ τ a hτ]
  tauto
end
