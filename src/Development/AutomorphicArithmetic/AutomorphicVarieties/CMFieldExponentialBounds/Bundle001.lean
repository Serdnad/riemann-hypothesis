module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
public import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem lift_coprime {n N b : ℕ} [NeZero N] (h : n ∣ N) (hb : b.Coprime n) :
    ∃ a : ℕ, a.Coprime N ∧ a ≡ b [MOD n] := by
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime b hb)
  refine ⟨(v : ZMod N).val, ZMod.val_coe_unit_coprime v, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ← ZMod.unitsMap_val h v, hv]
  simp

private theorem exists_aut {N a : ℕ} [NeZero N] (ha : a.Coprime N) :
    ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ, ∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  set ζ := IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)
  set τ := (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).symm (ZMod.unitOfCoprime a ha) with hτdef
  refine ⟨τ, ?_⟩
  have hτ : hζ.autToPow ℚ τ = ZMod.unitOfCoprime a ha :=
    (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).apply_symm_apply (ZMod.unitOfCoprime a ha)
  have hτζ : τ ζ = ζ ^ a := by
    rw [← hζ.autToPow_spec ℚ τ, hτ, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  intro x hx
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hτζ, ← pow_mul, ← pow_mul, mul_comm]

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩


theorem UpperTheory.V.abelianField_hasMu_iff_exists_primitiveRoot :
    ∀ (A : AbF) (l : ℕ), l.Prime → l ≠ 2 → ∀ (L : Type) [Field L] [NumberField L], IsAbField A L →
      (A.HasMu l ↔ ∃ z : L, IsPrimitiveRoot z l) := by
  intro A l hl hl2 L _ _ hL
  obtain ⟨N, hN, j, ζ, hdvd, hζ, hfix⟩ := hL
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  have hker1 : A.ker 1 := ⟨1, A.H.one_mem, by simp⟩
  have haut : ∀ a : ℕ, a.Coprime N → ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      (∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a) ∧ ((∀ y : L, τ (j y) = j y) ↔ A.ker a) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := exists_aut ha
    exact ⟨τ, hτ, hfix τ a (hτ ζ hζ.pow_eq_one)⟩
  constructor
  · rintro ⟨hlm, hmu⟩
    have hlN : l ∣ N := hlm.trans hdvd
    have hz : IsPrimitiveRoot (ζ ^ (N / l)) l :=
      IsPrimitiveRoot.pow (NeZero.pos N) hζ (by rw [Nat.div_mul_cancel hlN])
    have hord : orderOf (ζ ^ (N / l)) = l := hz.eq_orderOf.symm
    have hfin : IsOfFinOrder (ζ ^ (N / l)) := isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hz.pow_eq_one⟩
    have hmem : ζ ^ (N / l) ∈ j.fieldRange := by
      haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
      rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have hτj : ∀ y : L, τ (j y) = j y := fun y => hτ _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
      have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
      obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hτN
      have hka : A.ker a := (hfix τ a ha.symm).1 hτj
      have ha1 : a ≡ 1 [MOD l] := hmu a hka
      have hpow : (ζ ^ (N / l)) ^ a = (ζ ^ (N / l)) ^ 1 := by
        rw [hfin.pow_eq_pow_iff_modEq, hord]
        exact ha1
      rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
    obtain ⟨w, hw⟩ : ∃ w : L, j w = ζ ^ (N / l) := AlgHom.mem_fieldRange.1 hmem
    refine ⟨w, ?_⟩
    rw [← hw] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).1 hz
  · rintro ⟨z, hz⟩
    have hw : IsPrimitiveRoot (j z) l := hz.map_of_injective j.toRingHom.injective
    have hord : orderOf (j z) = l := hw.eq_orderOf.symm
    have hfin : IsOfFinOrder (j z) := isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hw.pow_eq_one⟩
    have hlN : l ∣ N := by
      by_contra hnd
      have hcop : Nat.Coprime N l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      have hirr := Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos (NeZero.pos N) hl.pos)
      have h1 := IsPrimitiveRoot.lcm_totient_le_finrank hζ hw hirr
      rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)),
        Nat.Coprime.lcm_eq_mul hcop, Nat.totient_mul hcop, Nat.totient_prime hl] at h1
      have hpos : 0 < N.totient := Nat.totient_pos.2 (NeZero.pos N)
      have h2 : 2 ≤ l - 1 := by omega
      nlinarith
    have hwN : (j z) ^ N = 1 := by
      obtain ⟨k, hk⟩ := hlN
      have e1 : (j z) ^ N = ((j z) ^ l) ^ k := by rw [← pow_mul, ← hk]
      rw [e1, hw.pow_eq_one, one_pow]
    have key : ∀ a : ℕ, a.Coprime N → A.ker a → a ≡ 1 [MOD l] := by
      intro a ha hka
      obtain ⟨τ, hτ, hiff⟩ := haut a ha
      have h1 := hiff.2 hka z
      rw [hτ _ hwN] at h1
      have h2 : (j z) ^ a = (j z) ^ 1 := by rw [pow_one]; exact h1
      rw [hfin.pow_eq_pow_iff_modEq, hord] at h2
      exact h2
    have hlm : l ∣ A.m := by
      by_contra hnd
      have hcop : Nat.Coprime A.m l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop 1 2
      have hbm : Nat.Coprime b A.m := by
        unfold Nat.Coprime
        rw [hb1.gcd_eq, Nat.gcd_one_left]
      have h2l : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm hl2)
      have hbl : Nat.Coprime b l := by
        unfold Nat.Coprime
        rw [hb2.gcd_eq]
        exact h2l
      have hbcop : Nat.Coprime b (A.m * l) := Nat.Coprime.mul_right hbm hbl
      have hmlN : A.m * l ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd hlN
      obtain ⟨a, ha, hab⟩ := lift_coprime hmlN hbcop
      have ham : a ≡ 1 [MOD A.m] := (Nat.ModEq.of_mul_right l hab).trans hb1
      have hal : a ≡ 2 [MOD l] := (Nat.ModEq.of_mul_left A.m hab).trans hb2
      have hka : A.ker a := ker_congr A ham hker1
      have h21 : 2 ≡ 1 [MOD l] := hal.symm.trans (key a ha hka)
      unfold Nat.ModEq at h21
      rw [Nat.mod_eq_of_lt (by omega : 2 < l), Nat.mod_eq_of_lt (by omega : 1 < l)] at h21
      omega
    refine ⟨hlm, ?_⟩
    intro a hka
    have hacop : a.Coprime A.m := by
      obtain ⟨u, -, hu⟩ := hka
      exact (ZMod.isUnit_iff_coprime a A.m).1 ⟨u, hu⟩
    obtain ⟨a', ha', ha'a⟩ := lift_coprime hdvd hacop
    have hka' := ker_congr A ha'a hka
    exact (Nat.ModEq.of_dvd hlm ha'a).symm.trans (key a' ha' hka')
end

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

open Polynomial in
private theorem finrank_quadratic_splitting_field (p : ℕ) (hp : 0 < p) (L : Type) [Field L] [Algebra ℚ L]
    [h : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Module.finrank ℚ L = 2 := by
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hdeg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hnoroot : ∀ x : ℚ, ¬ f.IsRoot x := by
    intro x hx
    rw [hf] at hx
    simp [Polynomial.IsRoot] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible f :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hnoroot
  have hspl := IsSplittingField.splits L f
  have hdeg0 : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]
    decide
  obtain ⟨α, hα⟩ := hspl.exists_eval_eq_zero hdeg0
  have haeval : aeval α f = 0 := by
    rw [aeval_def, ← eval_map]
    exact hα
  have hmin : f = minpoly ℚ α := minpoly.eq_of_irreducible_of_monic hirr haeval hmon
  have hint : IsIntegral ℚ α := ⟨f, hmon, by rw [← aeval_def]; exact haeval⟩
  have hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  have htop : IntermediateField.adjoin ℚ {α} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin ℚ (f.rootSet L) := by
      rw [IsSplittingField.adjoin_rootSet L f]
      trivial
    have hle : Algebra.adjoin ℚ (f.rootSet L) ≤ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by
      apply Algebra.adjoin_le
      intro β hβ
      rw [Polynomial.mem_rootSet] at hβ
      have e1 := hβ.2
      have e2 := haeval
      rw [hf] at e1 e2
      simp at e1 e2
      have : (β - α) * (β + α) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp this with h | h
      · have hb : β = α := by linear_combination h
        rw [hb]
        exact IntermediateField.mem_adjoin_simple_self ℚ α
      · have hb : β = -α := by linear_combination h
        rw [hb]
        exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ α)
    exact hle hy
  rw [← IntermediateField.finrank_top', ← htop, hfin]

open Polynomial in
private theorem finrank_kstar (p : ℕ) (hp : 0 < p) : Module.finrank ℚ (Kstar p) = 2 := by
  show Module.finrank ℚ (SplittingField (X ^ 2 + C (p : ℚ))) = 2
  exact @finrank_quadratic_splitting_field p hp _ _ _ (Polynomial.IsSplittingField.splittingField _)

theorem UpperTheory.V.pK_pOne_prime_conditions :
    ∀ ψ : PChar, ((pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N) ∧
      ((pOne ψ).Prime ∧ pOne ψ ≡ 1 [MOD ordCompl[2] (ordC ψ)] ∧ (pOne ψ).Coprime (2 * ψ.N * pK ψ)) ∧ Module.finrank ℚ (Kstar (pK ψ)) = 2 := by
  intro ψ
  have hN : ψ.N ≠ 0 := NeZero.ne _
  have hne1 : {p | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime ψ.N}.Nonempty := by
    obtain ⟨p, hpgt, hp, hpm⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 3) (by decide) (ψ.N + 7)
    refine ⟨p, hp, ?_, by omega, ?_⟩
    · have h3 : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hpm
      rw [ZMod.natCast_eq_natCast_iff'] at h3
      simpa using h3
    · rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
      omega
  have h1 : (pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N := Nat.sInf_mem hne1
  have hord : ordC ψ ≠ 0 := (orderOf_pos _).ne'
  have hk : ordC ψ / 2 ^ (ordC ψ).factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hord).ne'
  have hm : 0 < 2 * ψ.N * pK ψ := by
    have := h1.1.pos
    have := Nat.pos_of_ne_zero hN
    positivity
  have hne2 : {p | Nat.Prime p ∧ p ≡ 1 [MOD ordC ψ / 2 ^ (ordC ψ).factorization 2] ∧
      p.Coprime (2 * ψ.N * pK ψ)}.Nonempty := by
    obtain ⟨p, hp, hpgt, hpm⟩ := Nat.exists_prime_gt_modEq_one (2 * ψ.N * pK ψ) hk
    refine ⟨p, hp, hpm, ?_⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd hm h
    omega
  have h2 := Nat.sInf_mem hne2
  exact ⟨h1, h2, finrank_kstar _ h1.1.pos⟩
end

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.minusBound_le_exp_of_log_le :
    ∀ (C : ℝ) (o : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (n N t : ℕ) (W : ℝ), 1 ≤ N → 1 ≤ t → n ≤ N → Real.log ((N : ℝ) * t) ≤ 2 * W →
      minusBound C o n N t ≤ K * Real.exp (8 * W) := by
  intro C o
  refine ⟨3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3, by positivity, ?_⟩
  intro n N t W hN ht hn hW
  unfold minusBound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * t := one_le_mul_of_one_le_of_one_le hN1 ht1
  have hXpos : 0 < (N : ℝ) * t := by linarith
  have hXe : (N : ℝ) * t ≤ Real.exp (2 * W) := by
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr hW
  have hX4 : ((N : ℝ) * t) ^ 4 ≤ Real.exp (8 * W) := by
    have e : Real.exp (8 * W) = Real.exp (2 * W) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hXpos.le hXe 4
  have hnt : (n : ℝ) * t ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_right hn' (by positivity)
  have htX : (t : ℝ) ≤ (N : ℝ) * t := by nlinarith
  have hlog : Real.log ((t : ℝ) * N) ≤ (N : ℝ) * t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * N by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((t : ℝ) * N) := Real.log_nonneg (by linarith)
  have h1 : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) ≤ 3 * ((N : ℝ) * t) ^ 4 := by
    have h3 : (n : ℝ) * t * t * Real.log (t * N) ≤ ((N : ℝ) * t) ^ 3 := by
      calc (n : ℝ) * t * t * Real.log (t * N)
          ≤ ((N : ℝ) * t) * ((N : ℝ) * t) * ((N : ℝ) * t) :=
            mul_le_mul (mul_le_mul hnt htX (by positivity) (by positivity)) hlog hlog0 (by positivity)
        _ = ((N : ℝ) * t) ^ 3 := by ring
    have h34 : ((N : ℝ) * t) ^ 3 ≤ ((N : ℝ) * t) ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
    have e : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) = 3 * ((n : ℝ) * t * t * Real.log (t * N)) := by ring
    rw [e]
    linarith
  have h2 : ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ (∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hl1 : (1 : ℝ) ≤ l := by
      have := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
      exact_mod_cast this.one_lt.le
    have hge : (1 : ℝ) ≤ t * l * N :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht1 hl1) hN1
    have hlg : Real.log ((t : ℝ) * l * N) ≤ l * ((N : ℝ) * t) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * l * N by linarith)
      linarith
    have hlg0 : 0 ≤ Real.log ((t : ℝ) * l * N) := Real.log_nonneg hge
    have hsq : Real.log ((t : ℝ) * l * N) ^ 2 ≤ (l * ((N : ℝ) * t)) ^ 2 := pow_le_pow_left₀ hlg0 hlg 2
    have hnt2 : ((n : ℝ) * t) ^ 2 ≤ ((N : ℝ) * t) ^ 2 := pow_le_pow_left₀ (by positivity) hnt 2
    calc (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
        = (l : ℝ) * ((n : ℝ) * t) ^ 2 * Real.log (t * l * N) ^ 2 := by ring
      _ ≤ (l : ℝ) * ((N : ℝ) * t) ^ 2 * (l * ((N : ℝ) * t)) ^ 2 := by gcongr
      _ = (l : ℝ) ^ 3 * ((N : ℝ) * t) ^ 4 := by ring
  have hS0 : 0 ≤ ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2 :=
    Finset.sum_nonneg (fun l _ => by positivity)
  have hK0 : 0 ≤ 3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3 := by positivity
  calc 3 * (n : ℝ) * t ^ 2 * Real.log (t * N)
        + C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ 3 * ((N : ℝ) * t) ^ 4 + |C| * ((∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4) :=
        add_le_add h1 ((mul_le_mul_of_nonneg_right (le_abs_self C) hS0).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    _ = (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by ring
    _ ≤ (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * Real.exp (8 * W) :=
        mul_le_mul_of_nonneg_left hX4 hK0
end

section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V
open Polynomial

private theorem layerex_up {K : Type} [Field K] {l m : ℕ} (hl : l.Prime) {b : K}
    (h : IsPrimitiveRoot (b ^ l) (l ^ (m + 1))) : IsPrimitiveRoot b (l ^ (m + 2)) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : ¬ b ^ (l ^ (m + 1)) = 1 := by
    intro e
    have : (b ^ l) ^ (l ^ m) = 1 := by rw [← pow_mul, ← pow_succ']; exact e
    exact h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
      (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this
  have h2 : b ^ (l ^ (m + 1 + 1)) = 1 := by
    rw [pow_succ' l (m + 1), pow_mul]; exact h.pow_eq_one
  have h3 := orderOf_eq_prime_pow h1 h2
  have := IsPrimitiveRoot.orderOf b
  rwa [h3] at this

private theorem layerex_max (K : Type) [Field K] [NumberField K] {l k : ℕ} (hl : l.Prime)
    (h : ∃ z : K, IsPrimitiveRoot z (l ^ (k + 1))) :
    ∃ m, k ≤ m ∧ (∃ z : K, IsPrimitiveRoot z (l ^ (m + 1))) ∧
      ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2)) := by
  by_contra hc
  push Not at hc
  have key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1)) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact hc (k + n) (by omega) ih
  obtain ⟨z, hz⟩ := key (Module.finrank ℚ K)
  have hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1)) := by
    rw [Nat.lcm_self]; exact pow_pos hl.pos _
  have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hl] at h1
  have h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K) := Nat.lt_pow_self hl.one_lt
  have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
  have h4 := Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3
  omega

private theorem layerex_step (K : Type) [Field K] [NumberField K] {l m : ℕ} (hl : l.Prime)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (m + 1))) (hn : ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2))) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K'),
      IsCyclotomicExtension {l ^ (m + 2)} K K' ∧ Module.finrank K K' = l := by
  have hirr : Irreducible (X ^ l - C z : K[X]) :=
    X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, layerex_up hl (hb ▸ hz)⟩)
  haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite
  haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2)) := by
    apply layerex_up hl
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective
  refine ⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have : x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_mono ?_ this
    rintro _ rfl
    exact hr.pow_eq_one
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]

theorem UpperTheory.V.exists_cyclotomic_layer_of_primitiveRoot :
    ∀ (l j : ℕ), l.Prime → l ≠ 2 → ∀ (L : Type) [Field L] [NumberField L], (∃ z : L, IsPrimitiveRoot z l) →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), IsLayer l j L L' := by
  intro l j hl _ L _ _ hz
  have key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'),
      (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j := by
    induction j with
    | zero =>
      refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩
      haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, ⟨k, hk⟩, hd⟩ := ih
      obtain ⟨m, hkm, ⟨z, hz⟩, hn⟩ := layerex_max K (k := k) hl
        (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))
      obtain ⟨K', _, _, _, hc, hd'⟩ := layerex_step K hl hz hn
      letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
      haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine ⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩
      · haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
        have h1 := IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective
        rw [Set.union_comm] at h1
        exact (IsCyclotomicExtension.iff_union_of_dvd L K'
          ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1
      · rw [← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]
  obtain ⟨L', _, _, _, ⟨k, hk⟩, hd⟩ := key
  exact ⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩
end
