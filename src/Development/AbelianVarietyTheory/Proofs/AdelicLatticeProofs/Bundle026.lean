module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
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
public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem intValuation_map_le_of_map_le {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (P : HeightOneSpectrum R) (h : P.asIdeal.map σ ≤ P.asIdeal) (a : R) :
    P.intValuation (σ a) ≤ P.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have h1 : P.intValuation a = WithZero.exp (-((Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal R)).factors : ℕ) : ℤ) := P.intValuation_if_neg ha
  set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors
  have h2 : a ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem a k).1 h1.le
  rw [h1, P.intValuation_le_pow_iff_mem]
  have h3 : (P.asIdeal ^ k).map σ ≤ P.asIdeal ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h k
  exact h3 (Ideal.mem_map_of_mem σ h2)

theorem valuation_eq_one_of_norm_one_of_not_moved :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E),
      (∀ x, c (c x) = x) → ∀ (u : E) (P : HeightOneSpectrum (𝓞 E)), u * c u = 1 →
        ¬ Moved c P.asIdeal → P.valuation E u = 1 := by
  intro F E _ _ _ _ _ c hc u P hu hP
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (c : E →+* E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = c (a : E) := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [hσ, hσ, hc]
  have hle : P.asIdeal.map σ ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_contra hb
    exact hP ⟨a, ha, σ a, hσ a, hb⟩
  have hint : ∀ a, P.intValuation (σ a) = P.intValuation a := fun a => by
    apply le_antisymm (intValuation_map_le_of_map_le σ P hle a)
    have := intValuation_map_le_of_map_le σ P hle (σ a)
    rwa [hσσ] at this
  have hval : ∀ a : 𝓞 E, P.valuation E (c (a : E)) = P.valuation E (a : E) := fun a => by
    rw [← hσ]
    change P.valuation E (algebraMap (𝓞 E) E (σ a)) = P.valuation E (algebraMap (𝓞 E) E a)
    rw [P.valuation_of_algebraMap, P.valuation_of_algebraMap, hint]
  have hcu : P.valuation E (c u) = P.valuation E u := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hval a) (hval b)
  have h2 : P.valuation E u ^ 2 = 1 := by
    have := congrArg (P.valuation E) hu
    rwa [map_mul, hcu, map_one, ← sq] at this
  exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h2

end GlobalTheory.UnRep
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma pow_apply_ofMul_eq_iterate {M : Type} [CommGroup M] (ψ : AddMonoid.End (Additive M))
    (φ : M →* M) (hψ : ∀ a, ψ (Additive.ofMul a) = Additive.ofMul (φ a)) (n : ℕ) (a : M) :
    (ψ ^ n) (Additive.ofMul a) = Additive.ofMul ((⇑φ)^[n] a) := by
  rw [AddMonoid.End.coe_pow]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hψ]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma cyclotomic_comp_X_add_one_eq (p : ℕ) [Fact p.Prime] :
    ∃ H : ℤ[X], (cyclotomic p ℤ).comp (X + 1) = X ^ (p - 1) + (p : ℤ[X]) * (1 + X * H) := by
  have hp : p.Prime := Fact.out
  have hE := cyclotomic_comp_X_add_one_isEisensteinAt p
  have hm : ((cyclotomic p ℤ).comp (X + 1)).Monic := (cyclotomic.monic p ℤ).comp_X_add_C 1
  have hd : ((cyclotomic p ℤ).comp (X + 1)).natDegree = p - 1 := by
    rw [natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hp, ← C_1, natDegree_X_add_C, mul_one]
  obtain ⟨G, hG⟩ : C (p : ℤ) ∣ (cyclotomic p ℤ).comp (X + 1) - X ^ (p - 1) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy i (p - 1) with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact Ideal.mem_span_singleton.1 (hE.mem (by rwa [hd]))
    · rw [if_pos h, h, ← hd, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, coeff_eq_zero_of_natDegree_lt (by rwa [hd])]
      exact dvd_zero _
  have h0 : G.coeff 0 = 1 := by
    have h : ((cyclotomic p ℤ).comp (X + 1) - X ^ (p - 1)).coeff 0 = (C (p : ℤ) * G).coeff 0 := by
      rw [hG]
    have hp1 : (0 : ℕ) ≠ p - 1 := (Nat.sub_pos_of_lt hp.one_lt).ne
    rw [coeff_sub, coeff_X_pow, if_neg hp1, sub_zero, coeff_C_mul, coeff_zero_eq_eval_zero,
      eval_comp] at h
    simp only [eval_add, eval_X, eval_one, zero_add, eval_one_cyclotomic_prime] at h
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (mul_right_eq_self₀.1 h.symm).resolve_right hpz
  obtain ⟨H, hH⟩ : X ∣ G - 1 := by
    rw [X_dvd_iff, coeff_sub]
    simp [h0]
  refine ⟨H, ?_⟩
  rw [← hH, ← C_eq_natCast]
  linear_combination hG

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma exists_pow_factor_of_aeval_cyclotomic {S : Type*} [Ring S] (p : ℕ) [Fact p.Prime]
    (y : S) (hy : aeval y ((cyclotomic p ℤ).comp (X + 1)) = 0) :
    ∃ W V : S, y ^ (p - 1) = (p : S) * W ∧ y ^ (p - 1) = W * p ∧
      (p : S) = y ^ (p - 1) * V ∧ (p : S) = V * y ^ (p - 1) := by
  obtain ⟨H, hf⟩ := cyclotomic_comp_X_add_one_eq p
  have hg := mul_neg_geom_sum (-(X * H)) (p - 1)
  have h2 : (-(X * H)) ^ (p - 1) = X ^ (p - 1) * (-H) ^ (p - 1) := by rw [← mul_pow, mul_neg]
  have e1 : X ^ (p - 1) = (p : ℤ[X]) * (-(1 + X * H)) + (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination -hf
  have e2 : X ^ (p - 1) = (-(1 + X * H)) * (p : ℤ[X]) + (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination -hf
  have e3 : (p : ℤ[X]) = X ^ (p - 1) * ((p : ℤ[X]) * (-H) ^ (p - 1) -
      ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) +
      (cyclotomic p ℤ).comp (X + 1) * ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i := by
    linear_combination (-(∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i)) * hf +
      (-(p : ℤ[X])) * hg + (p : ℤ[X]) * h2
  have e4 : (p : ℤ[X]) = ((p : ℤ[X]) * (-H) ^ (p - 1) -
      ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) * X ^ (p - 1) +
      (∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) * (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination e3
  refine ⟨aeval (R := ℤ) y (-(1 + X * H) : ℤ[X]),
    aeval (R := ℤ) y ((p : ℤ[X]) * (-H) ^ (p - 1) - ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i),
    ?_, ?_, ?_, ?_⟩
  · have h := congrArg (aeval y) e1
    rwa [map_add, map_mul, map_natCast, hy, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e2
    rwa [map_add, map_mul, map_natCast, hy, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e3
    rwa [map_add, map_mul, map_mul, map_natCast, hy, zero_mul, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e4
    rwa [map_add, map_mul, map_mul, map_natCast, hy, mul_zero, add_zero, map_pow, aeval_X] at h


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.pows_eq_range_dif_pow : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M)
    (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) →
    (∀ a, _root_.GlobalTheory.CNorm.nrm τ p a = 1) →
    _root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧
      ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by
  intro p M _ τ lam hp hlam hN
  haveI : Fact p.Prime := ⟨hp⟩
  let T : AddMonoid.End (Additive M) := MonoidHom.toAdditive τ
  let Y : AddMonoid.End (Additive M) := MonoidHom.toAdditive (lam : M →* M)
  have hYT : Y + 1 = T := by
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, rfl⟩ : ∃ a, Additive.ofMul a = x := ⟨_, ofMul_toMul x⟩
    show Additive.ofMul (lam a) + Additive.ofMul a = Additive.ofMul (τ a)
    rw [hlam, ← ofMul_mul, div_mul_cancel]
  have hT : aeval T (cyclotomic p ℤ) = 0 := by

    rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, rfl⟩ : ∃ a, Additive.ofMul a = x := ⟨_, ofMul_toMul x⟩
    have hs := map_sum (AddMonoidHom.mk' (fun g : AddMonoid.End (Additive M) =>
      g (Additive.ofMul a)) (fun _ _ => rfl)) (fun i => T ^ i) (Finset.range p)
    change (∑ i ∈ Finset.range p, T ^ i) (Additive.ofMul a) =
      ∑ i ∈ Finset.range p, (T ^ i) (Additive.ofMul a) at hs
    rw [hs, Finset.sum_congr rfl fun i _ => pow_apply_ofMul_eq_iterate T τ (fun _ => rfl) i a]
    rw [← ofMul_prod, ← _root_.GlobalTheory.CNorm.nrm_apply, hN, ofMul_one]
    rfl
  have hy : aeval Y ((cyclotomic p ℤ).comp (X + 1)) = 0 := by
    rw [aeval_comp, map_add (f := _), aeval_X, map_one, hYT, hT]
  obtain ⟨W, V, h1, h2, h3, h4⟩ := exists_pow_factor_of_aeval_cyclotomic p Y hy
  have hL : ∀ a, Additive.ofMul ((lam ^ (p - 1) : Monoid.End M) a) =
      (Y ^ (p - 1)) (Additive.ofMul a) := fun a => by
    rw [Monoid.End.coe_pow]
    exact (pow_apply_ofMul_eq_iterate Y lam (fun _ => rfl) _ _).symm
  have hP : ∀ a : M, ((p : AddMonoid.End (Additive M))) (Additive.ofMul a) =
      Additive.ofMul (a ^ p) := fun a => by
    rw [AddMonoid.End.natCast_apply, ofMul_pow]
  have K1 : ∀ a, (lam ^ (p - 1) : Monoid.End M) a = (Additive.toMul (W (Additive.ofMul a))) ^ p :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, h1, ofMul_pow, ofMul_toMul, ← AddMonoid.End.natCast_apply]
      rfl
  have K2 : ∀ a, (lam ^ (p - 1) : Monoid.End M) a = Additive.toMul (W (Additive.ofMul (a ^ p))) :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, h2, ofMul_toMul, ← hP]
      rfl
  have K3 : ∀ a : M, a ^ p = (lam ^ (p - 1) : Monoid.End M) (Additive.toMul (V (Additive.ofMul a))) :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, ofMul_toMul, ← hP, h3]
      rfl
  have K4 : ∀ a : M, a ^ p =
      Additive.toMul (V (Additive.ofMul ((lam ^ (p - 1) : Monoid.End M) a))) := fun a => by
    apply Additive.ofMul.injective
    rw [hL, ofMul_toMul, ← hP, h4]
    rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · ext x
    simp only [_root_.GlobalTheory.CNorm.pows, Subgroup.mem_map, Subgroup.mem_top, true_and,
      powMonoidHom_apply, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (K3 y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨_, (K1 y).symm⟩
  · rw [K2, ha, ofMul_one, map_zero, toMul_zero]
  · rw [K4, ha, ofMul_one, map_zero, toMul_zero]

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (M : Type) [AddCommGroup M]
    [AddGroup.FG M] (p : ℕ) (hp : 0 < p) :
    Nat.card (nsmulAddMonoidHom (α := M) p).ker ≠ 0 ∧
      (nsmulAddMonoidHom (α := M) p).range.index =
        p ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) p).ker := by
  obtain ⟨n, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ e i)) :=
    Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype ℤ ι _).toEquiv.symm
  set D := DirectSum ι fun i => ZMod (q i ^ e i)
  set P := Fin n →₀ ℤ
  have hker : Nat.card (nsmulAddMonoidHom (α := M) p).ker =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(φ x).2, ?_⟩
        invFun := fun y => ⟨φ.symm (0, y), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
      exact congrArg Prod.snd h
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h ⊢
      rw [← map_nsmul, Prod.smul_mk, smul_zero, h, Prod.mk_zero_zero, map_zero]
    · intro x
      apply Subtype.ext
      apply φ.injective
      have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      have h1 : p • (φ x).1 = 0 := congrArg Prod.fst h
      have h2 : (φ x).1 = 0 := (smul_eq_zero.mp h1).resolve_left hp.ne'
      simp only [AddEquiv.apply_symm_apply]
      exact Prod.ext h2.symm rfl
    · intro y
      apply Subtype.ext
      simp
  have hrange : (nsmulAddMonoidHom (α := M) p).range =
      AddSubgroup.comap φ.toAddMonoidHom
        ((nsmulAddMonoidHom (α := P) p).range.prod (nsmulAddMonoidHom (α := D) p).range) := by
    ext x
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_comap,
      AddSubgroup.mem_prod, AddEquiv.coe_toAddMonoidHom]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨(φ y).1, by rw [map_nsmul]; rfl⟩, ⟨(φ y).2, by rw [map_nsmul]; rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨φ.symm (a, b), φ.injective ?_⟩
      rw [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_mk, ha, hb]
  have hindexD : (nsmulAddMonoidHom (α := D) p).range.index =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    haveI : (nsmulAddMonoidHom (α := D) p).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite
    exact AddSubgroup.index_range
  have hrank : Module.finrank ℤ M = n := by
    rw [φ.toIntLinearEquiv.finrank_eq]
    have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ P D)
    rw [LinearMap.range_eq_top.mpr fun x => ⟨(x, 0), rfl⟩, LinearMap.ker_fst, rank_top] at h
    have h0 : Module.rank ℤ (LinearMap.inr ℤ P D).range = 0 := by
      rw [rank_eq_zero_iff]
      rintro ⟨x, y, rfl⟩
      refine ⟨(Nat.card D : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      apply Subtype.ext
      simp only [SetLike.val_smul, LinearMap.coe_inr, Submodule.coe_zero, natCast_zsmul]
      ext
      · simp
      · simpa using card_nsmul_eq_zero' (x := y)
    rw [h0, add_zero, rank_finsupp_self, Cardinal.mk_fin, Cardinal.lift_natCast] at h
    change Module.finrank ℤ (P × D) = n
    rw [Module.finrank, ← h]
    simp
  refine ⟨?_, ?_⟩
  · rw [hker]
    exact Nat.card_pos.ne'
  · rw [hrange, AddSubgroup.index_comap_of_surjective _ φ.surjective, AddSubgroup.index_prod,
      AddSubgroup.index_range_nsmul, Module.finrank_finsupp_self, Fintype.card_fin, hrank,
      hindexD, hker]


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.pIdx_top_of_fg : ∀ (p : ℕ) (G : Type) [CommGroup G] [Group.FG G],
    0 < p →
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) ≠ 0 ∧
      _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
        p ^ Module.finrank ℤ (Additive G) * _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) := by
  intro p G _ _ hp
  obtain ⟨h1, h2⟩ := card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (Additive G) p hp
  have htor : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) =
      Nat.card (nsmulAddMonoidHom (α := Additive G) p).ker := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.ofMul x.1, ?_⟩
        invFun := fun y => ⟨y.1.toMul, Subgroup.mem_top _, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← ofMul_pow, x.2.2, ofMul_one]
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h
      rw [← toMul_nsmul, h, toMul_zero]
  have hidx : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
      (nsmulAddMonoidHom (α := Additive G) p).range.index := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right, ← Subgroup.index_toAddSubgroup]
    congr 1
    ext x
    change Additive.toMul x ∈ Subgroup.map (powMonoidHom p) ⊤ ↔ _
    rw [Subgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, by
        rw [nsmulAddMonoidHom_apply, ← ofMul_pow, ← powMonoidHom_apply, hy, ofMul_toMul]⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, Subgroup.mem_top _, by
        rw [powMonoidHom_apply, ← toMul_nsmul, ← nsmulAddMonoidHom_apply, hy]⟩
  exact ⟨htor ▸ h1, by rw [hidx, htor]; exact h2⟩

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem IsKum.minpoly_eq {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) : minpoly F θ = X ^ p - C δ := by
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime h.prime h.nonpow
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C δ h.prime.ne_zero)).symm
  simp [h.pow]

theorem IsKum.pow_apply {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (k : ℕ) :
    (σ ^ k) θ = algebraMap F E (ζ ^ k) * θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, h.conj, pow_succ', map_mul]
    ring

theorem kummer_galois : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ IsGalois F E ∧ orderOf σ = p ∧ (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) ∧ Nonempty (E ≃ₐ[F] AdjoinRoot (X ^ p - C δ : F[X])) ∧ ∀ (L : Type) [Field L] [Algebra F L] (r : L), r ^ p = algebraMap F L δ → ∃ ψ : E →ₐ[F] L, ψ θ = r := by
  intro p F E _ _ _ _ ζ δ θ σ h
  have hp := h.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero p := ⟨hp0⟩
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime hp h.nonpow
  have hζ : (primitiveRoots p F).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr h.root⟩
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hθ0 : θ ≠ 0 := by
    intro h0
    have h1 := h.pow
    rw [h0, zero_pow hp0, eq_comm, map_eq_zero] at h1
    exact h.nonpow 0 (by rw [zero_pow hp0, h1])
  have hsplit : IsSplittingField F E (X ^ p - C δ) := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot (h.root.map_of_injective hinj) h.pow
    · rw [eq_top_iff, ← h.gen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos δ)]
      simp [h.pow]
  have hfin : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ p - C δ)
  have hrank : Module.finrank F E = p :=
    finrank_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hgal : IsGalois F E := isGalois_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hext : ∀ τ₁ τ₂ : E ≃ₐ[F] E, τ₁ θ = τ₂ θ → τ₁ = τ₂ := by
    intro τ₁ τ₂ hτ
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top h.gen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hτ
  have hσp : σ ^ p = 1 :=
    hext _ _ (by rw [h.pow_apply, h.root.pow_eq_one, map_one, one_mul, AlgEquiv.one_apply])
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hc := h.conj
    rw [h1, AlgEquiv.one_apply] at hc
    have hz : algebraMap F E ζ = 1 := mul_right_cancel₀ hθ0 (by rw [← hc, one_mul])
    exact h.root.ne_one hp.one_lt (hinj (by rw [hz, map_one]))
  have hord : orderOf σ = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime hσp hσ1
  have hall : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ := by
    intro τ
    have hτp : (τ θ) ^ p = algebraMap F E δ := by rw [← map_pow, h.pow, AlgEquiv.commutes]
    have hq : (τ θ / θ) ^ p = 1 := by
      rw [div_pow, hτp, ← h.pow, div_self (pow_ne_zero _ hθ0)]
    obtain ⟨i, -, hi⟩ := (h.root.map_of_injective hinj).eq_pow_of_pow_eq_one hq
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨i, hext _ _ ?_⟩
    rw [zpow_natCast, h.pow_apply, map_pow, hi, div_mul_cancel₀ _ hθ0]
  let e : AdjoinRoot (X ^ p - C δ : F[X]) ≃ₐ[F] E := adjoinRootXPowSubCEquiv hζ hirr h.pow
  refine ⟨hfin, hrank, hgal, hord, hall, ⟨e.symm⟩, ?_⟩
  intro L _ _ r hr
  refine ⟨(AdjoinRoot.liftAlgHom (X ^ p - C δ) (Algebra.ofId F L) r (by simp [hr])).comp
    e.symm.toAlgHom, ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e, adjoinRootXPowSubCEquiv_symm_eq_root,
    AdjoinRoot.liftAlgHom_root]

end GlobalTheory.CNorm
end
