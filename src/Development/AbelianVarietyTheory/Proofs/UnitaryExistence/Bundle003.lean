module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

@[expose] public section

section

namespace GlobalTheory.IntegralNeighbourhoodZero

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

theorem nsmul_integral_mem_nhds_zero (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (RingOfIntegers F) F |
      ∃ a : FiniteAdeleRing (RingOfIntegers F) F,
        (∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F) ∧
          c = M • a} ∈ nhds (0 : FiniteAdeleRing (RingOfIntegers F) F) := by
  obtain ⟨m, hm⟩ : ∃ m : FiniteAdeleRing (RingOfIntegers F) F, m = algebraMap F _ ((M : F)⁻¹) := ⟨_, rfl⟩
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hmM : (M : FiniteAdeleRing (RingOfIntegers F) F) * m = 1 := by
    rw [hm, ← map_natCast (algebraMap F (FiniteAdeleRing (RingOfIntegers F) F)), ← map_mul,
      mul_inv_cancel₀ hMF, map_one]
  have hopen : IsOpen ((fun c => m * c) ⁻¹' {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F}) :=
    (isOpen_integral F).preimage (continuous_const.mul continuous_id)
  have h0 : (0 : FiniteAdeleRing (RingOfIntegers F) F) ∈ (fun c => m * c) ⁻¹'
      {a : FiniteAdeleRing (RingOfIntegers F) F |
        ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} := by
    intro v
    change (m * 0) v ∈ _
    rw [mul_zero]
    exact zero_mem _
  refine Filter.mem_of_superset (hopen.mem_nhds h0) ?_
  intro c hc
  refine ⟨m * c, hc, ?_⟩
  rw [nsmul_eq_mul, ← mul_assoc, hmM, one_mul]

end GlobalTheory.IntegralNeighbourhoodZero
end

section

open IsLocalRing

namespace GlobalTheory

theorem exists_systemOfParameters_insert (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] (a : S) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧
      ringKrullDim S = (n : WithBot ℕ∞) + 1 ∧
      ∃ N : ℕ, maximalIdeal S ^ N ≤ Ideal.span (insert a (Set.range x)) := by
  classical
  have hIle : Ideal.span {a} ≤ maximalIdeal S := (Ideal.span_singleton_le_iff_mem _).mpr ha
  have hIne : Ideal.span {a} ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hIle))
  have : Nontrivial (S ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (S ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (S ⧸ Ideal.span {a}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha0) ha
  obtain ⟨s, hsmin, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ Ideal.span {a}))
  have hht := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S ⧸ Ideal.span {a})
  have hsle : Ideal.span (s : Set (S ⧸ Ideal.span {a})) ≤ maximalIdeal (S ⧸ Ideal.span {a}) :=
    hsmin.1.2
  have hcomap : (maximalIdeal (S ⧸ Ideal.span {a})).comap (Ideal.Quotient.mk (Ideal.span {a})) =
      maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmapeq : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (maximalIdeal S) =
      maximalIdeal (S ⧸ Ideal.span {a}) := by
    rw [← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  let e := s.equivFin
  let x : Fin s.card → S := fun i =>
    (Ideal.Quotient.mk_surjective ((e.symm i : S ⧸ Ideal.span {a}))).choose
  have hx : ∀ i, Ideal.Quotient.mk (Ideal.span {a}) (x i) = e.symm i := fun i =>
    (Ideal.Quotient.mk_surjective _).choose_spec
  have hrange : Ideal.Quotient.mk (Ideal.span {a}) '' Set.range x =
      (s : Set (S ⧸ Ideal.span {a})) := by
    rw [← Set.range_comp]
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      simp only [Function.comp_apply, hx]
      exact (e.symm i).2
    · intro hq
      exact ⟨e ⟨q, hq⟩, by simp [hx]⟩
  refine ⟨s.card, x, fun i => ?_, ?_, ?_⟩
  · rw [← hcomap, Ideal.mem_comap, hx]
    exact hsle (Ideal.subset_span (e.symm i).2)
  · rw [← hdim, ← hht, ← hcard]
    norm_cast
  · have hrad : maximalIdeal (S ⧸ Ideal.span {a}) ≤
        (Ideal.span (s : Set (S ⧸ Ideal.span {a}))).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro p ⟨hsp, hp⟩
      exact hsmin.2 ⟨hp, hsp⟩ (IsLocalRing.le_maximalIdeal hp.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨N, fun y hy => ?_⟩
    have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {a})) hy
    rw [Ideal.map_pow, hmapeq] at h1
    have h2 := hN h1
    rw [← hrange, ← Ideal.map_span] at h2
    obtain ⟨z, hz, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hzy)
    exact Ideal.mem_span_insert.mpr ⟨-c, z, hz, by linear_combination hc⟩

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

private theorem eq_zero_of_forall_mem_pow_of_isAdicComplete {S : Type} [CommRing S] (I : Ideal S)
    (hc : IsAdicComplete I S) (s : S) (h : ∀ n : ℕ, s ∈ I ^ n) : s = 0 := by
  refine hc.toIsHausdorff.haus' s fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact h n

private theorem exists_limit_of_isAdicComplete {S : Type} [CommRing S] (I : Ideal S)
    (hc : IsAdicComplete I S) (f : ℕ → S) (h : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ I ^ a) :
    ∃ L : S, ∀ n, f n - L ∈ I ^ n := by
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' f fun {a b} hab => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact h hab
  refine ⟨L, fun n => ?_⟩
  have := hL n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

private theorem isUnit_of_not_mem_maximalIdeal_of_closed {S : Type} [CommRing S] [IsLocalRing S]
    (Λ : Subring S) (π : Λ) (hπm : (π : S) ∈ maximalIdeal S)
    (hres : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S)
    (hdiv : ∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a)
    (hcl : ∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ)
    (a : Λ) (ha : (a : S) ∉ maximalIdeal S) : IsUnit a := by
  have hu : IsUnit (a : S) := by
    by_contra h
    exact ha ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨t, ht⟩ : ∃ t : S, (a : S) * t = 1 := ⟨((hu.unit⁻¹ : Sˣ) : S), hu.mul_val_inv⟩
  obtain ⟨b, hbΛ, hb⟩ := hres t
  have h1 : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) ∈ maximalIdeal S := by
    have e : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) = (a : S) * (t - b) := by
      push_cast
      rw [mul_sub, ht]
    rw [e]
    exact Ideal.mul_mem_left _ _ hb
  obtain ⟨c, hcd⟩ := hdiv _ h1
  have hab : (a : S) * b = 1 - (π : S) * c := by
    have e := congrArg Subtype.val hcd
    push_cast at e
    linear_combination -e
  have htΛ : t ∈ Λ := by
    apply hcl
    intro n
    refine ⟨(b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i,
      Λ.mul_mem hbΛ (Λ.sum_mem fun i _ => Λ.pow_mem (Λ.mul_mem π.2 c.2) i), ?_⟩
    have g := mul_neg_geom_sum ((π : S) * c) n
    have e : t - (b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i = t * ((π : S) * c) ^ n := by
      linear_combination ((b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * ht
        - t * (∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * hab - t * g
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hπm) n)
  exact isUnit_iff_exists_inv.2 ⟨⟨t, htΛ⟩, Subtype.ext ht⟩

private theorem exists_pow_dvd_of_mem_maximalIdeal_pow {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (Λ : Subring S) (π : Λ) (hπ0 : (π : S) ≠ 0) (hπm : (π : S) ∈ maximalIdeal S)
    (hc : IsAdicComplete (maximalIdeal S) S)
    (hres : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S)
    (hdiv : ∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a)
    (hcl : ∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ)
    (k : ℕ) : ∃ N : ℕ, ∀ a : Λ, (a : S) ∈ maximalIdeal S ^ N → π ^ k ∣ a := by
  induction k with
  | zero => exact ⟨0, fun a _ => by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    have hne : ((π ^ k : Λ) : S) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hπ0
    obtain ⟨M, hM⟩ : ∃ M, ((π ^ k : Λ) : S) ∉ maximalIdeal S ^ M := by
      by_contra h
      push_neg at h
      exact hne (eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ h)
    refine ⟨max N M, fun a ha => ?_⟩
    obtain ⟨u, rfl⟩ := hN a (Ideal.pow_le_pow_right (le_max_left _ _) ha)
    rw [pow_succ]
    refine mul_dvd_mul_left _ ?_
    by_contra hu
    have hunit : IsUnit u := isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl u fun h => hu (hdiv u h)
    apply hM
    have e : π ^ k = (π ^ k * u) * ↑hunit.unit⁻¹ := by
      rw [mul_assoc, hunit.mul_val_inv, mul_one]
    rw [e, Subring.coe_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (le_max_right _ _) ha)

theorem isDVR_of_closed_subring_principal :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (Λ : Subring S) (π : Λ), (π : S) ≠ 0 → (π : S) ∈ maximalIdeal S → IsAdicComplete (maximalIdeal S) S → (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) → (∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a) → (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) → ∃ _ : IsDiscreteValuationRing Λ, maximalIdeal Λ = Ideal.span {π} ∧ IsAdicComplete (maximalIdeal Λ) Λ := by
  intro S _ _ _ Λ π hπ0 hπm hc hres hdiv hcl
  have hunit : ∀ a : Λ, IsUnit a ↔ (a : S) ∉ maximalIdeal S := fun a =>
    ⟨fun h hm => (IsLocalRing.mem_maximalIdeal _).1 hm (h.map Λ.subtype),
      isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl a⟩
  have hsep : ∀ x : Λ, (∀ n : ℕ, π ^ n ∣ x) → x = 0 := by
    intro x hx
    have : (x : S) = 0 := by
      refine eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ fun n => ?_
      obtain ⟨c, hc'⟩ := hx n
      rw [hc', Subring.coe_mul, Subring.coe_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm n)
    exact_mod_cast this
  have hirr : Irreducible π := by
    refine ⟨fun h => (hunit π).1 h hπm, fun ⦃a b⦄ hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨ha, hb⟩ := hne
    rw [hunit, not_not] at ha hb
    obtain ⟨x, rfl⟩ := hdiv a ha
    obtain ⟨y, rfl⟩ := hdiv b hb
    have h0 : π * (1 - π * (x * y)) = 0 := by linear_combination hab
    rcases mul_eq_zero.1 h0 with h | h
    · exact hπ0 (by rw [h]; rfl)
    · exact (hunit π).1 (isUnit_iff_exists_inv.2 ⟨x * y, by linear_combination -h⟩) hπm
  have hfac : ∀ {x : Λ}, x ≠ 0 → ∃ n : ℕ, Associated (π ^ n) x := by
    intro x hx
    have hex : ∃ n, ¬ π ^ n ∣ x := by
      by_contra h
      push_neg at h
      exact hx (hsep x h)
    classical
    obtain ⟨k, hk, hk1⟩ : ∃ k, π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x := by
      have h0 : Nat.find hex ≠ 0 := by
        intro h
        have := Nat.find_spec hex
        rw [h, pow_zero] at this
        exact this (one_dvd x)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      refine ⟨k, not_not.1 (Nat.find_min hex (by omega)), ?_⟩
      rw [← Nat.succ_eq_add_one, ← hk]
      exact Nat.find_spec hex
    obtain ⟨u, rfl⟩ := hk
    have hu : IsUnit u := (hunit u).2 fun hm => hk1 (by
      rw [pow_succ]
      exact mul_dvd_mul_left _ (hdiv u hm))
    exact ⟨k, hu.unit, by rw [hu.unit_spec]⟩
  have hdvr : IsDiscreteValuationRing Λ :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, hfac⟩
  have hmax : maximalIdeal Λ = Ideal.span {π} := by
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not, Ideal.mem_span_singleton]
    refine ⟨hdiv x, fun ⟨c, hc'⟩ => ?_⟩
    rw [hc', Subring.coe_mul]
    exact Ideal.mul_mem_right _ _ hπm
  refine ⟨hdvr, hmax, ?_⟩
  rw [hmax]
  have hmem : ∀ (n : ℕ) (y : Λ), y ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule Λ Λ) ↔ π ^ n ∣ y := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    refine hsep x fun n => ?_
    have := hx n
    rwa [SModEq.sub_mem, sub_zero, hmem] at this
  · intro f hf
    have hfS : ∀ {a b : ℕ}, a ≤ b → (f a : S) - f b ∈ maximalIdeal S ^ a := by
      intro a b hab
      have := hf hab
      rw [SModEq.sub_mem, hmem] at this
      obtain ⟨c, hc'⟩ := this
      have e := congrArg Subtype.val hc'
      push_cast at e
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm a)
    obtain ⟨L, hL⟩ := exists_limit_of_isAdicComplete _ hc (fun n => (f n : S)) hfS
    have hLΛ : L ∈ Λ := hcl L fun n => ⟨f n, (f n).2, by
      rw [← neg_sub]
      exact neg_mem (hL n)⟩
    refine ⟨⟨L, hLΛ⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem]
    obtain ⟨N, hN⟩ := exists_pow_dvd_of_mem_maximalIdeal_pow Λ π hπ0 hπm hc hres hdiv hcl n
    have h1 : π ^ n ∣ f n - f (max n N) := by
      have := hf (le_max_left n N)
      rwa [SModEq.sub_mem, hmem] at this
    have h2 : π ^ n ∣ f (max n N) - ⟨L, hLΛ⟩ := hN _ (by
      push_cast
      exact Ideal.pow_le_pow_right (le_max_right n N) (hL _))
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this

end GlobalTheory
end
