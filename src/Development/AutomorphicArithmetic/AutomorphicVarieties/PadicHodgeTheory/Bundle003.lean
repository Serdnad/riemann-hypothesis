module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg

open MvPowerSeries in
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

section Abstract

variable {O R A : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing A] [Algebra O A]

private def Appr (φ : R →ₐ[O] A) (J : Ideal A) (f : A) : Prop :=
  ∃ (a : R) (e : O), e ≠ 0 ∧ e • f - φ a ∈ J

private theorem appr_zero (φ : R →ₐ[O] A) (J : Ideal A) : Appr φ J 0 :=
  ⟨0, 1, one_ne_zero, by simp⟩

private theorem appr_add {φ : R →ₐ[O] A} {J : Ideal A} {f g : A} (hf : Appr φ J f) (hg : Appr φ J g) :
    Appr φ J (f + g) := by
  obtain ⟨a, e, he, h⟩ := hf
  obtain ⟨b, d, hd, h'⟩ := hg
  refine ⟨d • a + e • b, e * d, mul_ne_zero he hd, ?_⟩
  have : (e * d) • (f + g) - φ (d • a + e • b) =
      algebraMap O A d * (e • f - φ a) + algebraMap O A e * (d • g - φ b) := by
    rw [map_add (f := _), map_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [this]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ h')

private theorem appr_mul {φ : R →ₐ[O] A} {m : Ideal A} {i j : ℕ} {f g : A} (hfm : f ∈ m ^ i) (hgm : g ∈ m ^ j)
    (hf : Appr φ (m ^ (i + 1)) f) (hg : Appr φ (m ^ (j + 1)) g) : Appr φ (m ^ (i + j + 1)) (f * g) := by
  obtain ⟨a, e, he, h⟩ := hf
  obtain ⟨b, d, hd, h'⟩ := hg
  refine ⟨a * b, e * d, mul_ne_zero he hd, ?_⟩
  have hb : φ b ∈ m ^ j := by
    have h1 : φ b = algebraMap O A d * g - (d • g - φ b) := by
      rw [Algebra.smul_def]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hgm) (Ideal.pow_le_pow_right (Nat.le_succ j) h')
  have : (e * d) • (f * g) - φ (a * b) =
      algebraMap O A e * (f * (d • g - φ b)) + (e • f - φ a) * φ b := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul hfm h'
  · rw [add_right_comm, pow_add]
    exact Ideal.mul_mem_mul h hb

private theorem appr_step {φ : R →ₐ[O] A} {m : Ideal A} (h0 : ∀ f, Appr φ (m ^ (0 + 1)) f)
    (h1 : ∀ f ∈ m, Appr φ (m ^ (1 + 1)) f) (N : ℕ) : ∀ f ∈ m ^ N, Appr φ (m ^ (N + 1)) f := by
  induction N with
  | zero => exact fun f _ => h0 f
  | succ N ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => appr_add ha hb)
    exact appr_mul (j := 1) ha (by rwa [pow_one]) (ih a ha) (h1 b hb)

private theorem appr_all {φ : R →ₐ[O] A} {m : Ideal A} (h : ∀ N, ∀ f ∈ m ^ N, Appr φ (m ^ (N + 1)) f)
    (N : ℕ) (f : A) : Appr φ (m ^ N) f := by
  induction N with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | succ N ih =>
    obtain ⟨a, e, he, ha⟩ := ih
    obtain ⟨b, d, hd, hb⟩ := h N _ ha
    refine ⟨d • a + b, d * e, mul_ne_zero hd he, ?_⟩
    have : (d * e) • f - φ (d • a + b) = d • (e • f - φ a) - φ b := by
      rw [map_add (f := _), map_smul]
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [this]
    exact hb

end Abstract

theorem UpperTheory.power_series_approximation_mod_maximal :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O), c ≠ 0 → (∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (f : MvPowerSeries (Fin n) E), ∃ (a : R) (e : O), e ≠ 0 ∧ e • f - φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N := by
  intro O E _ _ _ _ _ R _ _ n φ t c hc ht N f
  have hmem : ∀ g : MvPowerSeries (Fin n) E,
      g ∈ maximalIdeal (MvPowerSeries (Fin n) E) ↔ MvPowerSeries.constantCoeff g = 0 := fun g => by
    simp only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
      not_not]
  have h0 : ∀ g, Appr φ (maximalIdeal (MvPowerSeries (Fin n) E) ^ (0 + 1)) g := by
    intro g
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) (MvPowerSeries.constantCoeff g)
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hy1 : algebraMap O E y ≠ 0 := fun h => hy0 (IsFractionRing.injective O E (by rw [h, map_zero]))
    refine ⟨algebraMap O R x, y, hy0, ?_⟩
    rw [zero_add, pow_one, hmem, AlgHom.commutes, Algebra.smul_def, map_sub, map_mul, ← hxy,
      MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C,
      MvPowerSeries.constantCoeff_C]
    rw [mul_div_cancel₀ _ hy1, sub_self]
  have h1 : ∀ g ∈ maximalIdeal (MvPowerSeries (Fin n) E),
      Appr φ (maximalIdeal (MvPowerSeries (Fin n) E) ^ (1 + 1)) g := by
    intro g hg
    have hs := mem_span_X g ((hmem g).1 hg)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine Finset.sum_induction _ _ (fun a b ha hb => appr_add ha hb) (appr_zero _ _) fun i _ => ?_
    refine appr_mul (i := 0) (j := 1) (by simp) (by rw [pow_one, hmem]; simp) (h0 _) ⟨t i, c, hc, ?_⟩
    have h2 := neg_mem (ht i)
    rwa [neg_sub] at h2
  exact appr_all (appr_step h0 h1) N f
end

section

open IsLocalRing UpperTheory.V.Alg

private def Cg {A : Type} [CommRing A] (I : Ideal A) (k : ℕ) (a b : A) : Prop :=
  b ∈ I ^ k ∧ a - b ∈ I ^ (k + 1)

private theorem Cg.mul {A : Type} [CommRing A] {I : Ideal A} {k l : ℕ} {a b c d : A}
    (h1 : Cg I k a b) (h2 : Cg I l c d) : Cg I (k + l) (a * c) (b * d) := by
  have hc : c ∈ I ^ l := by
    have := (I ^ l).add_mem (Ideal.pow_le_pow_right (Nat.le_succ l) h2.2) h2.1
    simpa using this
  refine ⟨by rw [pow_add]; exact Ideal.mul_mem_mul h1.1 h2.1, ?_⟩
  have e : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · rw [show k + l + 1 = (k + 1) + l by ring, pow_add]
    exact Ideal.mul_mem_mul h1.2 hc
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul h1.1 h2.2

private theorem Cg.refl {A : Type} [CommRing A] (I : Ideal A) (a : A) : Cg I 0 a a :=
  ⟨by simp, by simp⟩

private theorem Cg.pow {A : Type} [CommRing A] {I : Ideal A} {a b : A}
    (h : Cg I 1 a b) (k : ℕ) : Cg I k (a ^ k) (b ^ k) := by
  induction k with
  | zero => simpa using Cg.refl I 1
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem Cg.prod {A ι : Type} [CommRing A] {I : Ideal A} {a b : ι → A}
    (h : ∀ i, Cg I 1 (a i) (b i)) (d : ι → ℕ) (s : Finset ι) :
    Cg I (∑ i ∈ s, d i) (∏ i ∈ s, a i ^ d i) (∏ i ∈ s, b i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cg.refl I 1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

private theorem order_of_mem_pow {σ E : Type} [Field E] (k : ℕ) :
    ∀ f : MvPowerSeries σ E, f ∈ maximalIdeal (MvPowerSeries σ E) ^ k → (k : ℕ∞) ≤ f.order := by
  induction k with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      have h1 : ((1 : ℕ) : ℕ∞) ≤ b.order := by
        refine MvPowerSeries.nat_le_order ?_
        intro d hd
        have hd0 : d = 0 := by
          have : Finsupp.degree d = 0 := by omega
          exact (Finsupp.degree_eq_zero_iff d).1 this
        subst hd0
        rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
          isUnit_iff_ne_zero, not_not] at hb
        simpa using hb
      refine le_trans ?_ MvPowerSeries.le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih a ha) h1
    · intro a b ha hb
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

theorem UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (u : Fin n → MvPowerSeries (Fin n) E) (c : O), c ≠ 0 → (∀ i, u i - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (h : MvPolynomial (Fin n) O), h.IsHomogeneous N → MvPolynomial.aeval u h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) → h = 0 := by
  intro O E _ _ _ _ _ n u c hc hu N h hh hm
  classical
  set I := maximalIdeal (MvPowerSeries (Fin n) E) with hI
  let v : Fin n → MvPowerSeries (Fin n) E := fun i => c • MvPowerSeries.X i
  have hv : ∀ i, Cg I 1 (u i) (v i) := by
    intro i
    refine ⟨?_, hu i⟩
    rw [pow_one]
    have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ I := by
      rw [hI, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    show c • MvPowerSeries.X i ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hX
  have hdeg : ∀ d ∈ h.support, ∑ i, d i = N := by
    intro d hd
    have := hh (MvPolynomial.mem_support_iff.1 hd)
    rw [← this, ← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rfl
  have hdiff : MvPolynomial.aeval u h - MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun d hd => ?_
    rw [← mul_sub]
    refine Ideal.mul_mem_left _ _ ?_
    have := (Cg.prod hv d Finset.univ).2
    rwa [hdeg d hd] at this
  have hvm : MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    have := (I ^ (N + 1)).sub_mem hm hdiff
    simpa using this
  have hval : MvPolynomial.aeval v h =
      ∑ d ∈ h.support, MvPowerSeries.monomial d (algebraMap O E (h.coeff d * c ^ N)) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd => ?_
    have hX : (∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ^ d i)
        = MvPowerSeries.monomial d 1 := by
      have h1 : ((MvPolynomial.monomial d (1 : E) : MvPolynomial (Fin n) E) :
          MvPowerSeries (Fin n) E) = MvPowerSeries.monomial d 1 := MvPolynomial.coe_monomial _ _
      rw [← h1, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp [map_prod]
    simp only [v, Algebra.smul_def, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hdeg d hd, hX, ← mul_assoc, ← map_pow, ← map_mul, MvPowerSeries.algebraMap_apply,
      ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]
    simp
  by_contra hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.2 hne
  have h0 : MvPowerSeries.coeff d (MvPolynomial.aeval v h) = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ _ hvm))
    rw [Finsupp.degree_eq_sum, hdeg d hd]
    exact_mod_cast Nat.lt_succ_self N

  rw [hval, map_sum, Finset.sum_eq_single d] at h0
  · rw [MvPowerSeries.coeff_monomial_same,
      map_eq_zero_iff _ (IsFractionRing.injective O E)] at h0
    exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hd) (pow_ne_zero _ hc) h0
  · intro e _ he
    exact MvPowerSeries.coeff_monomial_ne he.symm _
  · intro h'; exact absurd hd h'
end

section

open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.height_ker_section_le_of_cotangent_generators :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (x : S →ₐ[O] O) (n : ℕ) (t : Fin n → S), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2) → (RingHom.ker x).height ≤ (n : ℕ∞) := by
  classical
  intro O S _ _ _ _ _ x n t ht hx
  set P := RingHom.ker x with hPdef
  haveI hP : P.IsPrime := RingHom.ker_isPrime x
  set L := Localization.AtPrime P
  set T : Ideal L := Ideal.span ((Finset.univ.image (fun i => algebraMap S L (t i)) : Finset L) : Set L) with hT
  have hTm : T ≤ maximalIdeal L := by
    rw [hT, Ideal.span_le]
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (ht i)
  have key : Ideal.map (algebraMap S L) P ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨e, o, he, hmem⟩ := hx a ha
    have hunit : IsUnit (algebraMap S L (algebraMap O S e)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L P]
      intro hin
      apply he
      have : x (algebraMap O S e) = 0 := hin
      simpa using this
    rw [Ideal.mem_comap]
    have h2 : algebraMap S L (e • a - ∑ i, o i • t i) ∈ maximalIdeal L • maximalIdeal L := by
      rw [smul_eq_mul, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_mul, ← pow_two]
      exact Ideal.mem_map_of_mem _ hmem
    have h3 : algebraMap S L (∑ i, o i • t i) ∈ T := by

      rw [map_sum]
      refine Ideal.sum_mem _ (fun i _ => ?_)
      rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      simp
    have h4 : algebraMap S L (algebraMap O S e) * algebraMap S L a ∈ T ⊔ maximalIdeal L • maximalIdeal L := by
      have : algebraMap S L (algebraMap O S e) * algebraMap S L a = algebraMap S L (∑ i, o i • t i) + algebraMap S L (e • a - ∑ i, o i • t i) := by
        rw [← map_mul, ← Algebra.smul_def, ← map_add (f := _)]
        congr 1
        abel
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right h2)
    obtain ⟨u, hu⟩ := hunit
    have : algebraMap S L a = ((u⁻¹ : Lˣ) : L) * (algebraMap S L (algebraMap O S e) * algebraMap S L a) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h4
  have hmT : maximalIdeal L ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rwa [Localization.AtPrime.map_eq_maximalIdeal] at key
  have hmle : maximalIdeal L ≤ T :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hmT
  have heq : T = maximalIdeal L := le_antisymm hTm hmle
  have hmin : maximalIdeal L ∈ T.minimalPrimes := by
    rw [heq]
    exact ⟨⟨inferInstance, le_rfl⟩, fun q hq _ => hq.2⟩
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hPL : P.height = (maximalIdeal L).height := by
    rw [← IsLocalization.height_under P.primeCompl (maximalIdeal L), Localization.AtPrime.under_maximalIdeal]
  rw [hPL]
  refine hh.trans ?_
  have hc : (Finset.univ.image (fun i => algebraMap S L (t i))).card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => algebraMap S L (t i)))
  exact_mod_cast hc
end

section

open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.exists_derivations_dual_to_cotangent_parameters :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → ∃ (n : ℕ) (D : Fin n → (R →ₗ[O] E)) (t : Fin n → R) (c : O), c ≠ 0 ∧ (∀ i a b, D i (a * b) = algebraMap O E (x a) * D i b + algebraMap O E (x b) * D i a) ∧ (∀ i, ∀ a ∈ I, D i a = 0) ∧ (∀ i, x (t i) = 0) ∧ (∀ i j, D j (t i) = if j = i then algebraMap O E c else 0) ∧ ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I := by
  intro O E _ _ _ _ _ R _ _ _ I x hI
  classical
  set p : Ideal R := RingHom.ker x with hp
  have hmem : ∀ a, a ∈ p ↔ x a = 0 := fun a => RingHom.mem_ker
  let J : Ideal R := p ^ 2 ⊔ I
  have hJp : J ≤ p := sup_le (Ideal.pow_le_self two_ne_zero) hI
  let N : Submodule O R := Submodule.span O {(1 : R)} ⊔ J.restrictScalars O
  let f : (R ⧸ N) →ₗ[O] TensorProduct O E (R ⧸ N) := TensorProduct.mk O E (R ⧸ N) 1
  let π : R →ₗ[O] TensorProduct O E (R ⧸ N) := f ∘ₗ N.mkQ
  have hπN : ∀ a ∈ N, π a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero N).2 ha
    simp only [π, LinearMap.comp_apply, this, map_zero]
  have hJN : ∀ a ∈ J, a ∈ N := fun a ha => Submodule.mem_sup_right (by simpa using ha)
  have h1N : (1 : R) ∈ N := Submodule.mem_sup_left (Submodule.subset_span rfl)
  have hsub : ∀ a : R, a - x a • (1 : R) ∈ p := by
    intro a
    rw [hmem]
    simp
  have hder : ∀ a b, π (a * b) = x a • π b + x b • π a := by
    intro a b
    have h1 : (a - x a • (1 : R)) * (b - x b • (1 : R)) ∈ N := by
      apply hJN
      apply Submodule.mem_sup_left
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    have h2 : a * b = (a - x a • (1 : R)) * (b - x b • (1 : R)) - (x a * x b) • (1 : R)
        + (x a • b + x b • a) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [h2, map_add (f := _), hπN _ (N.sub_mem h1 (N.smul_mem _ h1N))]
    simp
  have hker : ∀ a, x a = 0 → π a = 0 → ∃ e : O, e ≠ 0 ∧ e • a ∈ J := by
    intro a ha h
    have h' : f (N.mkQ a) = 0 := h
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) f).1 h'
    refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
    have h3 : (s : O) • a ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N]
      simpa [Submonoid.smul_def] using hs
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hv' : v ∈ J := by simpa using hv
    have hxv : x v = 0 := (hmem v).1 (hJp hv')
    have := congrArg x huv
    simp [hxv, ha] at this
    rw [← huv, this]
    simpa using hv'
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian p)
  have hgp : ∀ i, x (g i) = 0 := fun i => (hmem _).1 (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range (π ∘ g)) = ⊤ := by
    have key : ∀ a ∈ p, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a ha
      rw [← hg] at ha
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha

      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_eq_mul, hder, hgp, zero_smul, add_zero, ← IsScalarTower.algebraMap_smul E]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have key2 : ∀ a, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a
      have := key _ (hsub a)
      rwa [map_sub, hπN _ (N.smul_mem _ h1N), sub_zero] at this
    rw [eq_top_iff]
    rintro v -
    induction v with
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | tmul e q =>
      obtain ⟨a, rfl⟩ := N.mkQ_surjective q
      have : e ⊗ₜ[O] N.mkQ a = e • π a := by
        simp [π, f, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key2 a)
  obtain ⟨κ, a, hainj, hsp, hli⟩ := exists_linearIndependent' E (π ∘ g)
  haveI : Finite κ := Finite.of_injective a hainj
  obtain ⟨n, ⟨ε⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ E (TensorProduct O E (R ⧸ N)) :=
    Module.Basis.mk hli (by rw [hsp, hspan])
  let b := b0.reindex ε
  let t : Fin n → R := fun i => g (a (ε.symm i))
  have hbt : ∀ i, π (t i) = b i := by
    intro i
    simp [b, b0, t]
  refine ⟨n, fun i => ((b.coord i).restrictScalars O) ∘ₗ π, t, 1, one_ne_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro i u v
    rw [LinearMap.comp_apply, hder, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
    rfl
  · intro i u hu
    simp [hπN u (hJN u (Submodule.mem_sup_right hu))]
  · intro i
    exact hgp _
  · intro i j
    simp [hbt, Finsupp.single_apply, eq_comm]
  · intro u hu
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun i => b.repr (π u) i)
    choose o ho using hd
    have h0 : π ((d : O) • u - ∑ i, o i • t i) = 0 := by

      rw [map_sub, map_smul, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (π u), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hbt, ← IsScalarTower.algebraMap_smul E (o i), ho, smul_assoc]
    obtain ⟨e, he, hJ⟩ := hker _ (by simp [hu, t, hgp]) h0
    refine ⟨e * d, fun i => e * o i, mul_ne_zero he (nonZeroDivisors.coe_ne_zero d), ?_⟩
    simpa [smul_sub, Finset.smul_sum, mul_smul] using hJ
end
