module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Ramification
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pDlogCmp : SDlogCmp := by
  intro R _ p hp m n N hm F g w hF hg hw hL
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  set k := min n (min (j + 1 - 1) N) with hk
  have hkn : k ≤ n := by omega
  have hkj : k ≤ j := by omega
  have hkN : k ≤ N := by omega
  set D := PowerSeries.derivative (R := R) with hD
  set W := w ^ p ^ n with hW
  let J : Ideal (PowerSeries R) := Ideal.span {(p : PowerSeries R) ^ k, cyc R p (j + 1)}
  have hpow : ∀ i, k ≤ i → ∀ y : PowerSeries R, (p : PowerSeries R) ^ i * y ∈ J := by
    intro i hi y
    have e : (p : PowerSeries R) ^ i * y = (p : PowerSeries R) ^ k * ((p : PowerSeries R) ^ (i - k) * y) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    exact J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hcyc : ∀ y, cyc R p (j + 1) * y ∈ J := fun y =>
    J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hev : ∀ x ∈ J, ev R p (j + 1) x ∈ Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k} := by
    intro x hx
    have hle : J ≤ (Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k}).comap (ev R p (j + 1)) := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
        exact Ideal.subset_span rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap]
        have h0 : ev R p (j + 1) (cyc R p (j + 1)) = 0 := by
          unfold ev
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [h0]
        exact Ideal.zero_mem _
    exact hle hx
  obtain ⟨a, b, hab⟩ : ∃ a b : PowerSeries R,
      F - g * W = (p : PowerSeries R) ^ N * a + cyc R p (j + 1) * b := by
    unfold LC at hL
    rw [← map_sub] at hL
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hL
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {cyc R p (j + 1)}) c
    have h0 : ev R p (j + 1) (F - g * W - (p : PowerSeries R) ^ N * a) = 0 := by
      have hea : ev R p (j + 1) a = c := by
        unfold ev
        exact ha
      rw [map_sub, ← hc, map_mul, map_pow, map_natCast, hea, mul_comm]
      exact sub_self _
    unfold ev at h0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact ⟨a, b, by linear_combination -hb⟩
  have hEJ : F - g * W ∈ J := by
    rw [hab]
    exact J.add_mem (hpow N hkN a) (hcyc b)
  have hDcyc : D (cyc R p (j + 1)) ∈ J := by
    have hc : cyc R p (j + 1) = ∑ i ∈ Finset.range p, (1 + PowerSeries.X) ^ (p ^ j * i) := by
      unfold cyc
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp.out, Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_mul]

    rw [hc, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz_pow, map_add (f := _), Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      zero_add, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_assoc]
    exact hpow j hkj _
  have hDE : D (F - g * W) ∈ J := by
    rw [hab, map_add (f := _), Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.map_natCast]
    simp only [smul_zero, mul_zero, add_zero, smul_eq_mul]
    exact J.add_mem (hpow N hkN _) (J.add_mem (hcyc _) (J.mul_mem_left _ hDcyc))
  have hDW : D W ∈ J := by
    rw [hW, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]
    exact hpow n hkn _
  have hdd : ∀ x, dd x = (1 + PowerSeries.X) * D x := by
    intro x
    unfold dd
    rfl
  have hFi := Ring.mul_inverse_cancel F hF
  have hgi := Ring.mul_inverse_cancel g hg
  have key : dl F - dl g =
      Ring.inverse F * Ring.inverse g * ((1 + PowerSeries.X) * (D F * g - D g * F)) := by
    unfold dl
    rw [hdd F, hdd g]
    linear_combination (-(1 + PowerSeries.X) * D F * Ring.inverse F) * hgi +
      ((1 + PowerSeries.X) * D g * Ring.inverse g) * hFi
  have hmid : D F * g - D g * F = g * g * D W + g * D (F - g * W) - D g * (F - g * W) := by
    have hDF : D F = D (F - g * W) + g * D W + W * D g := by
      rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hDF]
    ring
  unfold LC
  rw [← map_sub]
  apply hev
  rw [key]
  refine J.mul_mem_left _ (J.mul_mem_left _ ?_)
  rw [hmid]
  exact J.sub_mem (J.add_mem (J.mul_mem_left _ hDW) (J.mul_mem_left _ hDE)) (J.mul_mem_left _ hEJ)

end UpperTheory.Kd.C7
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem exists_natCast_add_mul_of_frobenius_fixed {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime]
    (σ : R ≃+* R) (hpr : Prime (p : R)) (hfrob : ∀ x : R, σ x - x ^ p ∈ Ideal.span {(p : R)})
    (x : R) (hx : σ x = x) : ∃ a : ℕ, ∃ y : R, x = a + p * y ∧ σ y = y := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (mem_nonunits_iff.mpr hpr.not_unit)
  let K := R ⧸ Ideal.span {(p : R)}
  let π : R →+* K := Ideal.Quotient.mk _
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hxx : π x ^ p = π x := by
    have h1 := hfrob x
    rw [hx] at h1
    have h2 : π (x - x ^ p) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
    rw [map_sub, map_pow] at h2
    exact (sub_eq_zero.mp h2).symm
  have hf : Function.Injective f := f.injective
  let q : Polynomial K := Polynomial.X ^ p - Polynomial.X
  have hdeg : q.natDegree = p := by
    have h1 : (Polynomial.X : Polynomial K).natDegree < (Polynomial.X ^ p : Polynomial K).natDegree := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      exact hp.out.one_lt
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, Polynomial.natDegree_X_pow]
  have hq : q ≠ 0 := by
    intro h
    have := hdeg
    rw [h, Polynomial.natDegree_zero] at this
    exact hp.out.ne_zero this.symm
  have hroot : ∀ t : K, t ^ p = t → t ∈ q.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    simp [q, ht]
  have hsub : Finset.univ.image f ⊆ q.roots.toFinset := by
    intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    apply hroot
    rw [← map_pow, ZMod.pow_card]
  have hcard : q.roots.toFinset.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ZMod.card]
    calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' q
      _ = p := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : π x ∈ Finset.univ.image f := heq ▸ hroot _ hxx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
  have hval : π (a.val : R) = π x := by
    rw [map_natCast, ZMod.natCast_val, ← ha]
    rfl
  have hmemI : x - (a.val : R) ∈ Ideal.span {(p : R)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (x - (a.val : R)) = 0
    rw [map_sub, hval, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmemI
  refine ⟨a.val, y, by rw [mul_comm, hy]; ring, ?_⟩
  have h3 : (p : R) * σ y = p * y := by
    have := congrArg σ hy
    rw [map_mul, map_natCast, map_sub, map_natCast, hx] at this
    rw [mul_comm, this, mul_comm, hy]
  exact mul_left_cancel₀ hpr.ne_zero h3

theorem UpperTheory.Kd.C7.pFixAbs :
    UpperTheory.Kd.C7.SFixAbs := by
  intro R _ p _ _ σ hσ x hx
  obtain ⟨hdom, hpr, hcomp, hfrob, -⟩ := hσ
  classical
  haveI := hdom
  haveI := hcomp
  have step : ∀ y : {y : R // σ y = y}, ∃ a : ℕ, ∃ y' : {y : R // σ y = y}, y.1 = a + p * y'.1 := by
    intro y
    obtain ⟨a, y', h1, h2⟩ := exists_natCast_add_mul_of_frobenius_fixed p σ hpr hfrob y.1 y.2
    exact ⟨a, ⟨y', h2⟩, h1⟩
  choose d nx hdn using step
  let seq : ℕ → {y : R // σ y = y} := fun n => Nat.rec ⟨x, hx⟩ (fun _ y => nx y) n
  let s : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, d (seq i) * p ^ i
  have hrep : ∀ n, x = (s n : R) + (p : R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : seq (n + 1) = nx (seq n) := rfl
      rw [ih, hdn (seq n)]
      simp only [s, Finset.sum_range_succ, e]
      push_cast
      ring
  have hdvd : ∀ m k, (p : ℤ) ^ m ∣ ((s (m + k) : ℕ) : ℤ) - (s m : ℤ) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ((s (m + (k + 1)) : ℕ) : ℤ) - s m
          = (((s (m + k)) : ℤ) - s m) + (d (seq (m + k)) : ℤ) * (p : ℤ) ^ (m + k) := by
        simp only [s, ← add_assoc, Finset.sum_range_succ]
        push_cast
        ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ (Nat.le_add_right _ _)) _)
  have hZ : ∀ (a b : ℤ_[p]) (m : ℕ), a ≡ b [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p])]
      ↔ (p : ℤ_[p]) ^ m ∣ a - b := by
    intro a b m
    rw [SModEq.sub_mem, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.smul_eq_mul,
      Ideal.mul_top, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal ℤ_[p]) inferInstance
    (f := fun n => (s n : ℤ_[p])) (by
      intro m n hmn
      rw [hZ]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have h1 := map_dvd (Int.castRingHom ℤ_[p]) (hdvd m k)
      simp only [map_pow, map_sub, map_natCast] at h1
      rw [← dvd_neg, neg_sub]
      exact h1)
  refine ⟨L, ?_⟩
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : R)})]
  intro n
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := (hZ _ _ n).mp (hL n)
  have h2 := congrArg (algebraMap ℤ_[p] R) hc
  rw [RingHom.map_sub, map_natCast, map_mul, map_pow, map_natCast] at h2
  refine ⟨-(algebraMap ℤ_[p] R c + (seq n).1), ?_⟩
  linear_combination (-1 : R) * h2 - hrep n
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pConj : SConj := by
  intro l _ _ Ω _ _ _ A _ c Z hZ m s hs t ht
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hti : t⁻¹ ∈ Ine (F := ℚ) A := inv_mem ht
  have h1I : (1 : G ℚ Ω) ∈ Ine (F := ℚ) A := one_mem _
  refine ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hsI) hti, ?_⟩, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · have h0 : Z m 1 x = 0 := by
      have h := hZ.coc m 1 h1I 1 h1I x
      rw [mul_one, map_one, inv_one, mul_one] at h
      linear_combination -h
    have h2 := hZ.coc m t ht t⁻¹ hti x
    rw [mul_inv_cancel, h0] at h2
    have h3 := hZ.coc m t ht (s * t⁻¹) (mul_mem hsI hti) x
    have h4 := hZ.coc m s hsI t⁻¹ hti (x * (cycMod ℚ Ω l m t)⁻¹)
    rw [hsk, inv_one, mul_one] at h4
    rw [mul_assoc, h3, h4]
    linear_combination -h2

end UpperTheory.Kd.C7
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem unramified_uniformizer_divides {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (π : 𝓞 K) (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p = Ideal.span {π}) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver p]
    (h : Algebra.IsUnramifiedAt (𝓞 K) P) (x : 𝓞 E) (hx : x ∈ P) :
    ∃ t y : 𝓞 E, t ∉ P ∧ t * x = algebraMap (𝓞 K) (𝓞 E) π * y := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 K) p P).1 h).2
  have h3 : algebraMap (𝓞 E) (Localization.AtPrime P) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P x).2 hx
  rw [← h2] at h3
  have h4 : Ideal.map (algebraMap (𝓞 K) (Localization.AtPrime P)) p =
      Ideal.span {algebraMap (𝓞 K) (Localization.AtPrime P) π} := by
    rw [hp, Ideal.map_span, Set.image_singleton]
  rw [h4, Ideal.mem_span_singleton'] at h3
  obtain ⟨z, hz⟩ := h3
  obtain ⟨⟨y, t⟩, hyt⟩ := IsLocalization.surj P.primeCompl z
  refine ⟨t, y, t.2, ?_⟩
  apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  simp only at hyt
  rw [map_mul, map_mul, ← hz, ← hyt, ← IsScalarTower.algebraMap_apply]
  ring

private theorem valuation_le_uniformizer_div {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 E)) (hu : IsPlaceOver A u) (π : 𝓞 E)
    (h : ∀ x ∈ u.asIdeal, ∃ t y : 𝓞 E, t ∉ u.asIdeal ∧ t * x = π * y) (z : E)
    (hz : A.valuation (algebraMap E Ω z) < 1) :
    A.valuation (algebraMap E Ω z) ≤ A.valuation (algebraMap E Ω (π : E)) := by
  have h1 : ∀ s : 𝓞 E, s ∉ u.asIdeal → A.valuation (algebraMap E Ω (s : E)) = 1 := fun s hs =>
    le_antisymm (CompanionTheory.FamInh.val_int_le_one A s) (not_lt.1 ((hu s).not.2 hs))
  obtain ⟨n, d, e | e⟩ := u.exists_primeCompl_mul_eq_or_mul_eq z
  · have e' : z * ((d : 𝓞 E) : E) = (n : E) := e
    have h2 : A.valuation (algebraMap E Ω z) = A.valuation (algebraMap E Ω (n : E)) := by
      rw [← e', map_mul, map_mul, h1 d d.2, mul_one]
    obtain ⟨t, y, ht, e2⟩ := h n ((hu n).1 (h2 ▸ hz))
    have e3 : (t : E) * (n : E) = (π : E) * (y : E) := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) e2
    have h3 := congrArg (fun a : E => A.valuation (algebraMap E Ω a)) e3
    simp only [map_mul] at h3
    rw [h1 t ht, one_mul] at h3
    rw [h2, h3]
    exact mul_le_of_le_one_right' (CompanionTheory.FamInh.val_int_le_one A y)
  · have e' : z * (n : E) = ((d : 𝓞 E) : E) := e
    have h2 := h1 d d.2
    rw [← e', map_mul, map_mul] at h2
    exact absurd h2 ((mul_le_of_le_one_right' (CompanionTheory.FamInh.val_int_le_one A n)).trans_lt hz).ne

private theorem valuation_le_uniformizer_inertia {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hv : IsPlaceOver A v) (π : 𝓞 K)
    (hπ : v.asIdeal = Ideal.span {π}) (x : Ω) (hx : ∀ s ∈ Ine (F := K) A, s x = x) (h1 : A.valuation x < 1) :
    A.valuation x ≤ A.valuation (algebraMap K Ω (π : K)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : IsGalois K Ω := {}
  let M : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)).toIntermediateField
  have hxM : x ∈ M := FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  haveI : IsAlgClosure M Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨w, hw, hwv⟩ := CompanionTheory.FamInh.exists_place_between (L := M) hv
  let E : IntermediateField K M := IntermediateField.fixedField (w.asIdeal.inertia Gal(M/K))
  haveI : NumberField E := NumberField.of_module_finite K E
  have hxE : (⟨x, hxM⟩ : M) ∈ E := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := CompanionTheory.FamInh.exists_lift_ine hw hτ
    apply (algebraMap M Ω).injective
    exact (AlgEquiv.restrictNormal_commutes σ M _).trans (hx σ hσ)
  have hun : Algebra.IsUnramifiedAt (𝓞 K) (w.asIdeal.under (𝓞 E)) :=
    (GroundTheory.ProfCoh.isUnramifiedAt_under_iff_inertia (F := K) (E := E) (M := M) w.asIdeal).2
      fun σ hσ y => (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ hσ
  have hu : IsPlaceOver A (w.under (𝓞 E)) := fun y => by
    have := hw (algebraMap (𝓞 E) (𝓞 M) y)
    exact this
  haveI : (w.asIdeal.under (𝓞 E)).LiesOver v.asIdeal := inferInstance
  have := valuation_le_uniformizer_div A (w.under (𝓞 E)) hu (algebraMap (𝓞 K) (𝓞 E) π)
    (unramified_uniformizer_divides π v.asIdeal hπ (w.asIdeal.under (𝓞 E)) hun) ⟨_, hxE⟩ h1
  exact this

theorem UpperTheory.Kd.C7.inertia_invariant_valuation_uniformizer_bound :
    UpperTheory.Kd.C7.FixedIntegersIsUnitOfNotMemPrimeSpan := by
  intro l hl _ Ω _ _ _ A ⟨v, hv, hlv⟩ x hx
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpr : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have h0 : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
    have := (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm).2 h0
    simpa using this
  have hπ : v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    have hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal (by simpa using hpr.ne_zero)
    exact (hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hlv)).symm
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  by_cases h1 : A.valuation (x : Ω) < 1
  · exfalso
    have h2 := valuation_le_uniformizer_inertia A v hv _ hπ x x.2.2 h1
    have h3 : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [h3] at h2
    have h4 : (x : Ω) / l ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    refine hx (Ideal.mem_span_singleton'.2 ⟨⟨(x : Ω) / l, h4, fun s hs => ?_⟩, Subtype.ext ?_⟩)
    · rw [map_div₀, x.2.2 s hs, map_natCast]
    · push_cast
      exact div_mul_cancel₀ _ hl0
  · have h2 : A.valuation (x : Ω) = 1 := le_antisymm ((A.valuation_le_one_iff _).2 x.2.1) (not_lt.1 h1)
    have h0 : (x : Ω) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      exact zero_ne_one h2
    have h4 : (x : Ω)⁻¹ ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, h2, inv_one]
    refine IsUnit.of_mul_eq_one ⟨(x : Ω)⁻¹, h4, fun s hs => ?_⟩ (Subtype.ext ?_)
    · rw [map_inv₀, x.2.2 s hs]
    · exact mul_inv_cancel₀ h0
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem frobEx_norm {l : ℕ} (hl : l.Prime) {v : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = l := by
  haveI : Fact l.Prime := ⟨hl⟩
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
    apply hmax.eq_of_le
    · intro htop
      apply v.isPrime.ne_top
      exact (Ideal.map_eq_top_of_bijective _ e.bijective).1 htop
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have := Ideal.mem_map_of_mem (e : 𝓞 ℚ →+* ℤ) hv
      simpa using this
  unfold normV
  rw [Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ e hJ).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

theorem UpperTheory.Kd.C7.pFrobEx :
    UpperTheory.Kd.C7.SFrobEx := by
  intro l _ _ Ω _ _ _ A hA
  obtain ⟨v, hv, hlv⟩ := hA
  have hnorm : normV v = l := frobEx_norm Fact.out hlv
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  refine ⟨?_, fun σ _ σ' _ hσ hσ' => inv_mul_mem_Ine_of_isFrob hσ hσ',
    GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hv
  rw [hnorm] at hσ
  obtain ⟨ι, hι, hιu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval (cycZ ℚ Ω l σ)⁻¹
  have hfr : IsFrob A l (σ * ι) := isFrob_mul_of_mem_Ine hσ hι
  refine ⟨σ * ι, hfr.1, hfr, ?_⟩
  unfold cycBar
  rw [MonoidHom.comp_apply, map_mul, hιu, mul_inv_cancel, map_one]
end
