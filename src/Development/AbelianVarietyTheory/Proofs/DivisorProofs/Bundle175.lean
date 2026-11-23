module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle141
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

section

open GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.AffineCurveNbhd

theorem isNbhd_away_of_add_mul_eq_one (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A')
    (hN : IsNbhd B A' f) (hh : h + algebraMap B A' f * c = 1) : IsNbhd B (Localization.Away h) f := by
  set F := algebraMap B A' f with hF
  have hpow : ∀ m : ℕ, F ∣ h ^ m - 1 := by
    intro m
    have h1 : F ∣ h - 1 := ⟨-c, by linear_combination hh⟩
    have := sub_dvd_pow_sub_pow h 1 m
    rw [one_pow] at this
    exact h1.trans this
  have hL : ∀ b : B, algebraMap B (Localization.Away h) b =
      algebraMap A' (Localization.Away h) (algebraMap B A' b) := fun b =>
    IsScalarTower.algebraMap_apply B A' (Localization.Away h) b
  refine ⟨?_, ?_⟩
  · intro a'
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    rw [← hn] at hs
    obtain ⟨b, hb⟩ := hN.1 x
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨d, hd⟩ := hb
    refine ⟨b, ?_⟩
    rw [Ideal.mem_span_singleton, hL b, hL f]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h |>.exists_right_inv
    have hu1 : algebraMap A' (Localization.Away h) F ∣ u - 1 := by
      refine ⟨algebraMap A' (Localization.Away h) c * u, ?_⟩
      have := congrArg (algebraMap A' (Localization.Away h)) hh
      simp only [map_add (f := _), map_mul, map_one] at this
      linear_combination hu - u * this
    have hun : algebraMap A' (Localization.Away h) F ∣ u ^ n - 1 := by
      have := sub_dvd_pow_sub_pow u 1 n
      rw [one_pow] at this
      exact hu1.trans this
    obtain ⟨e, he⟩ := hun
    have ha' : a' = algebraMap A' (Localization.Away h) x * u ^ n := by
      have : a' * (algebraMap A' (Localization.Away h) h * u) ^ n = a' := by rw [hu, one_pow, mul_one]
      rw [← this, mul_pow, ← mul_assoc, ← map_pow, hs]
    refine ⟨algebraMap A' (Localization.Away h) x * e + algebraMap A' (Localization.Away h) d, ?_⟩
    have hx : algebraMap A' (Localization.Away h) x =
        algebraMap A' (Localization.Away h) (algebraMap B A' b) + algebraMap A' (Localization.Away h) F *
          algebraMap A' (Localization.Away h) d := by
      rw [← map_mul, ← map_add (f := _), ← hd]; ring_nf
    rw [ha']
    linear_combination (algebraMap A' (Localization.Away h) x) * he + hx
  · intro a ha
    rw [Ideal.mem_span_singleton, hL a, hL f] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    have heq : algebraMap A' (Localization.Away h) (algebraMap B A' a * h ^ n) =
        algebraMap A' (Localization.Away h) (F * x) := by
      rw [map_mul, map_mul, hy, ← hs, hn]; ring
    obtain ⟨⟨k, hk⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp heq
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hk
    simp only at hk'
    apply hN.2
    rw [Ideal.mem_span_singleton]
    obtain ⟨g, hg⟩ := hpow (m + n)
    refine ⟨h ^ m * x - g * algebraMap B A' a, ?_⟩
    rw [← hF]
    linear_combination hk' - algebraMap B A' a * hg

end GlobalTheory.AffineCurveNbhd
end

section

open GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.LocDivEtale

open IsLocalRing

theorem span_singleton_eq_maximalIdeal_pow {L : Type} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] (π : L)
    (hπ : maximalIdeal L = Ideal.span {π}) (x : L) (hx : x ≠ 0) :
    ∃ n : ℕ, Ideal.span {x} = maximalIdeal L ^ n := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal L) (maximalIdeal.isMaximal L).ne_top
  have hex : ∃ n, x ∉ maximalIdeal L ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ i, maximalIdeal L ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp
      | succ k => exact h k
    rw [hK] at this; exact this
  obtain ⟨n, hn, hn'⟩ : ∃ n, x ∉ maximalIdeal L ^ (n + 1) ∧ x ∈ maximalIdeal L ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  clear hex
  refine ⟨n, ?_⟩
  rw [hπ, Ideal.span_singleton_pow] at hn' hn ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hn'
  have hyu : IsUnit y := by
    by_contra hy'
    apply hn
    have : y ∈ maximalIdeal L := (mem_maximalIdeal _).2 hy'
    rw [hπ] at this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    rw [Ideal.mem_span_singleton']
    exact ⟨z, by rw [← hy, ← hz]; ring⟩
  rw [← hy]
  exact Ideal.span_singleton_mul_left_unit hyu _

theorem exists_local_uniformizer (B : Type) [CommRing B] [IsDedekindDomain B] (m : Ideal B) [m.IsPrime]
    (hm0 : m ≠ ⊥) : ∃ π ∈ m, ∀ b ∈ m, ∃ t ∉ m, ∃ c : B, t * b = π * c := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime m)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj m.primeCompl ϖ
  simp only at hπt
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨π, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m, ← hπt]
    exact Ideal.mul_mem_right _ _ (hϖ.not_isUnit)
  · intro b hb
    have hb' : algebraMap B (Localization.AtPrime m) b ∈ maximalIdeal (Localization.AtPrime m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m b).2 hb
    rw [hmax] at hb'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb'
    obtain ⟨⟨c, u⟩, hcu⟩ := IsLocalization.surj m.primeCompl z
    simp only at hcu
    have heq : algebraMap B (Localization.AtPrime m) (b * (t * u)) =
        algebraMap B (Localization.AtPrime m) (π * c) := by
      rw [map_mul, map_mul, map_mul, ← hz, ← hπt, ← hcu]; ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists m.primeCompl (Localization.AtPrime m)).1 heq
    refine ⟨w * (t * u), ?_, w * c, ?_⟩
    · exact (m.primeCompl).mul_mem w.2 ((m.primeCompl).mul_mem t.2 u.2)
    · rw [show (w : B) * (t * u) * b = w * (b * (t * u)) by ring, hw]; ring

theorem exists_dvd_mul_pow : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A']
    [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal →
    algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  intro B A' _ _ _ _ _ f hf hN a ha M hM hfM
  classical
  set m : Ideal B := M.comap (algebraMap B A') with hm_def
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hfm : f ∈ m := hfM
  have hm0 : m ≠ ⊥ := by
    intro h; apply hf
    rw [h] at hfm; exact (Submodule.mem_bot _).1 hfm
  obtain ⟨π, hπm, hπ⟩ := exists_local_uniformizer B m hm0
  let L := Localization.AtPrime M
  haveI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing M.primeCompl L inferInstance
  let φ : B →+* L := (algebraMap A' L).comp (algebraMap B A')
  have hmem : ∀ b ∈ m, φ b ∈ Ideal.span {φ π} := by
    intro b hb
    obtain ⟨t, ht, c, htc⟩ := hπ b hb
    have hu : IsUnit (φ t) := IsLocalization.map_units L (⟨algebraMap B A' t, ht⟩ : M.primeCompl)
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, htc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmax : maximalIdeal L = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := hN.1 x
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
      have hbm : b ∈ m := by
        show algebraMap B A' b ∈ M
        have : algebraMap B A' b = x - c * algebraMap B A' f := by rw [hc]; ring
        rw [this]; exact M.sub_mem hx (M.mul_mem_left _ hfM)
      have hx' : x = algebraMap B A' b + c * algebraMap B A' f := by rw [hc]; ring
      show algebraMap A' L x ∈ Ideal.span {φ π}
      rw [hx', map_add (f := _), map_mul]
      exact Ideal.add_mem _ (hmem b hbm) (Ideal.mul_mem_left _ _ (hmem f hfm))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hπm
  have ha0 : algebraMap A' L a ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl L a).1 h
    have : (s : A') = 0 := (mem_nonZeroDivisors_iff.1 ha).2 _ hs
    exact s.2 (this ▸ M.zero_mem)
  obtain ⟨n, hn⟩ := span_singleton_eq_maximalIdeal_pow (φ π) hmax _ ha0
  have hfL : φ f ^ n ∈ Ideal.span {algebraMap A' L a} := by
    rw [hn]; exact Ideal.pow_mem_pow ((IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hfM) n
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hfL
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj M.primeCompl z
  simp only at hys
  have heq : algebraMap A' L (algebraMap B A' f ^ n * s) = algebraMap A' L (y * a) := by
    rw [map_mul, map_mul, map_pow, ← hys]
    show φ f ^ n * _ = _
    rw [← hz]; ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M.primeCompl L).1 heq
  refine ⟨w * s, (M.primeCompl).mul_mem w.2 s.2, n, w * y, ?_⟩
  rw [show (w : A') * s * algebraMap B A' f ^ n = w * (algebraMap B A' f ^ n * s) by ring, hw]; ring

end GlobalTheory.LocDivEtale
end
end

section

open Polynomial

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

theorem hasse_coe (l : ℕ) (f : R[X]) :
    hasse l (f : PowerSeries R) = ((hasseDeriv l f : R[X]) : PowerSeries R) := by
  ext n
  rw [coeff_hasse, Polynomial.coeff_coe, Polynomial.coeff_coe, hasseDeriv_coeff]

theorem coeff_hasse_congr {l n : ℕ} {φ φ' : PowerSeries R}
    (h : ∀ m ≤ n + l, PowerSeries.coeff m φ = PowerSeries.coeff m φ') :
    PowerSeries.coeff n (hasse l φ) = PowerSeries.coeff n (hasse l φ') := by
  rw [coeff_hasse, coeff_hasse, h _ le_rfl]

theorem coeff_mul_congr {n : ℕ} {φ φ' ψ ψ' : PowerSeries R}
    (h₁ : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m φ')
    (h₂ : ∀ m ≤ n, PowerSeries.coeff m ψ = PowerSeries.coeff m ψ') :
    PowerSeries.coeff n (φ * ψ) = PowerSeries.coeff n (φ' * ψ') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h₁ _ (by omega), h₂ _ (by omega)]

theorem hasse_mul (l : ℕ) (φ ψ : PowerSeries R) :
    hasse l (φ * ψ) = ∑ p ∈ Finset.range (l + 1), hasse p φ * hasse (l - p) ψ := by
  ext n
  set M := n + l + 1 with hM
  set f : R[X] := PowerSeries.trunc M φ
  set g : R[X] := PowerSeries.trunc M ψ
  have hf : ∀ m < M, PowerSeries.coeff m φ = PowerSeries.coeff m (f : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hg : ∀ m < M, PowerSeries.coeff m ψ = PowerSeries.coeff m (g : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hpoly : hasse l ((f : PowerSeries R) * (g : PowerSeries R)) =
      ∑ p ∈ Finset.range (l + 1), hasse p (f : PowerSeries R) * hasse (l - p) (g : PowerSeries R) := by
    rw [← Polynomial.coe_mul, hasse_coe, hasseDeriv_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => hasseDeriv i f * hasseDeriv j g) l]
    simp only [hasse_coe]

    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul]

  rw [coeff_hasse_congr (φ' := (f : PowerSeries R) * (g : PowerSeries R)), hpoly, map_sum, map_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpl : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    apply coeff_mul_congr
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hf m' (by omega)).symm
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hg m' (by omega)).symm
  · intro m hm
    exact coeff_mul_congr (fun m' hm' => hf m' (by omega)) (fun m' hm' => hg m' (by omega))

end GlobalTheory.PicDiv

namespace GlobalTheory

theorem hasse_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1),
          ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha

  rw [GlobalTheory.PicDiv.hasse_mul, ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul]

end GlobalTheory
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem intertwiner_fixes_of_local_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M)
    (hT : ∀ x v, T (W x v) = W (φ x) (T v)) (hTe : ∀ e, Fixes W A e → T e = e) (P : X →ₗ[R] X)
    (hP : ∀ x y, γ (P x) y = γ x (P y)) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ x, φ (x - P x) = x - P x)
    (m : M) (hm : ∀ a ∈ A, W (P a) m = m) : T m = m := by
  have hsm : ∀ (c : ℂ) e, Fixes W A e → Fixes W A (c • e) := fun c e he a ha => by rw [map_smul, he a ha]
  have key : ∀ {ι : Type} (x : ι → X) (s : Finset ι) (e : ι → M), (∀ i, Fixes W A (e i)) →
      (∀ a ∈ A, W (P a) (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i)) →
      T (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i) := by
    intro ι x s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro e he hfix
      by_cases hall : ∀ i ∈ s, P (x i) ∈ A
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h1 := h.comp (x i - P (x i)) (P (x i)) (e i)
        rw [he i _ (hall i hi), sub_add_cancel] at h1
        have h2 : T (W (x i - P (x i)) (e i)) = W (x i - P (x i)) (e i) := by rw [hT, hφ, hTe _ (he i)]
        rw [h1, map_smul] at h2
        exact smul_right_injective M (h.ne_zero _ _) h2
      · push Not at hall
        obtain ⟨j, hj, hjA⟩ := hall
        rw [hA] at hjA
        push Not at hjA
        obtain ⟨a, ha, hz⟩ := hjA
        have hz' : γ (P a) (x j) ≠ 1 := by
          intro h0
          rw [hP] at h0
          exact hz (h.swap_eq_one h0)
        set z := γ (P a) (x j) with hzdef
        have hact : ∀ i, W (P a) (W (x i) (e i)) = γ (P a) (x i) • W (x i) (e i) := fun i => by
          rw [h.comm, he i _ (hPA a ha)]
        have hsum : (1 - z) • ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s.erase j, W (x i) ((γ (P a) (x i) - z) • e i) := by
          rw [Finset.sum_erase s (by simp [hzdef]), sub_smul, one_smul]
          have h4 : ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) := by

            rw [← hfix a ha, map_sum]
            exact Finset.sum_congr rfl fun i _ => hact i
          calc _ = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) - ∑ i ∈ s, z • W (x i) (e i) := by
                rw [← h4, Finset.smul_sum]
            _ = _ := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ => by rw [map_smul, sub_smul]
        have h3 := ih (s.erase j) (Finset.erase_ssubset hj) (fun i => (γ (P a) (x i) - z) • e i)
          (fun i => hsm _ _ (he i)) (fun b hb => by rw [← hsum, map_smul, hfix b hb])
        rw [← hsum, map_smul] at h3
        exact smul_right_injective M (sub_ne_zero.2 hz'.symm) h3
  have hmem : m ∈ Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} := by rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  choose x e he hge using fun i => (g i).2
  have hm' : m = ∑ i, W (x i) (c i • e i) := by
    rw [← hg]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hge i]
  rw [hm'] at hm ⊢
  exact key x Finset.univ _ (fun i => hsm _ _ (he i)) hm

end GlobalTheory.FinWeil
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.RealWeil

theorem dRho_apply_basis {l : Type} [Fintype l] [DecidableEq l] (w : l ⊕ l → ℝ) (f : Sch l)
    (x : EuclideanSpace ℝ l) :
    dRho w f x = ∑ b, (w (.inl b) : ℂ) * fderiv ℝ f x (EuclideanSpace.single b 1) +
      2 * π * I * (∑ b, (w (.inr b) : ℂ) * (x b : ℂ)) * f x := by
  rw [dRho_apply]
  have h1 : pPart w = ∑ b, w (.inl b) • EuclideanSpace.single b (1 : ℝ) := by
    ext i
    simp [pPart, PiLp.single_apply, Pi.single_apply]
  have h2 : inner ℝ (qPart w) x = ∑ b, w (.inr b) * x b := by
    simp [qPart, PiLp.inner_apply, mul_comm]

  rw [h1, map_sum, h2]
  simp [Complex.real_smul, ofReal_sum]

theorem fderiv_eq_of_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 →
    ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) →
    ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) =
      2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  intro l _ _ s P Q hP hQ hdet f hf a x
  set u : l → ℂ := fun b => fderiv ℝ f x (EuclideanSpace.single b 1) with hu
  set xC : l → ℂ := fun i => (x i : ℂ) with hxC
  have hj : ∀ j, ∑ b, P b j * u b + 2 * π * I * (∑ b, Q b j * xC b) * f x = 0 := by
    intro j
    have e := congrArg (fun g : Sch l => g x) (hf j)
    simp only [SchwartzMap.smul_apply, smul_eq_mul, dRho_apply_basis] at e
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at e
    simp only [hP, hQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [hu, hxC]
    linear_combination e
  have hv : Pᵀ *ᵥ u = -(2 * π * I * f x) • (Qᵀ *ᵥ xC) := by
    funext j
    simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hj j
  have hunit : IsUnit Pᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  have hu' : u = (Pᵀ)⁻¹ *ᵥ (Pᵀ *ᵥ u) := by rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have key : u a = ((Pᵀ)⁻¹ *ᵥ (-(2 * π * I * f x) • (Qᵀ *ᵥ xC))) a := by rw [← hv, ← hu']
  change u a = _
  rw [key, mulVec_smul, mulVec_mulVec, ← transpose_nonsing_inv, ← transpose_mul, Matrix.transpose_neg,
    Matrix.neg_mulVec]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end GlobalTheory.RealWeil
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem integral_rhoFun_mul_conj (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  have h : ∀ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) =
      u (x + pPart w) * starRingEnd ℂ (v (x + pPart w)) := by
    intro x
    have hp : phase w x * starRingEnd ℂ (phase w x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
      simp
    simp only [rhoFun, map_mul]
    calc _ = (phase w x * starRingEnd ℂ (phase w x)) * (u (x + pPart w) * starRingEnd ℂ (v (x + pPart w))) := by
          ring
      _ = _ := by rw [hp, one_mul]
  simp_rw [h]
  exact integral_add_right_eq_self (fun x => u x * starRingEnd ℂ (v x)) (pPart w)

end GlobalTheory.RealWeil
end
