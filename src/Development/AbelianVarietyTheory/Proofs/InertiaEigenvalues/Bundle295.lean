module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValue
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle272
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.FrobIdeal

theorem exists_coords_mem {R ι : Type} [CommRing R] [Fintype ι] (f : R →+* R) (e : ι → R)
    (hspan : ∀ y : R, ∃ z : ι → R, y = ∑ j, e j * f (z j)) (𝔟 : Ideal R) {x : R} (hx : x ∈ 𝔟.map f) :
    ∃ w : ι → R, (∀ j, w j ∈ 𝔟) ∧ x = ∑ j, e j * f (w j) := by
  have key : ∀ a : R, ∃ w : ι → R, (∀ j, w j ∈ 𝔟) ∧ a * x = ∑ j, e j * f (w j) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      intro a
      obtain ⟨z, rfl⟩ := hspan a
      refine ⟨fun j => z j * t, fun j => 𝔟.mul_mem_left _ ht, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
    | zero => exact fun a => ⟨0, fun _ => 𝔟.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      intro a
      obtain ⟨u, hu, h1⟩ := hx a
      obtain ⟨v, hv, h2⟩ := hy a
      refine ⟨u + v, fun j => 𝔟.add_mem (hu j) (hv j), ?_⟩
      rw [mul_add, h1, h2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, map_add (f := _), mul_add]
    | smul c x _ hx =>
      intro a
      obtain ⟨u, hu, h1⟩ := hx (a * c)
      exact ⟨u, hu, by rw [← h1, smul_eq_mul, mul_assoc]⟩
  simpa using key 1

theorem colon_le_map {R ι : Type} [CommRing R] [Fintype ι] (f : R →+* R) (e : ι → R)
    (hfree : ∀ y : R, ∃! z : ι → R, y = ∑ j, e j * f (z j)) (𝔞 𝔟 : Ideal R) (x q : R)
    (hx : f x = x * q) (hq : ∀ g ∈ 𝔞, q * g ∈ 𝔟.map f) {y : R} (hy : x * y ∈ 𝔞) :
    ∃ z : ι → R, (∀ j, x * z j ∈ 𝔟) ∧ y = ∑ j, e j * f (z j) := by
  obtain ⟨z, hz, -⟩ := hfree y
  refine ⟨z, ?_, hz⟩
  obtain ⟨w, hw, h⟩ := exists_coords_mem f e (fun y => (hfree y).exists) 𝔟 (hq _ hy)
  have h2 : q * (x * y) = ∑ j, e j * f (x * z j) := by
    conv_lhs => rw [hz]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hx]; ring
  have h3 : (fun j => x * z j) = w := (hfree _).unique h2 h
  intro j
  have : x * z j = w j := congrFun h3 j
  rw [this]; exact hw j

theorem phi_mem_span (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ϖ : O)
    (hϖ : ϖ ∣ (l : O)) (N : ℕ) (hN : 1 ≤ N) {y : PowerSeries O}
    (hy : y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ N}) :
    phi l O y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ (N + 1)} := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  obtain ⟨r, hr⟩ := Series.phi_X_mod l O
  obtain ⟨t, ht⟩ := hϖ
  have hC : phi l O (PowerSeries.C ϖ) = PowerSeries.C ϖ := (phi l O).commutes ϖ
  have hl : (l : PowerSeries O) = PowerSeries.C ϖ * PowerSeries.C t := by
    rw [← map_mul, ← ht, map_natCast]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (phi l O PowerSeries.X) (PowerSeries.X ^ l) N
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨m, hm⟩ : ∃ m, l * N = m + (N + 1) := ⟨l * N - (N + 1), by
    have : 2 * N ≤ l * N := Nat.mul_le_mul_right N h2
    omega⟩
  rw [← pow_mul, hm, pow_add] at hd
  nth_rewrite 2 [hr] at hd
  rw [hl] at hd
  refine Ideal.mem_span_pair.2 ⟨phi l O a + phi l O b * PowerSeries.C t * r * d,
    phi l O b * PowerSeries.X ^ m, ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, hC]
  linear_combination (-(phi l O b)) * hd

end GlobalTheory.Cyc.FrobIdeal

namespace GlobalTheory.Cyc

open FrobIdeal

theorem XX_pow_mem_of_QQ_pow_mul_mem_map_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (s n H c : ℕ) [NeZero n], 1 ≤ s → ∀ 𝔞 : ZMod n → Ideal (PowerSeries O), (∀ i, PowerSeries.X ^ c ∈ 𝔞 i) → (∀ i, ∀ g ∈ 𝔞 i, QQ l O s ^ H * g ∈ (𝔞 (i - 1)).map (phi l O)) → ∀ i, XX l O s ^ H ∈ 𝔞 i := by
  intro l _ O _ _ _ _ _ hl0 hlu s n H c _ _ 𝔞 hc hK i
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ∀ a : O, ¬ IsUnit a → ϖ ∣ a := fun a ha => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact ha
  by_contra hi
  have main : ∀ (m : ℕ) (y : PowerSeries O), XX l O s ^ H * y ∈ 𝔞 (i + m) →
      y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ (m + 1)} := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [Nat.cast_zero, add_zero] at hy
      have hu : ¬ IsUnit y := fun hu => hi ((Ideal.mul_unit_mem_iff_mem _ hu).1 hy)
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu
      obtain ⟨t, ht⟩ := hdvd _ hu
      refine Ideal.mem_span_pair.2 ⟨PowerSeries.C t, PowerSeries.mk fun p => PowerSeries.coeff (p + 1) y, ?_⟩
      conv_rhs => rw [PowerSeries.eq_shift_mul_X_add_const y]
      rw [ht, map_mul]; ring
    | succ m ih =>
      intro y hy
      obtain ⟨z, hz, rfl⟩ := colon_le_map (phi l O : PowerSeries O →+* PowerSeries O)
        (fun j : Fin l => (1 + PowerSeries.X) ^ (j : ℕ)) (GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi l O hl0 hlu)
        (𝔞 (i + (m + 1 : ℕ))) (𝔞 (i + m)) (XX l O s ^ H) (QQ l O s ^ H)
        (by rw [map_pow, ← mul_pow]; exact congrArg (· ^ H) (Series.phi_XX l O s))
        (fun g hg => by
          have h := hK _ g hg
          rw [Nat.cast_succ, ← add_assoc, add_sub_cancel_right] at h
          exact h) hy
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _
        (phi_mem_span l O ϖ (hdvd _ hlu) (m + 1) (Nat.le_add_left 1 m) (ih _ (hz j)))
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (main c _ (Ideal.mul_mem_left _ _ (hc _)))
  have h := congrArg (PowerSeries.coeff c) hab
  rw [map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', if_neg (by omega),
    PowerSeries.coeff_X_pow, if_pos rfl, add_zero] at h
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one_right _ h)

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.IoMap

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem X_pow_dvd_sub_trunc (a : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ a - (trunc n a : Polynomial R) := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [coeff_trunc, hm]

theorem algHom_coe (f : R⟦X⟧ →ₐ[R] A) (p : Polynomial R) :
    f (p : R⟦X⟧) = Polynomial.aeval (f X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f X) := by
    ext
    simp
  simpa using DFunLike.congr_fun this p

theorem algHom_unique (f g : R⟦X⟧ →ₐ[R] A) (h : f X = g X)
    (hs : ∀ x : A, (∀ n, f X ^ n ∣ x) → x = 0) : f = g := by
  ext a
  rw [← sub_eq_zero]
  refine hs _ fun n => ?_
  obtain ⟨b, hb⟩ := X_pow_dvd_sub_trunc a n
  have h1 := congrArg f hb
  have h2 := congrArg g hb
  rw [map_sub, map_mul, map_pow, algHom_coe] at h1 h2
  rw [← h] at h2
  exact ⟨f b - g b, by linear_combination h1 - h2⟩

theorem algHom_exists (y : A) (hc : GlobalTheory.Per.AinfComplete.Summ y)
    (hs : ∀ x : A, (∀ n, y ^ n ∣ x) → x = 0) : ∃ f : R⟦X⟧ →ₐ[R] A, f X = y := by
  have h1 : ∀ a : R⟦X⟧, ∃ L : A, ∀ n, y ^ n ∣ L - Polynomial.aeval y (trunc n a) := by
    intro a
    obtain ⟨L, hL⟩ := hc fun i => algebraMap R A (coeff i a)
    refine ⟨L, fun n => ?_⟩
    have e : Polynomial.aeval y (trunc n a) =
        ∑ i ∈ Finset.range n, y ^ i * algebraMap R A (coeff i a) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [trunc_succ, map_add (f := _), ih, Finset.sum_range_succ, Polynomial.aeval_monomial, mul_comm]
    rw [e]
    exact Ideal.mem_span_singleton.1 (hL n)
  choose L hL using h1
  have h2 : ∀ (a : R⟦X⟧) (p : Polynomial R) (n : ℕ), (X : R⟦X⟧) ^ n ∣ a - p →
      y ^ n ∣ L a - Polynomial.aeval y p := by
    intro a p n h
    have h3 : (Polynomial.X : Polynomial R) ^ n ∣ trunc n a - p := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have := X_pow_dvd_iff.1 h d hd
      simpa [coeff_trunc, hd] using this
    have h4 := map_dvd (Polynomial.aeval y) h3
    rw [map_pow, Polynomial.aeval_X, map_sub] at h4
    convert dvd_add (hL a n) h4 using 1
    ring
  have h3 : ∀ p : Polynomial R, L p = Polynomial.aeval y p := fun p => by
    rw [← sub_eq_zero]
    exact hs _ fun n => h2 _ _ _ (by simp)
  have hadd : ∀ a b, L (a + b) = L a + L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := hL (a + b) n
    rw [map_add (f := _), map_add (f := _)] at this
    convert dvd_sub (dvd_sub this (hL a n)) (hL b n) using 1
    ring
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := h2 (a * b) (trunc n a * trunc n b) n (by
      rw [Polynomial.coe_mul]
      convert dvd_add ((X_pow_dvd_sub_trunc a n).mul_right b)
        ((X_pow_dvd_sub_trunc b n).mul_left (trunc n a : Polynomial R)) using 1
      ring)
    rw [map_mul] at this
    convert dvd_sub (dvd_sub this ((hL a n).mul_right (L b)))
      ((hL b n).mul_left (Polynomial.aeval y (trunc n a))) using 1
    ring
  refine ⟨{ toFun := L
            map_one' := by simpa using h3 1
            map_mul' := hmul
            map_zero' := by simpa using h3 0
            map_add' := hadd
            commutes' := fun r => by simpa using h3 (Polynomial.C r) }, ?_⟩
  simpa using h3 Polynomial.X

end General

variable (l : ℕ) [Fact l.Prime]

theorem ne_zero_of_coeff {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (m : ℕ) : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ coeff m a → ψ a ≠ 0 := by
  have h0 : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a → ψ a ≠ 0 := by
    intro a ha
    have : IsUnit (constantCoeff a) := by
      by_contra hn
      exact ha ((PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hn))
    exact ((isUnit_iff_constantCoeff.2 this).map ψ).ne_zero
  induction m with
  | zero => intro a ha; exact h0 a (by simpa using ha)
  | succ m ih =>
    intro a ha
    by_cases h : ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a
    · obtain ⟨c, hc⟩ := h
      rw [eq_X_mul_shift_add_const a, hc, map_add (f := _), map_mul, map_mul, map_mul, map_natCast,
        map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
      exact mul_ne_zero hX (ih _ (by simpa using ha))
    · exact h0 a h

theorem ne_zero_of_not_dvd {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (a : ℤ_[l]⟦X⟧) (ha : ¬ ((l : ℕ) : ℤ_[l]⟦X⟧) ∣ a) : ψ a ≠ 0 := by
  by_contra h
  apply ha
  have : ∀ m, ((l : ℕ) : ℤ_[l]) ∣ coeff m a := fun m => by
    by_contra hm
    exact ne_zero_of_coeff l ψ hX m a hm h
  choose c hc using this
  refine ⟨PowerSeries.mk c, ?_⟩
  ext m
  rw [← map_natCast (C : ℤ_[l] →+* ℤ_[l]⟦X⟧), coeff_C_mul, coeff_mk, hc]

theorem phi_X : phi l ℤ_[l] X = (1 + X) ^ l - 1 := by
  rw [phi, act, substAlgHom_X, cyc, binomialSeries_nat]
  simp

theorem constantCoeff_teich_sub (e : OCb l) :
    WittVector.constantCoeff (WittVector.teichmuller l e - 1 : Ainf l) = e - 1 := by
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem complete_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    GlobalTheory.Per.AinfComplete.Summ (WittVector.teichmuller l e - 1 : Ainf l) ∧
      ∀ x : Ainf l, (∀ n, (WittVector.teichmuller l e - 1 : Ainf l) ^ n ∣ x) → x = 0 := by
  have hy : ¬ IsUnit (WittVector.teichmuller l e - 1 : Ainf l) := fun h =>
    he (constantCoeff_teich_sub l e ▸ h.map WittVector.constantCoeff)
  have := (GlobalTheory.Per.AinfComplete.main l _ hy).2
  exact ⟨GlobalTheory.Per.AinfComplete.summ_of_precomplete _, fun x hx =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)⟩

noncomputable def frobA : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (x : Ainf l) : frobA l x = WittVector.frobenius x := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ e : OCb l, ¬ IsUnit (e - 1) →
    (∃! io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io) ∧
    ∀ io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io →
      (∀ a, io (phi l ℤ_[l] a) = WittVector.frobenius (io a)) ∧
      (e ≠ 1 → ∀ a, ¬ ((l : ℕ) : PowerSeries ℤ_[l]) ∣ a → IsUnit (inclW l (io a))) := by
  intro l hl e he
  obtain ⟨hc, hs⟩ := complete_teich l e he
  refine ⟨?_, fun io hio => ⟨?_, fun he1 a ha => ?_⟩⟩
  · obtain ⟨f, hf⟩ := algHom_exists (R := ℤ_[l]) _ hc hs
    refine ⟨f, hf, fun g hg => algHom_unique g f (Eq.trans hg hf.symm) ?_⟩
    rw [show g X = _ from hg]
    exact hs
  · have he' : ¬ IsUnit (e ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have e1 : (io.comp (phi l ℤ_[l])) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, phi_X, map_sub, map_pow, map_add (f := _), map_one, hio', map_pow]
      ring
    have e2 : ((frobA l).comp io) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, hio', map_sub, map_one]
      congr 1
      exact WittVector.map_teichmuller l (frobenius (OCb l) l) e
    have := algHom_unique _ _ (e1.trans e2.symm) (by rw [e1]; exact (complete_teich l _ he').2)
    intro a
    rw [← frobA_apply]
    exact DFunLike.congr_fun this a
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [inclW, WittVector.map_coeff]
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have := ne_zero_of_not_dvd l
      ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom) (by
        change WittVector.constantCoeff (io X) ≠ 0
        rw [hio', constantCoeff_teich_sub]
        exact sub_ne_zero.2 he1) a ha
    intro hz
    exact this ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))

end GlobalTheory.Cyc.IoMap
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.CharLat

theorem nonempty_equiv_of_free {O K : Type} [CommRing O] [IsDomain O] [Field K] [Module O K]
    (φ : O →+* K) (hsm : ∀ (o : O) (x : K), o • x = φ o * x)
    (hfr : ∀ z : K, ∃ a d : O, d ≠ 0 ∧ z * φ d = φ a)
    (T : Submodule O K) [Module.Free O T] (hT : T ≠ ⊥) :
    Nonempty (O ≃ₗ[O] T) := by
  let b := Module.Free.chooseBasis O T
  haveI hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) := by
    constructor
    intro i j
    by_contra hij
    have hi : ((b i : T) : K) ≠ 0 := fun h0 => b.ne_zero i (Subtype.ext h0)
    obtain ⟨a, d, hd0, hd⟩ := hfr (((b j : T) : K) / ((b i : T) : K))
    have hrel : d • b j + (-a) • b i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, ZeroMemClass.coe_zero,
        map_neg, ← hd]
      field_simp
      ring
    have hinj : Function.Injective ![j, i] := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd (hxy : j = i).symm hij
      · exact absurd (hxy : i = j) hij
      · rfl
    have hli : LinearIndependent O ![b j, b i] := by
      have := b.linearIndependent.comp ![j, i] hinj
      convert this using 1
      ext k
      fin_cases k <;> rfl
    have h2 := LinearIndependent.pair_iff.1 hli d (-a) hrel
    exact hd0 h2.1
  haveI hne : Nonempty (Module.Free.ChooseBasisIndex O T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have h0 : (⟨x, hx⟩ : T) = 0 := b.repr.injective (Subsingleton.elim _ _)
    simpa using congrArg Subtype.val h0
  haveI : Unique (Module.Free.ChooseBasisIndex O T) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact ⟨(LinearEquiv.funUnique (Module.Free.ChooseBasisIndex O T) O O).symm.trans b.equivFun.symm⟩

end GlobalTheory.CharLat

namespace GlobalTheory.CharLat


set_option maxHeartbeats 2000000 in
theorem exists_equiv_charLattice : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  intro l _ LL G _ _ θ Lc
  haveI := LL.2
  haveI hF : IsFractionRing (↥(OL LL)) (↥LL.1) :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥LL.1)
  haveI := Lc.free
  have hT : Lc.T ≠ ⊥ := by
    intro h
    have hs := Lc.span
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hs
    exact bot_ne_top hs
  have hsm : ∀ (o : ↥(OL LL)) (x : ↥LL.1), o • x = algebraMap (↥(OL LL)) (↥LL.1) o * x :=
    fun o x => rfl
  have hfr : ∀ z : ↥LL.1, ∃ a d : ↥(OL LL), d ≠ 0 ∧ z * algebraMap (↥(OL LL)) (↥LL.1) d =
      algebraMap (↥(OL LL)) (↥LL.1) a := by
    intro z
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (↥(OL LL))) z
    exact ⟨a, d, nonZeroDivisors.coe_ne_zero d, hd⟩
  obtain ⟨e⟩ := nonempty_equiv_of_free (algebraMap (↥(OL LL)) (↥LL.1)) hsm hfr Lc.T hT
  refine ⟨e, fun g a => ?_⟩
  rw [Formalism.GaloisCohomology.scalRep_apply, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_smul, hsm]
  rfl

end GlobalTheory.CharLat
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senWeights_close_of_height_gamma_conditions : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m), ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 → ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  first | exact @GlobalTheory.Models.sen_near_of_abc | exact GlobalTheory.Models.sen_near_of_abc | (intros; apply GlobalTheory.Models.sen_near_of_abc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  first | exact @GlobalTheory.Reg.Enlarge.enlarge_exists | exact GlobalTheory.Reg.Enlarge.enlarge_exists | (intros; apply GlobalTheory.Reg.Enlarge.enlarge_exists <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  first | exact @GlobalTheory.UnipCoords.unipCoordsHomeomorph | exact GlobalTheory.UnipCoords.unipCoordsHomeomorph | (intros; apply GlobalTheory.UnipCoords.unipCoordsHomeomorph <;> assumption)
end
