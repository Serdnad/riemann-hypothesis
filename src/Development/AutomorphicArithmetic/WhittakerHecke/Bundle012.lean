module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
public import GroundTheory.GlobalFields.TateThesis.Bundle009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)


open scoped nonZeroDivisors in
private theorem den_of {Q : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hQ : IsCompact Q) :
    ∃ d : ℕ, 0 < d ∧ ∀ q : ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ Q →
      ∃ l : ℤ, (d : ℚ) * q = l := by
  obtain ⟨D, hD0, hD⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set z : ℤ := Rat.ringOfIntegersEquiv D with hz
  have hz0 : z ≠ 0 := by
    intro h
    exact hD0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))
  have hdz : algebraMap (𝓞 ℚ) ℚ D = z := (Rat.ringOfIntegersEquiv_apply_coe D).symm
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, fun q hq => ?_⟩
  have h1 := hD _ hq
  rw [← map_mul] at h1
  have h2 : algebraMap (𝓞 ℚ) ℚ D * q ∈
      ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  have hn : ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) = (z : ℚ) * q := by
    rw [← hdz, ← hr]
    exact Rat.ringOfIntegersEquiv_apply_coe r |>.symm ▸ rfl
  rcases Int.natAbs_eq z with h | h
  · refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = z := by omega
    rw [hn, show ((z.natAbs : ℕ) : ℚ) = (z : ℚ) by rw [← Int.cast_natCast, e1]]
  · refine ⟨-Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = -z := by omega
    rw [Int.cast_neg, hn, show ((z.natAbs : ℕ) : ℚ) = -(z : ℚ) by
      rw [← Int.cast_natCast, e1, Int.cast_neg], neg_mul]

private theorem mul_int {a : ℕ} {q : ℚ} (c : ℕ) (h : ∃ l : ℤ, (a : ℚ) * q = l) :
    ∃ l : ℤ, ((c * a : ℕ) : ℚ) * q = l := by
  obtain ⟨l, hl⟩ := h
  refine ⟨c * l, ?_⟩
  push_cast
  rw [mul_assoc, hl]

theorem UpperTheory.exists_common_denom_of_isCompact_unipotent_translates :
    ∀ (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact L → ∀ S : Set (A ℚ)ˣ, IsCompact S →
        ∃ d : ℕ, 0 < d ∧ ∀ u ∈ S, ∀ (b : FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ ξ' : Fin 2 → ℚ),
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (∃ l : ℤ, (d : ℚ) * ξ 0 = l) ∧ (ξ 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ 1 = l) ∧
            (ξ 0 = ξ' 0 → ∃ l : ℤ, (d : ℚ) * (ξ 1 - ξ' 1) = l) := by
  intro L hL S hS
  have hf : Continuous fun u : (A ℚ)ˣ => (u : A ℚ).2 :=
    continuous_snd.comp Units.continuous_val
  have hi : Continuous fun u : (A ℚ)ˣ => ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hp : ∀ i : Fin 2, Continuous fun v : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => v i :=
    fun i => continuous_apply i
  set Q0 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      p.1 0 * ((p.2⁻¹ : (A ℚ)ˣ) : A ℚ).2) '' (L ×ˢ S) with hQ0
  set Q2 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => p.1 1 * (p.2 : A ℚ).2) '' (L ×ˢ S)
    with hQ2
  set Q1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      (p.1 1 - p.2.1 1) * (p.2.2 : A ℚ).2) '' (L ×ˢ (L ×ˢ S)) with hQ1
  have c0 : IsCompact Q0 := (hL.prod hS).image
    (((hp 0).comp continuous_fst).mul (hi.comp continuous_snd))
  have c2 : IsCompact Q2 := (hL.prod hS).image
    (((hp 1).comp continuous_fst).mul (hf.comp continuous_snd))
  have c1 : IsCompact Q1 := (hL.prod (hL.prod hS)).image
    ((((hp 1).comp continuous_fst).sub ((hp 1).comp (continuous_fst.comp continuous_snd))).mul
      (hf.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨d0, hd0, H0⟩ := den_of c0
  obtain ⟨d2, hd2, H2⟩ := den_of c2
  obtain ⟨d1, hd1, H1⟩ := den_of c1
  refine ⟨d1 * d2 * d0, by positivity, fun u hu b ξ ξ' h h' => ?_⟩
  have hu1 : (u : A ℚ).2 * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = 1 := by
    have h0 : (u : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := Units.mul_inv u
    exact congrArg Prod.snd h0
  have hu2 : ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = 1 := by
    rw [mul_comm, hu1]
  refine ⟨mul_int _ (H0 _ ⟨(_, u), ⟨h, hu⟩, ?_⟩), fun e => ?_, fun e => ?_⟩
  · change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2 *
      ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
    rw [mul_assoc, hu1, mul_one]
  · have := H2 (ξ 1) ⟨(_, u), ⟨h, hu⟩, by
      change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = _
      rw [e, map_zero, zero_mul, zero_add, mul_assoc, hu2, mul_one]⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d1 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
  · have := H1 (ξ 1 - ξ' 1) ⟨(_, _, u), ⟨h, h', hu⟩, by
      change ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 -
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2) * (u : A ℚ).2 = _
      rw [e, ← sub_mul, mul_assoc, hu2, mul_one, map_sub]
      ring⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d2 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

section

variable {E : Type} [Field E] [NumberField E]

private theorem norm_deg' (w : H.P E) : normV w = normV (w.under (𝓞 ℚ)) ^ w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 ℚ)).isMaximal
  simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 ℚ)).asIdeal w.asIdeal).symm

private theorem deg_le (h2 : Module.finrank ℚ E = 2) (v : H.P ℚ)
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 ℚ) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 ℚ) ℚ (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_sq (h2 : Module.finrank ℚ E = 2) {w : H.P E}
    (h : normV w ≠ normV (w.under (𝓞 ℚ))) : normV w = normV (w.under (𝓞 ℚ)) ^ 2 := by
  have := w.isPrime
  have hs := deg_le h2 (w.under (𝓞 ℚ)) {⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_singleton] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 ℚ)
  have h4 := norm_deg' w
  dsimp only at hs
  generalize w.asIdeal.inertiaDeg (𝓞 ℚ) = f at hs h3 h4
  interval_cases f
  · exact absurd (h4.trans (pow_one _)) h
  · exact h4

private theorem res_surj (w : H.P E) (hn : normV w = normV (w.under (𝓞 ℚ))) (x : 𝓞 E) :
    ∃ t : 𝓞 ℚ, x - algebraMap (𝓞 ℚ) (𝓞 E) t ∈ w.asIdeal := by
  have := (w.under (𝓞 ℚ)).isMaximal
  have := w.isPrime
  letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  let φ : (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) →+* (𝓞 E ⧸ w.asIdeal) :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 ℚ) (𝓞 E)) le_rfl
  have hb : Function.Bijective φ := (RingHom.injective φ).bijective_of_nat_card_le hn.le
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ x)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, Ideal.Quotient.eq.1 (hc.symm.trans ?_ )⟩
  exact Ideal.quotientMap_mk

private theorem num_den (v : H.P ℚ) {δ : ℚ} (h : v.valuation ℚ δ = 1) :
    ((δ.num : ℤ) : 𝓞 ℚ) ∉ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  have hmem : ∀ a : 𝓞 ℚ, a ∈ v.asIdeal ↔ v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a) < 1 :=
    fun a => (v.valuation_lt_one_iff_mem a).symm
  have e : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.num : ℤ) : 𝓞 ℚ)) =
      v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.den : ℕ) : 𝓞 ℚ)) := by
    rw [map_intCast, map_natCast, ← Rat.mul_den_eq_num δ, map_mul, h, one_mul]
  have hiff : ((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ↔ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hmem, hmem, e]
  have hc : IsCoprime ((δ.num : ℤ) : 𝓞 ℚ) ((δ.den : ℕ) : 𝓞 ℚ) := by
    have h1 : IsCoprime δ.num (δ.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact δ.reduced
    simpa using h1.map (Int.castRingHom (𝓞 ℚ))
  have hnot : ¬ (((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) := by
    rintro ⟨h1, h3⟩
    obtain ⟨x, y, hxy⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left x h1) (v.asIdeal.mul_mem_left y h3)))
  exact ⟨fun h1 => hnot ⟨h1, hiff.1 h1⟩, fun h3 => hnot ⟨hiff.2 h3, h3⟩⟩

private theorem val_two {K : Type} [Field K] [NumberField K] (v : H.P K) (h : Valued.v (2 : H.Kv v) = 1) :
    v.valuation K (2 : K) = 1 := by
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : K)).symm.trans ?_
  change Valued.v (algebraMap K (H.Kv v) 2) = 1
  rw [map_ofNat]
  exact h

private theorem no_ram (D : Dat ℚ E) (w : H.P E) (hG : H.Gd D.δ (w.under (𝓞 ℚ)))
    (hu : ∀ w' : H.P E, w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → w' = w)
    (hn : normV w = normV (w.under (𝓞 ℚ))) : False := by
  have hδ : (w.under (𝓞 ℚ)).valuation ℚ D.δ = 1 :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ D.δ).symm.trans hG.del
  have h2v : ((2 : ℕ) : 𝓞 ℚ) ∉ (w.under (𝓞 ℚ)).asIdeal := by
    have h := val_two _ hG.two
    have hmem : ((2 : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal ↔
        (w.under (𝓞 ℚ)).valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((2 : ℕ) : 𝓞 ℚ)) < 1 :=
      ((w.under (𝓞 ℚ)).valuation_lt_one_iff_mem _).symm
    rw [hmem, map_natCast, Nat.cast_ofNat, h]
    exact lt_irrefl _
  obtain ⟨ha, hb⟩ := num_den _ hδ
  set n : ℤ := D.δ.num with hnum
  set d : ℕ := D.δ.den with hden
  have hnd : (d : E) * algebraMap ℚ E D.δ = (n : E) := by
    have := congrArg (algebraMap ℚ E) (Rat.mul_den_eq_num D.δ)
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]
    exact this
  have hsq : ((d : E) * D.θ) ^ 2 = ((d * n : ℤ) : E) := by
    rw [mul_pow, D.sq, pow_two, mul_assoc, hnd]
    push_cast
    rfl
  have hint : IsIntegral ℤ ((d : E) * D.θ) :=
    IsIntegral.of_pow two_pos (hsq ▸ isIntegral_algebraMap (R := ℤ) (x := (d * n : ℤ)))
  obtain ⟨T, hT⟩ : ∃ T : 𝓞 E, (T : E) = (d : E) * D.θ := ⟨⟨_, hint⟩, rfl⟩
  have hT2 : T ^ 2 = algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) := by
    refine RingOfIntegers.ext ?_
    simp only [map_pow, map_mul, map_natCast, map_intCast]
    rw [show (algebraMap (𝓞 E) E) T = (T : E) from rfl, hT, hsq]
    push_cast
    rfl
  let e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv D.σ.toRingEquiv
  have hcomm : ∀ a : 𝓞 ℚ, e (algebraMap (𝓞 ℚ) (𝓞 E) a) = algebraMap (𝓞 ℚ) (𝓞 E) a :=
    fun a => RingOfIntegers.ext (D.σ.commutes (a : ℚ))
  have h1 : w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective = w := by
    refine hu _ (HeightOneSpectrum.ext (Ideal.ext fun a => ?_))
    change e (algebraMap (𝓞 ℚ) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) a ∈ w.asIdeal
    rw [hcomm]
  have he : ∀ x, x ∈ w.asIdeal → e x ∈ w.asIdeal := by
    intro x hx
    have h3 : x ∈ (w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := by
      rw [h1]
      exact hx
    exact h3
  have heT : e T = -T := by
    refine RingOfIntegers.ext ?_
    change D.σ (T : E) = _
    rw [hT, map_mul, map_natCast, D.conj]
    simp [hT]
  obtain ⟨t, ht⟩ := res_surj w hn T
  have ht' := he _ ht
  rw [map_sub, heT, hcomm] at ht'
  have h2T : algebraMap (𝓞 ℚ) (𝓞 E) ((2 : ℕ) : 𝓞 ℚ) * T ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem ht ht'
    rw [map_natCast]
    convert this using 1
    push_cast
    ring
  have := w.isPrime
  rcases w.isPrime.mem_or_mem h2T with h | h
  · exact h2v h
  · have h5 : algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) ∈ w.asIdeal := by
      rw [← hT2, pow_two]
      exact w.asIdeal.mul_mem_left _ h
    rcases (w.under (𝓞 ℚ)).isPrime.mem_or_mem (show _ ∈ (w.under (𝓞 ℚ)).asIdeal from h5) with h6 | h6
    · exact hb h6
    · exact ha h6

end

theorem UpperTheory.good_prime_split_or_inert_of_quadratic :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ), H.Gd D.δ v → (∃ w : H.P E, w.under (𝓞 ℚ) = v) ∧
        ∀ w : H.P E, w.under (𝓞 ℚ) = v → (normV w = normV v ∧ ∃ w' : H.P E, w' ≠ w ∧ w'.under (𝓞 ℚ) = v) ∨ normV w = normV v ^ 2 := by
  intro E _ _ D v hG
  have h2 : Module.finrank ℚ E = 2 := by simpa using Module.finrank_eq_card_basis D.b
  refine ⟨?_, fun w hw => ?_⟩
  · have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  · subst hw
    by_cases hn : normV w = normV (w.under (𝓞 ℚ))
    · refine Or.inl ⟨hn, ?_⟩
      by_contra hu
      push_neg at hu
      exact no_ram D w hG (fun w' h => by_contra fun hne => hu w' hne h) hn
    · exact Or.inr (norm_sq h2 hn)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.AdeleBaseChangeSplitting
open UpperTheory.ConvolutionTheory.R2.H GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem split_iota (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal] (h : SplitAt v w) :
    ∃ i : Kv v ≃+* Kv w, (∀ x, completionMap v w x = i x) ∧
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (i x) = Valued.v x := by
  obtain ⟨-, i, hc, ha, hv⟩ := h
  refine ⟨i, ?_, ha, hv⟩
  have := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).equalizer
    (continuous_completionMap v w) hc (by
      funext x
      change completionMap v w (algebraMap F (Kv v) x) = i (algebraMap F (Kv v) x)
      rw [ha, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w)])
  exact fun x => congrFun this x

private theorem adeleMap_split_two_places (v : P F) (w w' : P E) [hl : w.asIdeal.LiesOver v.asIdeal]
    [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc', -, -, -, -, hs', -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc'', -, -, -, -, hs'', -, -⟩ := sgLaws E w'
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs' _).1, (hs'' _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs'' _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc' _).symm
    · by_cases h' : u = w'
      · subst h'
        have hb : below F u = v := (below_eq_iff _ _).2 hl'
        subst hb
        rw [(hs' _).2 _ h, zero_add]
        exact (congrArg _ (hc x)).trans (hc'' _).symm
      · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
        rw [(hs x).2 _ hb, map_zero, (hs' _).2 _ h, (hs'' _).2 _ h', add_zero]

private theorem main (D : Dat F E) (v : P F) (w w' : P E) [hl : w.asIdeal.LiesOver v.asIdeal]
    [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w') (h1 : SplitAt v w) (h2 : SplitAt v w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (hG : Gd D.δ v) :
    ∃ χ : Kv w → ℂ, Good χ ∧ ∀ x, ∃ u t, sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  obtain ⟨i, hi, hia, hiv⟩ := split_iota v w h1
  obtain ⟨j, hj, hja, hjv⟩ := split_iota v w' h2
  obtain ⟨τ, hτ⟩ := i.surjective (algebraMap E (Kv w) D.θ)
  have hτ2 : τ ^ 2 = algebraMap F (Kv v) D.δ := by
    apply i.injective
    rw [map_pow, hτ, hia, ← map_pow, D.sq]
  have hτv : Valued.v τ = 1 := by
    have h := hG.del
    rw [← hτ2, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτv
  have h20 : (2 : Kv v) ≠ 0 := fun h => by simpa [h] using hG.two
  have hτ' : j τ = -algebraMap E (Kv w') D.θ := by
    have hsq : (j τ) ^ 2 = (algebraMap E (Kv w') D.θ) ^ 2 := by
      rw [← map_pow, hτ2, hja, ← map_pow, D.sq]
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left fun he => hne ?_
    have hval : ∀ y : E, w.valuation E y = w'.valuation E y := by
      intro y
      have hy : y = algebraMap F E (D.b.repr y 0) + algebraMap F E (D.b.repr y 1) * D.θ := by
        conv_lhs => rw [← D.b.sum_repr y]
        simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
      set a := algebraMap F (Kv v) (D.b.repr y 0)
      set b := algebraMap F (Kv v) (D.b.repr y 1)
      have e1 : algebraMap E (Kv w) y = i (a + b * τ) := by
        rw [map_add (f := _), map_mul, hτ, hia, hia, ← map_mul, ← map_add (f := _), ← hy]
      have e2 : algebraMap E (Kv w') y = j (a + b * τ) := by
        rw [map_add (f := _), map_mul, he, hja, hja, ← map_mul, ← map_add (f := _), ← hy]
      rw [← valued_algebraMap_field, ← valued_algebraMap_field, e1, e2, hiv, hjv]
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), hval]
  have hcv : Valued.v (2 * τ) = 1 := by rw [map_mul, hG.two, hτv, mul_one]
  obtain ⟨g1, g2, g3⟩ := hG.psi
  obtain ⟨hadd, hmul, -⟩ := sgLaws F v
  obtain ⟨hadd1, hmul1, -⟩ := sgLaws E w
  obtain ⟨hadd2, hmul2, -⟩ := sgLaws E w'
  have hsv : ∀ x : Kv w, Valued.v (-(i.symm x / (2 * τ))) = Valued.v x := by
    intro x
    rw [Valuation.map_neg, map_div₀, hcv, div_one, ← hiv, RingEquiv.apply_symm_apply]
  refine ⟨fun x => ψ (sg v (-(i.symm x / (2 * τ)))), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩,
    fun x => ⟨sg v (i.symm x / 2), sg v (i.symm x / (2 * τ)), ?_, ?_⟩⟩
  · have e : -(i.symm (x + y) / (2 * τ)) = -(i.symm x / (2 * τ)) + -(i.symm y / (2 * τ)) := by
      rw [map_add (f := _)]; ring
    show ψ (sg v (-(i.symm (x + y) / (2 * τ)))) = _
    rw [e]
    exact g1 _ _
  · exact g2 _ (by unfold IsInt at *; rw [hsv]; exact hx)
  · have := g3 (-(i.symm x / (2 * τ))) fun c hc => by
      have h := hx (i c) (by unfold IsInt at *; rw [hiv]; exact hc)
      have e : -(i.symm (i c * x) / (2 * τ)) = c * -(i.symm x / (2 * τ)) := by
        rw [map_mul, RingEquiv.symm_apply_apply]; ring
      change ψ (sg v (-(i.symm (i c * x) / (2 * τ)))) = 1 at h
      rw [e] at h
      exact h
    unfold IsInt at *
    rwa [hsv] at this
  · have hmk : ∀ u t : A F, D.mkE u t = adeleMap F E u + adeleMap F E t * rt D.θ := fun _ _ => rfl
    obtain ⟨y, rfl⟩ := i.surjective x
    have z2 : sg w' 0 = 0 := by
      have := hmul2 0 0
      simpa using this.symm
    have c1 : cp w (rt D.θ) = i τ := hτ.symm
    have c2 : cp w' (rt D.θ) = - j τ := by rw [hτ', neg_neg]; rfl
    rw [RingEquiv.symm_apply_apply, hmk, adeleMap_split_two_places v w w' hne hu, adeleMap_split_two_places v w w' hne hu,
      add_mul, mul_comm (sg w _), mul_comm (sg w' _), hmul1, hmul2, add_add_add_comm, ← hadd1, ← hadd2,
      c1, c2, hi, hi, hj, hj, ← map_neg, ← map_mul, ← map_mul, ← map_add, ← map_add,
      show y / 2 + τ * (y / (2 * τ)) = y by field_simp; ring,
      show y / 2 + -τ * (y / (2 * τ)) = 0 by field_simp; ring, map_zero, z2, add_zero]
  · have := hmul (-1) (i.symm x / (2 * τ))
    rw [map_neg, map_one, neg_one_mul, neg_one_mul] at this
    rw [this]

end UpperTheory.AdeleBaseChangeSplitting

theorem UpperTheory.exists_localCharacter_of_split_pair_rat :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') → H.Gd D.δ v →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w w' hne hw hw' h1 h2 hu hG
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  exact UpperTheory.AdeleBaseChangeSplitting.main D v w w' hne h1 h2
    (fun u h => hu u (HeightOneSpectrum.ext h.1.symm)) hG
end
