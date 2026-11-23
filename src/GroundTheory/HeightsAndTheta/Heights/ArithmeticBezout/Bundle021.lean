module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle019
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem aeval_mul_homogeneousComponent {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
    (q : MvPolynomial (Fin n) F) (e : ℕ) (t : Ω) (x : Fin n → Ω) :
    aeval (fun m => t * x m) (homogeneousComponent e q) = t ^ e * aeval x (homogeneousComponent e q) := by

  rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_filter] at hα
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hdeg : Finsupp.degree α = ∑ i ∈ α.support, α i := rfl
  rw [← hα.2, hdeg]
  ring

theorem FormsThroughPoint.proof (hZ : IncidenceZeroLocus.Statement) (hI : ThroughPointIncIdeal.Statement)
    (hC : ChartZeroTrdeg.Statement) (hT : ThroughTwoPointsTrdeg.Statement)
    (hB : TrdegBaseAlgebraic.Statement) : FormsThroughPoint.Statement := by
  intro F _ n k Q hQ hdim x hx hxQ
  obtain ⟨q, hqQ, hqx⟩ := hxQ

  have h1 := ComponentOfIncIdeal.one_le_ringKrullDim_quot hQ
  obtain ⟨d, hd, hdk⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
      d + 1 ≤ k := by
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at h1 hdim ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := hdim
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m =>
        have h1' : 1 ≤ m := by exact_mod_cast h1
        have hm : m ≤ k := by exact_mod_cast hdim
        refine ⟨m - 1, ?_, by omega⟩
        rw [show m - 1 + 1 = m by omega]
        rfl

  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  let c : Fin n → AlgebraicClosure F := Pi.single j₀ (x j₀)⁻¹
  have hj₀' : x j₀ ≠ 0 := hj₀
  have hc : ∑ j, c j * x j = 1 := by
    rw [Finset.sum_eq_single j₀ (fun b _ hb => by simp [c, hb]) (by simp)]
    simp [c, hj₀']
  by_contra hno
  push Not at hno

  have hg := hI F n k Q x c hc hno
  let K := AlgebraicClosure F
  let R := MvPolynomial (Fin k × Fin n) K
  let Ω := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let v : Fin k × Fin n → Ω := fun ij => algebraMap R Ω (genSubst x c ij)
  have hv : ∀ g ∈ incIdeal Q k, aeval v g = 0 := by
    intro g hgI
    have hval : aeval v g = algebraMap R Ω (aeval (genSubst x c) g) := aeval_algebraMap_apply Ω (genSubst x c) g
    rw [hval, hg g hgI, map_zero]
  obtain ⟨y, hy0, hyQ, hyv⟩ := hZ F n k Q hQ.isHomog Ω v hv

  have hnp : ∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m) := by
    intro t ht
    obtain ⟨e, he⟩ : ∃ e, aeval x (homogeneousComponent e q) ≠ 0 := by
      by_contra h
      push Not at h
      apply hqx

      rw [← sum_homogeneousComponent q, map_sum]
      exact Finset.sum_eq_zero fun e _ => h e
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hy0
      rw [ht]
      funext m
      simp
    have hzero := hyQ _ (hQ.isHomog q hqQ e)
    have hscale := aeval_mul_homogeneousComponent q e t (algebraMap K Ω ∘ x)
    simp only [Function.comp_apply] at hscale
    rw [ht, hscale, aeval_algebraMap_apply] at hzero
    exact mul_ne_zero (pow_ne_zero _ ht0) ((map_ne_zero _).mpr he) hzero

  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have hk := hT K Ω n k hinj x c hc y j hj hnp hyv
  have hb := hB F K Ω inferInstance (Fin n) (fun m => y m * (y j)⁻¹)
  have hd' := hC F n d Q hQ hd Ω y j hyQ hj
  have hkd : (k : Cardinal) ≤ d := hk.trans (hb.trans hd')
  norm_cast at hkd
  omega

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

private theorem mem_incIdeal_iff {P : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ u ∈ incidence P k, aeval u g = 0 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

end Helpers

theorem ChowFormReduced.proof_of_prime_separate (hPrime : IncIdealPrime.Statement) (hSep : IncIdealSeparate.Statement) :
    ChowFormReduced.Statement := by
  classical
  intro F _ n k J h hJh hJr hch
  have hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W :=
    fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW
  have hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J :=
    fun W hW => (mem_support_fundCycle_iff hJr).mp hW

  have hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k := by
    intro g
    rw [← hch.2 g]
    constructor
    · intro hg W hW
      exact mem_incIdeal_iff.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)
    · intro hg u hu
      obtain ⟨W, hW, huW⟩ := exists_relComps_of_mem_incidence hu
      exact mem_incIdeal_iff.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW

  have hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support,
      incIdeal W' k ≤ incIdeal W k → W' = W := by
    intro W hW W' hW' hle
    have hne : incIdeal W' k ≠ ⊥ := fun hb => hch.1 (by
      have := (hspan h).mp dvd_rfl W' hW'
      rwa [hb, Ideal.mem_bot] at this)
    have hWW' : W' ≤ W := hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle
    exact le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')

  have hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q} := by
    intro W hW
    have hPW : (incIdeal W k).IsPrime := hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant
    have hhW : h ∈ incIdeal W k := (hspan h).mp dvd_rfl W hW
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hch.1
    have hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k := by
      rwa [← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit] at hhW
    obtain ⟨q, hqf, hqW⟩ := (hPW.multiset_prod_mem_iff_exists_mem _).1 hprod
    have hq : Prime q := UniqueFactorizationMonoid.prime_of_factor q hqf
    have hqh : q ∣ h := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
    have hqle : Ideal.span {q} ≤ incIdeal W k := (Ideal.span_singleton_le_iff_mem _).mpr hqW
    refine ⟨q, hq, le_antisymm ?_ hqle⟩
    have hqP : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q} := by
      intro g hg
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hqh ((hspan g).mpr fun W' hW' =>
        Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)
    obtain ⟨W', hW', hle⟩ := hqP.inf_le'.mp hinf
    have hW'W : W' = W := hsep W hW W' hW' (hle.trans hqle)
    rw [← hW'W]
    exact hle
  choose! q hq hqspan using hprin

  have hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h := by
    refine Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_
    · intro W hW W' hW' hne
      refine (hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_
      have hmem : q W' ∈ incIdeal W k := by
        rw [hqspan W hW]
        exact Ideal.mem_span_singleton.mpr hdvd
      refine (hsep W hW W' hW' ?_).symm
      rw [hqspan W' hW']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    · have := (hspan h).mp dvd_rfl W hW
      rw [hqspan W hW] at this
      exact Ideal.mem_span_singleton.mp this
  have hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W := by
    refine (hspan _).mpr fun W hW => ?_
    rw [hqspan W hW]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁ hdvd₂
  obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp
    u.isUnit
  refine ⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩
  · rw [← mem_incIdeal_iff, hqspan W hW, Ideal.mem_span_singleton]
  · rw [Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one],
      ← hu, hur, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ProjDegreeChow.proof (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by
  intro n e δ W f A hW hf hδ hA
  rw [h₁ n e W A]
  obtain ⟨hdom, hfin⟩ := h₂ n e W A hW.isPrime hA
  have hc := h₃ n e W f A hW hf hA
  have hsep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
      (Vertical.SecAlg
        (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
        (projPar A)) :=
    ⟨fun x => PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  refine le_antisymm (h₄ ℂ _ n e δ W f (projPar A) hW hf hδ hfin hdom hsep fun h => hc ?_)
    (h₅ ℂ _ n e δ W f (projPar A) hW hf hδ hc).2
  rw [h, map_zero]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeBallFinite.proof (hMass : ConeIntegralMass.Statement) : ConeBallFinite.Statement := by
  intro n e h W f hW hf
  obtain ⟨δ, hδ1, hδ⟩ := hf.exists_multiHomog hW
  have hm := hMass n e δ h W f hW hf hδ
  rw [lt_top_iff_ne_top]
  intro hinf
  unfold coneIntegral at hm
  change (∫ y in coneBall h W, (1 : ℝ) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / _ =
    (δ : ℝ) at hm
  rw [setIntegral_const, measureReal_def, hinf, ENNReal.toReal_top, zero_smul, zero_div] at hm
  have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  exact hδ0 hm.symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I) :
    IsHomogIdeal (I.map (MvPolynomial.map φ)) := by
  rw [isHomogIdeal_iff] at hI ⊢
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  rw [hT, Ideal.map_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := x.2
  refine ⟨d, ?_⟩
  rw [mem_homogeneousSubmodule] at hd ⊢
  exact hd.map φ

theorem ChowFormBaseChange.proof (hRad : RadicalBaseChange.Statement)
    (hExt : ChowFormExtend.Statement) (hRed : ChowFormReduced.Statement) :
    ChowFormBaseChange.Statement := by
  intro K _ _ n k I f σ hI hf
  have hJ : IsHomogIdeal (I.map (MvPolynomial.map σ)) := isHomogIdeal_map σ hI.isHomog
  refine ⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩
  exact hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem map_specFirst {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {k n : ℕ}
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial.map φ (specFirst f u) = specFirst (MvPolynomial.map φ f) (fun j => φ (u j)) := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar]
  | succ i => simp [specFirstVar]

theorem ChowHeightRecursion.proof (hV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) :
    ChowHeightRecursion.Statement := by
  intro K _ _ n e δ H I f u hI hf hδ hu
  set u' : Fin n → K := fun j => (u j : K) with hu'
  set g := specFirst f u' with hg

  have hfin_f := log_gaussNorm_support_finite (K := K) hf.1
  have hfin_g : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v g)).Finite := by
    by_cases hg0 : g = 0
    · have : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => Real.log (gaussNorm v g)) = 0 := by
        funext v
        rw [hg0]
        simp [gaussNorm]
        exact Or.inl rfl
      rw [this, Function.support_zero]
      exact Set.finite_empty
    · exact log_gaussNorm_support_finite hg0
  have hfinsum : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g)) + vertTerm I (e + 1) u := by
    unfold vertTerm
    rw [← finsum_add_distrib hfin_g]
    · refine finsum_congr fun v => ?_
      rw [← hV K n e I f u hI hf hu v]
      ring
    · refine Set.Finite.subset (hfin_f.union hfin_g) fun v hv => ?_
      rw [Function.mem_support, ← hV K n e I f u hI hf hu v] at hv
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
      exact hv (by rw [hcon.1, hcon.2, sub_zero])

  have harch : ∀ σ : K →+* ℂ, mahler (H.normAt σ) (e + 1) (f.map σ) =
      mahler (H.normAt σ) e (g.map σ) - δ * (harmonic (n - 1) : ℝ) / 2 -
        cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    intro σ
    obtain ⟨hprime, hcyc⟩ := hB K n (e + 1) I f σ hI hf
    have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
      (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
    have h := hA n e δ (H.normAt σ) _ _ (fun j => σ (u j)) hprime hcyc hδσ
      (fun W hW => hAv K n I u' σ hI hu W hW)
    rw [hg, map_specFirst, h]
    ring
  unfold chowHt
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) (e + 1) (f.map σ) +
        ((e + 1 : ℕ) : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) e (g.map σ) + (e : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) -
        ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [harch σ]
    push_cast
    ring
  rw [hfinsum, hs]
  ring

end

end GroundTheory.Heights₂.Heights
end
