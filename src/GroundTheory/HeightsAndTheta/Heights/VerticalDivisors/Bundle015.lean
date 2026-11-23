module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (P J : Ideal A) (ψ : A ⧸ P →+* L)
    (hloc : IsLocalHom (ψ.comp (Ideal.Quotient.mk P))) (hflat : ψ.Flat)
    (hmax : (IsLocalRing.maximalIdeal A).map (ψ.comp (Ideal.Quotient.mk P)) =
      IsLocalRing.maximalIdeal L) :
    Module.length L (L ⧸ J.map (ψ.comp (Ideal.Quotient.mk P))) =
      Module.length A (A ⧸ (P ⊔ J)) := by
  have : Nontrivial (A ⧸ P) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg ψ h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := ψ.toAlgebra
  have : Module.Flat (A ⧸ P) L := hflat
  have : IsLocalHom (algebraMap (A ⧸ P) L) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (hloc.map_nonunit a ha).map _
  have hq : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk P) =
      IsLocalRing.maximalIdeal (A ⧸ P) := by
    have h : (IsLocalRing.maximalIdeal (A ⧸ P)).comap (Ideal.Quotient.mk P) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hmax' : (IsLocalRing.maximalIdeal (A ⧸ P)).map (algebraMap (A ⧸ P) L) =
      IsLocalRing.maximalIdeal L := by
    rw [← hq, Ideal.map_map]
    exact hmax
  have key := IsLocalRing.length_baseChange (A ⧸ P) L ((A ⧸ P) ⧸ J.map (Ideal.Quotient.mk P))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L
    (J.map (Ideal.Quotient.mk P))).toLinearEquiv.length_eq, hmax'] at key
  have h1 : Module.length L (L ⧸ IsLocalRing.maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one, Ideal.map_map, RingHom.algebraMap_toAlgebra] at key
  rw [key, ← Module.length_eq_of_surjective (S := A) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A P J).toLinearEquiv.length_eq

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (u : Fin n → R) :
    (linForm u).map φ = linForm (fun j => φ (u j)) := by

  simp only [linForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

theorem secLin_eq_mk_map {K : Type*} [Field K] [NumberField K] {n e : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (u : Fin n → 𝓞 K) :
    secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      Ideal.Quotient.mk _ ((linForm u).map (algebraMap (𝓞 K) (ParDVR e n v))) := by
  rw [secLin, map_linForm]

theorem SpecLength.proof (h1 : SpecChart.Statement) (h2 : FiniteOrd.Statement)
    (h3 : ParDVRIsDVR.Statement) (h4 : SecBFinite.Statement) (h5 : SecBLinInj.Statement) :
    SpecLength.Statement := by
  classical
  intro K _ _ n e I f u v hI hf hu 𝔫 W hW hWn
  have hWp : W.IsPrime := hW.1.1.1
  obtain ⟨ψ, hψ, hloc, hflat, hmax⟩ := h1 K n e I v hI 𝔫 W hW hWn
  have := h3 K e n v
  have := h4 K n e I f v hI hf
  have hfin := h2 (ParDVR e n v) (SecB e I v) _ (h5 K n e I f u v hI hf hu) 𝔫
  have hx : algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
      (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))) =
      (ψ.comp (Ideal.Quotient.mk _)) (algebraMap _ (Localization.AtPrime W) (linForm u)) := by
    rw [RingHom.comp_apply, hψ]
    exact congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)) (secLin_eq_mk_map I v u)
  have hlen0 := length_quot_map_of_flat (A := Localization.AtPrime W)
    (L := Localization.AtPrime 𝔫.asIdeal)
    (P := (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
    (J := Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}) (ψ := ψ) hloc hflat
  have hlen := hlen0 hmax
  rw [Ideal.map_span, Set.image_singleton, ← hx] at hlen
  have hmult : localMult (integralModel I ⊔ Ideal.span {linForm u}) W =
      (Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸
        ((integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
          Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}))).toNat := by
    rw [localMult, dite_eq_left hWp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  unfold Ring.ord at hfin ⊢
  rw [hlen] at hfin ⊢
  split_ifs with hlW
  · rw [hmult, ENat.natCast_toNat hfin]
  · have hunit : IsUnit (algebraMap _ (Localization.AtPrime W) (linForm u)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ W _).mpr hlW
    have htop : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
        Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)} = ⊤ :=
      eq_top_iff.mpr (le_sup_of_le_right (Ideal.span_singleton_eq_top.mpr hunit).ge)
    rw [htop]
    have : Subsingleton (Localization.AtPrime W ⧸ (⊤ : Ideal (Localization.AtPrime W))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem homogeneousComponent_map_coeffs {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem SpecCompDim.proof (hCone : ConeDimOfChowForm.Statement) (hFib : FibreCompDim.Statement) :
    SpecCompDim.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : I.IsPrime := hI.isPrime
  let k := v.asIdeal.ResidueField
  let φ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k :=
    MvPolynomial.map (algebraMap (𝓞 K) k)
  let ψ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) K :=
    MvPolynomial.map (algebraMap (𝓞 K) K)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hker : RingHom.ker φ = Ideal.map C v.asIdeal := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWprime : W.IsPrime := hWmin.1.1
  have hkerW : RingHom.ker φ ≤ W := hker ▸ le_sup_right.trans hWmin.1.2

  have hP : (integralModel I).IsPrime := Ideal.comap_isPrime ψ I
  have hPC : (integralModel I).comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, integralModel, Ideal.mem_bot]
    constructor
    · intro h
      by_contra hc
      have hu : IsUnit (ψ (C c)) := by
        rw [show ψ (C c) = C (algebraMap (𝓞 K) K c) from map_C _ _]
        exact (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc)).map C
      exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    · rintro rfl
      simp
  have hPloc : (integralModel I).map ψ = I := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := 𝓞 K) (S := K)
    have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (𝓞 K)) K
    exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin n)))
      (MvPolynomial (Fin n) K) I
  have hdim := hFib (𝓞 K) K n (integralModel I) W v hP hPC hWmin
  rw [hPloc, hCone K n (e + 1) I f hI hf] at hdim
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hkerW, ?_, ?_⟩, hdim⟩
  ·
    have hmin : reduceMod v W ∈ (reduceMod v (integralModel I)).minimalPrimes := by
      change W.map φ ∈ ((integralModel I).map φ).minimalPrimes
      rw [Ideal.minimalPrimes_map_of_surjective hφ, hker]
      exact ⟨W, hWmin, rfl⟩
    refine MinimalPrimeHomog.proof k n _ _ ?_ hmin
    intro g hg d
    change g ∈ (integralModel I).map φ at hg
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hg
    rw [homogeneousComponent_map_coeffs]
    refine Ideal.mem_map_of_mem φ ?_
    change ψ (homogeneousComponent d p) ∈ I
    rw [← homogeneousComponent_map_coeffs]
    exact hI.isHomog _ hp d
  ·
    obtain ⟨j, hj⟩ := hWrel
    refine ⟨j, fun h => hj ?_⟩
    have h' : X j ∈ (W.map φ).comap φ := by
      rw [Ideal.mem_comap, map_X]
      exact h
    rwa [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerW] at h'

end

end GroundTheory.Heights₂.Heights.Vertical
end
