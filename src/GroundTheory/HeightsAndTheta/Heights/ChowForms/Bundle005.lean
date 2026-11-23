module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle003
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartFirstGroupDvd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      (∑ m, X m * C (chartX I t e (X m))) ∣
        map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

noncomputable section

namespace LengthFiniteAlgebra

variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

theorem comap_eq_maximalIdeal [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    P.comap (algebraMap O B) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)

theorem finite_maximalSpectrum [Module.Finite O B] : Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := O) (S := B) (maximalIdeal O)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal O).primesOver B)
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, ⟨(comap_eq_maximalIdeal P.asIdeal).symm⟩⟩) ?_
  intro P Q h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)

theorem length_eq_finsum_localization [IsNoetherianRing O] [Module.Finite O B] :
    Module.length O B =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype, ← Module.length_pi_of_fintype]
  let φ : B →ₗ[O] (∀ P : MaximalSpectrum B, Localization.AtPrime P.asIdeal) :=
    LinearMap.pi fun P => (IsScalarTower.toAlgHom O B (Localization.AtPrime P.asIdeal)).toLinearMap
  have hφ : Function.Injective φ := by
    intro x y h
    apply MaximalSpectrum.toPiLocalization_injective B
    funext P
    exact congrFun h P
  by_cases h : Module.length O B = ⊤
  · rw [h]
    exact (top_le_iff.mp (h ▸ Module.length_le_of_injective φ hφ)).symm
  · have hfl : IsFiniteLength O B := Module.length_ne_top_iff.mp h
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
    have : IsArtinianRing B := isArtinian_of_tower O hfl.2
    have hsurj : Function.Surjective φ := by
      intro z
      obtain ⟨x, hx⟩ := PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology B z
      exact ⟨x, hx⟩
    exact (LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).length_eq

theorem isLocalHom_localization [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ P.comap (algebraMap O B) := by
    rw [comap_eq_maximalIdeal P]; exact hna
  have h2 : algebraMap B (Localization.AtPrime P) (algebraMap O B a) ∈
      maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2 ha


omit [IsLocalRing O] in
theorem length_residueField (P : Ideal B) [P.IsMaximal] :
    Module.length O (ResidueField (Localization.AtPrime P)) = Module.length O (B ⧸ P) := by
  let e' : (B ⧸ P) ≃ₐ[B] ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  exact (e'.toLinearEquiv.restrictScalars O).length_eq.symm

theorem ord_mul_length [Module.Finite O B] (P : Ideal B) [P.IsMaximal] (θ : B) :
    Ring.ord (Localization.AtPrime P) (algebraMap B _ θ) * Module.length O (B ⧸ P) =
      Module.length O (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) θ}) := by
  have := isLocalHom_localization (O := O) P
  have h1 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) θ})
  have h2 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (ResidueField (Localization.AtPrime P))
  have h3 : Module.length (Localization.AtPrime P) (ResidueField (Localization.AtPrime P)) = 1 := by
    rw [Module.length_eq_of_surjective (S := Localization.AtPrime P)
      (R := ResidueField (Localization.AtPrime P)) residue_surjective]
    exact Module.length_eq_one _ _
  rw [length_residueField, h3, one_mul] at h2
  rw [h2, h1]
  rfl


omit [IsLocalRing O] in
theorem length_localization_quotient (I : Ideal B) (Q : Ideal (B ⧸ I)) [Q.IsMaximal] :
    Module.length O (Localization.AtPrime Q) =
      Module.length O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl =
      Q.primeCompl := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  have : IsLocalization Q.primeCompl
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
    rw [← hsub]; infer_instance
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))
  have : IsScalarTower O (B ⧸ I)
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ I),
        IsScalarTower.algebraMap_apply O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))),
        IsScalarTower.algebraMap_apply O B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))]
      rfl
  exact (e.toLinearEquiv.restrictScalars O).length_eq

theorem finsum_reindex [Module.Finite O B] (θ : B) :
    ∑ᶠ Q : MaximalSpectrum (B ⧸ Ideal.span {θ}), Module.length O (Localization.AtPrime Q.asIdeal) =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P.asIdeal) θ}) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  have := finite_maximalSpectrum (O := O) (B := B ⧸ Ideal.span {θ})
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Fintype.ofFinite (MaximalSpectrum (B ⧸ Ideal.span {θ}))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let ι : MaximalSpectrum (B ⧸ Ideal.span {θ}) → MaximalSpectrum B := fun Q =>
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk _), by
      have := Q.isMaximal; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  refine Fintype.sum_of_injective ι ?_ _ _ ?_ ?_
  · intro Q₁ Q₂ h
    exact MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  · intro P hP
    have hθ : θ ∉ P.asIdeal := by
      intro hθ
      apply hP
      have hle : Ideal.span {θ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hθ
      have := P.isMaximal
      have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := P.asIdeal)
        (f := Ideal.Quotient.mk (Ideal.span {θ})) Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
      exact ⟨⟨_, hmax⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩
    have hu : IsUnit (algebraMap B (Localization.AtPrime P.asIdeal) θ) :=
      IsLocalization.map_units (Localization.AtPrime P.asIdeal) (⟨θ, hθ⟩ : P.asIdeal.primeCompl)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Module.length_eq_zero
  · intro Q
    have := Q.isMaximal
    rw [length_localization_quotient (Ideal.span {θ}) Q.asIdeal, Ideal.map_span, Set.image_singleton]

end LengthFiniteAlgebra


open LengthFiniteAlgebra in
theorem LengthFiniteAlgebra.proof : LengthFiniteAlgebra.Statement := by
  intro O B _ _ _ _ _ _ θ
  have hr : LinearMap.range (LinearMap.mulLeft O θ) = (Ideal.span {θ}).restrictScalars O := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm]
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  rw [(Submodule.quotEquivOfEq _ _ hr ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {θ})).length_eq,
    length_eq_finsum_localization, finsum_reindex]
  congr 1
  funext P
  exact (ord_mul_length P.asIdeal θ).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem finsum_maximalSpectrum_ord_eq_sum {O B ι : Type*} [CommRing O] [CommRing B] [Algebra O B] (θ : B)
    (S : Finset ι) (c : ι → Ideal B) (hc : Set.BijOn c ↑S {P | P.IsMaximal ∧ θ ∈ P}) (m : ι → ℕ∞)
    (hm : ∀ i ∈ S, ∀ _ : (c i).IsPrime,
      Ring.ord (Localization.AtPrime (c i)) (algebraMap B _ θ) * Module.length O (B ⧸ c i) = m i) :
    ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal) =
      ∑ i ∈ S, m i := by
  classical
  let ψ : Ideal B → ℕ∞ := fun P => if h : P.IsMaximal then
    (haveI := h.isPrime
     Ring.ord (Localization.AtPrime P) (algebraMap B (Localization.AtPrime P) θ) * Module.length O (B ⧸ P))
    else 0
  calc ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)
      = ∑ᶠ 𝔓 ∈ {𝔓 : MaximalSpectrum B | θ ∈ 𝔓.asIdeal},
          Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) *
            Module.length O (B ⧸ 𝔓.asIdeal) := by
        refine finsum_congr fun 𝔓 => ?_
        rw [finsum_eq_if]
        split_ifs with h
        · rfl
        · have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔓.asIdeal) θ) :=
            IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) (Localization.AtPrime 𝔓.asIdeal) ⟨θ, h⟩
          rw [Ring.ord_of_isUnit hu, zero_mul]
    _ = ∑ᶠ P ∈ {P : Ideal B | P.IsMaximal ∧ θ ∈ P}, ψ P :=
        finsum_mem_eq_of_bijOn MaximalSpectrum.asIdeal
          ⟨fun 𝔓 h => ⟨𝔓.isMaximal, h⟩, fun a _ b _ h => MaximalSpectrum.ext h,
            fun P hP => ⟨⟨P, hP.1⟩, hP.2, rfl⟩⟩
          (fun 𝔓 _ => by simp only [ψ, dif_pos 𝔓.isMaximal])
    _ = ∑ᶠ i ∈ (S : Set ι), ψ (c i) := (finsum_mem_eq_of_bijOn c hc fun _ _ => rfl).symm
    _ = ∑ i ∈ S, ψ (c i) := finsum_mem_coe_finset _ _
    _ = ∑ i ∈ S, m i := Finset.sum_congr rfl fun i hi => by
        have hmax : (c i).IsMaximal := (hc.mapsTo (Finset.mem_coe.mpr hi)).1
        simp only [ψ, dif_pos hmax]
        exact hm i hi hmax.isPrime

theorem ChartLength.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegree.Statement) : ChartLength.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrder.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoice.Statement) (h₄ : SpecFirstNe.Statement) (h₅ : LocalizationPrimeDVR.Statement)
    (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement) (h₈ : ChartLocDomain.Statement)
    (h₉ : ChartNorm.Statement) (h₁₀ : ChartLength.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrder.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem EmultiplicityOrd.proof (h₁ : LocalizationPrimeDVR.Statement) : EmultiplicityOrd.Statement := by
  intro R _ _ _ _ q x p _ hq hp hx
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₁ R q p hq hp
  set O := Localization.AtPrime p
  have hfin : FiniteMultiplicity q x := FiniteMultiplicity.of_prime_left hq hx
  obtain ⟨y, hxy, hy⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]

  have hyu : IsUnit (algebraMap R O y) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O p y]
    change y ∉ p
    rw [hp, Ideal.mem_span_singleton]
    exact hy

  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R O q) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hnz : algebraMap R O q ∈ nonZeroDivisors O :=
    mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz,
    Ring.ord_of_irreducible hirr]
  simp

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartIncOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    [(W.map (chartX I t e)).IsPrime]
    [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
    (x : MvPolynomial (Fin n) F),
    Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
        (algebraMap (ChartInc I t e) _ (chartX I t e x)) =
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
        (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) x))

section Inhabitants

theorem isPrime_map_of_sup_ker {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (K : Ideal R) (h : (K ⊔ RingHom.ker f).IsPrime) : (K.map f).IsPrime := by
  have e : K.map f = (K ⊔ RingHom.ker f).map f := by
    rw [Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker f).mpr le_rfl, sup_bot_eq]
  rw [e]
  exact Ideal.map_isPrime_of_surjective hf le_sup_right

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end
