module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.of_intNumBase_cutRational
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.proof VocabMultiHomog.proof
    (VocabMultiHomogIdeal.proof VocabMultiHomog.proof) VocabDivCycle.proof
    (IntNumPoint.proof hBase) (IntNumRatSection.proof hCut)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [Algebra O Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra O Φ]
  [IsScalarTower O Ω Φ]

theorem segreVec_algebraMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreVec (fun p => algebraMap Ω Φ (y p)) c = algebraMap Ω Φ (segreVec y c) := by
  simp [segreVec, map_prod]

theorem algebraMap_mem_chartRing_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {z : Ω}
    (hz : z ∈ chartRing O (segreVec y) c) :
    algebraMap Ω Φ z ∈ chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c := by
  have hle : chartRing O (segreVec y) c ≤
      (chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c).comap
        (IsScalarTower.toAlgHom O Ω Φ) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    show algebraMap Ω Φ (segreVec y j / segreVec y c) ∈
      chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c
    rw [map_div₀, ← segreVec_algebraMap, ← segreVec_algebraMap]
    exact div_mem_chartRing _ _ _
  exact hle hz

end Lemmas

theorem eq_repr_smul_basis_first {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (w : Module.Basis (Fin N) Ω E) (h0 : 0 < N) (v : E)
    (hv : ∀ j : Fin N, (⟨0, h0⟩ : Fin N) < j → w.repr v j = 0) :
    v = w.repr v ⟨0, h0⟩ • w ⟨0, h0⟩ := by
  conv_lhs => rw [← w.sum_repr v]
  refine Finset.sum_eq_single _ (fun j _ hj => ?_) (by simp)
  have hlt : (⟨0, h0⟩ : Fin N) < j := by
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    show 0 < (j : ℕ)
    omega
  rw [hv j hlt, zero_smul]

theorem SegreFlagClosureBirational.proof : SegreFlagClosureBirational.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t _ hN c hc c₁ c₂ hc₂
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  have hcΩ : segreVec y c ≠ 0 := by
    intro h
    apply hc
    rw [segreVec_algebraMap, h, map_zero]
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcΩ k (Finset.mem_univ k)
  have hpow : ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)

  have hmem : ∏ k, y ⟨k, c k⟩ ^ x i0 k ∈ degLat O y (x i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag.graded c hcΩ i0] at hmem
  obtain ⟨v, hv, hvj, hv0⟩ := hmem
  have hmem' : ∏ k, y ⟨k, c k⟩ ^ x' i0 k ∈ degLat O y (x' i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag'.graded c hcΩ i0] at hmem'
  obtain ⟨v', hv', hvj', hv0'⟩ := hmem'
  have hv_eq : v = (∏ k, y ⟨k, c k⟩ ^ x i0 k) • w i0 := by
    rw [← hv0]; exact eq_repr_smul_basis_first w hN v hvj
  have hv'_eq : v' = (∏ k, y ⟨k, c k⟩ ^ x' i0 k) • w' i0 := by
    rw [← hv0']; exact eq_repr_smul_basis_first w' hN v' hvj'
  have hw' : w' i0 = w.repr (w' i0) i0 • w i0 :=
    eq_repr_smul_basis_first w hN (w' i0) fun j hj => hF.sameFlag i0 j hj
  set u : Ω := w.repr (w' i0) i0 with hudef
  have hu : u ≠ 0 := by
    intro h
    apply w'.ne_zero i0
    rw [hw', h, zero_smul]

  choose α hα hαeq using fun l => hφ.sections c hcΩ l v hv
  choose β hβ hβeq using fun l => hφ'.sections c hcΩ l v' hv'
  set D : Ω := (∏ k, y ⟨k, c k⟩ ^ x i0 k) * ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u) with hDdef
  set G : Ω := (∏ k, y ⟨k, c k⟩ ^ a₀ k) * ∏ k, y ⟨k, c k⟩ ^ a₀' k with hGdef
  have hD : D ≠ 0 := mul_ne_zero (hpow _) (mul_ne_zero (hpow _) hu)
  have hprod : ∀ (l : Fin M) (m : Fin M'), D * (φ l (w i0) * φ' m (w i0)) = G * (α l * β m) := by
    intro l m
    have hA : (∏ k, y ⟨k, c k⟩ ^ x i0 k) * φ l (w i0) = α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k := by
      rw [← hαeq l, hv_eq, map_smul, smul_eq_mul]
    have hB : (∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0) =
        β m * ∏ k, y ⟨k, c k⟩ ^ a₀' k := by
      rw [← hβeq m, hv'_eq, hw', smul_smul, map_smul, smul_eq_mul]
    rw [hDdef, hGdef]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0)) * hA +
      (α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k) * hB
  have hprodΦ : ∀ (l : Fin M) (m : Fin M'),
      algebraMap Ω Φ D * (algebraMap Ω Φ (φ l (w i0)) * algebraMap Ω Φ (φ' m (w i0))) =
        algebraMap Ω Φ G * (algebraMap Ω Φ (α l) * algebraMap Ω Φ (β m)) := by
    intro l m
    have := congrArg (algebraMap Ω Φ) (hprod l m)
    simpa only [map_mul] using this

  set T : Φ := ∑ i, t i * algebraMap Ω Φ (w.repr (e i) i0) with hT
  have hfc : ∀ j : Fin N, j ≠ i0 → flagCoord w e t 1 j = 0 := by
    intro j hj
    have : ¬ ((j : ℕ) < 1) := by
      intro h
      apply hj
      ext
      simp only [hi0]
      omega
    simp [flagCoord, this]
  have hfc0 : flagCoord w e t 1 i0 = T := by simp [flagCoord, hi0, hT]
  have hsome : ∀ l : Fin M, flagLinePt w e φ φ' t 1 ⟨some (), l⟩ = T * algebraMap Ω Φ (φ l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hnone : ∀ l : Fin M', flagLinePt w e φ φ' t 1 ⟨none, l⟩ = T * algebraMap Ω Φ (φ' l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ' l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hseg : ∀ c' : ∀ o, lineBlocks M M' o, segreVec (flagLinePt w e φ φ' t 1) c' =
      (T * algebraMap Ω Φ (φ' (c' none) (w i0))) * (T * algebraMap Ω Φ (φ (c' (some ())) (w i0))) := by
    intro c'
    rw [segreVec, Fintype.prod_option, Fintype.prod_unique]
    exact congrArg₂ (· * ·) (hnone (c' none)) (hsome (c' (some ())))

  refine ⟨algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)),
    algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)), ?_, ?_⟩
  · intro h0
    apply hc₂
    have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only [mul_zero]
    rw [hseg]
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * h2 + T ^ 2 * algebraMap Ω Φ G * h0
  · have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only
    rw [hseg, hseg]
    have h1 := hprodΦ (c₁ (some ())) (c₁ none)
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * (algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none))) * h1 -
      T ^ 2 * (algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none))) * h2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem length_self_eq_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

private theorem length_localizedModule_quot {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem LocCycleLocalQuot.proof (h₂ : LocalQuotPrimes.Statement.{u}) : LocCycleLocalQuot.Statement.{u} := by
  intro R _ P U _ J W hPJ hW hPW hWU
  obtain ⟨hup, hdown⟩ := h₂ R P U (hPW.trans hWU)
  obtain ⟨hpW, hcW⟩ := hup W hW hPW hWU

  have hmin : W ∈ J.minimalPrimes ↔ W.map (localQuotMap P U) ∈ (J.map (localQuotMap P U)).minimalPrimes := by
    constructor
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hpW, Ideal.map_mono hJW⟩, fun q hq hqW => ?_⟩
      have := hq.1
      obtain ⟨hPq, hqU, hqe⟩ := hdown q hq.1
      have h := hm ⟨Ideal.comap_isPrime _ q, Ideal.le_comap_map.trans (Ideal.comap_mono hq.2)⟩
        ((Ideal.comap_mono hqW).trans hcW.le)
      rw [← hqe]
      exact Ideal.map_mono h
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hW, Ideal.le_comap_map.trans ((Ideal.comap_mono hJW).trans hcW.le)⟩, fun Q hQ hQW => ?_⟩
      obtain ⟨hQp, hQc⟩ := hup Q hQ.1 (hPJ.trans hQ.2) (hQW.trans hWU)
      have h := hm ⟨hQp, Ideal.map_mono hQ.2⟩ (Ideal.map_mono hQW)
      rw [← hcW, ← hQc]
      exact Ideal.comap_mono h
  unfold locCycle
  by_cases h : W ∈ J.minimalPrimes
  swap
  · rw [dite_eq_right h, dite_eq_right (mt hmin.2 h)]
  rw [dite_eq_left h, dite_eq_left (hmin.1 h)]
  have := hW
  have := hpW
  set φ := localQuotMap P U with hφ
  obtain ⟨p, hp⟩ : ∃ p, W.map φ = p := ⟨_, rfl⟩
  rw [hp] at hpW hcW
  have := hpW
  have hφp : ∀ x : R, φ x ∈ p ↔ x ∈ W := fun x => by rw [← Ideal.mem_comap, hcW]

  have hrep : ∀ a : localQuot P U, ∃ r u : R, u ∉ U ∧ a * φ u = φ r := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b
    refine ⟨r, u, u.2, ?_⟩
    simp only [hφ, localQuotMap, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hnum : ∀ (t : localQuot P U) (r' u' : R), t ∉ p → u' ∉ U → t * φ u' = φ r' → r' ∉ W := by
    intro t r' u' ht hu' hr' hmem
    rw [← hφp, ← hr'] at hmem
    rcases hpW.mem_or_mem hmem with h | h
    · exact ht h
    · exact hu' (hWU ((hφp u').1 h))
  let ψ : (Localization.AtPrime W) →+* (Localization.AtPrime p) := Localization.localRingHom W p φ hcW.symm
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨r, u, hu, hr⟩ := hrep a
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hs : r' * u ∈ W.primeCompl :=
      W.primeCompl.mul_mem (hnum t r' u' t.2 hu' hr') fun h => hu (hWU h)
    refine ⟨IsLocalization.mk' _ (r * u') ⟨r' * u, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    linear_combination (φ r) * hr' - (φ r') * hr

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap R (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hr'W := hnum t r' u' ht hu' hr'
    have h0 : φ (r' * r) = 0 := by
      rw [map_mul, ← hr', mul_right_comm, htr, zero_mul]
    rw [hφ, localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      IsLocalization.mem_map_algebraMap_iff U.primeCompl] at h0
    obtain ⟨⟨⟨i, hi⟩, v⟩, hv⟩ := h0
    rw [← map_mul, IsLocalization.eq_iff_exists U.primeCompl] at hv
    obtain ⟨c, hc⟩ := hv
    have hcW : (c : R) * r' * v ∈ W.primeCompl :=
      W.primeCompl.mul_mem (W.primeCompl.mul_mem (fun h => c.2 (hWU h)) hr'W) fun h => v.2 (hWU h)
    have hmemP : (c : R) * r' * v * r ∈ P := by
      have : (c : R) * (r' * r * v) = c * r' * v * r := by ring
      rw [← this, hc]
      exact P.mul_mem_left _ hi
    have hrJ : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, hcW⟩), ← map_mul]
      exact Ideal.mem_map_of_mem _ (hPJ hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  let : CommRing (Localization.AtPrime p) := inferInstance
  have hcomp : ψ.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (localQuot P U) (Localization.AtPrime p)).comp φ :=
    RingHom.ext fun x => Localization.localRingHom_to_map W p φ hcW.symm x
  have hI : (J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)) = (J.map (algebraMap R (Localization.AtPrime W))).map ψ := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  let g := (Ideal.Quotient.mk ((J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)))).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [← length_localizedModule_quot, ← length_localizedModule_quot] at key
  subst hp
  exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem mem_minimalPrimes_of_locCycle_ne_zero {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dite_eq_right hc])

theorem LocalCoeffRing.proof (h₁ : LocalQuotRing.Statement.{u}) (h₂ : LocalQuotPrimes.Statement.{u})
    (h₃ : LocCycleLocalQuot.Statement.{u}) (h₄ : LocalQuotColon.Statement.{u})
    (h₅ : LocalQuotFinsum.Statement.{u}) (h₆ : LocalCoeffLocal.Statement.{u}) :
    LocalCoeffRing.Statement.{u} := by
  intro R _ _ P U hP hU hPU hchain f g s u v hf hg hs hu huv hno
  have := hU
  obtain ⟨hdom, hloc, hunit, hker⟩ := h₁ R P U hP hPU
  have := hdom
  have := hloc
  obtain ⟨hup, hdown⟩ := h₂ R P U hPU
  have hmin := fun {J W : Ideal R} (h : locCycle J W ≠ 0) => mem_minimalPrimes_of_locCycle_ne_zero h
  have hmin' := fun {J W : Ideal (localQuot P U)} (h : locCycle J W ≠ 0) =>
    mem_minimalPrimes_of_locCycle_ne_zero h

  have hm : IsLocalRing.maximalIdeal (localQuot P U) = U.map (localQuotMap P U) := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not]
  have hUc : (U.map (localQuotMap P U)).comap (localQuotMap P U) = U := (hup U hU hPU le_rfl).2
  have hPbot : P.map (localQuotMap P U) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr fun y hy => RingHom.mem_ker.mpr ((hker y).2 hy)
  have hmapx : ∀ x : R, (P ⊔ Ideal.span {x}).map (localQuotMap P U) =
      Ideal.span {localQuotMap P U x} := by
    intro x
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hPbot, bot_sup_eq]

  have hchain' : ∀ Q₁ Q₂ : Ideal (localQuot P U), Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ →
      Q₂ < IsLocalRing.maximalIdeal (localQuot P U) → False := by
    intro Q₁ Q₂ hQ₁ hQ₂ h0 h12 h2m
    obtain ⟨hP1, -, he1⟩ := hdown Q₁ hQ₁
    obtain ⟨-, hU2, he2⟩ := hdown Q₂ hQ₂
    exact hchain _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _)
      (lt_of_le_of_ne hP1 fun h => h0.ne (by rw [← he1, ← h, hPbot]))
      (lt_of_le_of_ne (Ideal.comap_mono h12.le) fun h => h12.ne (by rw [← he1, ← he2, h]))
      (lt_of_le_of_ne hU2 fun h => h2m.ne (by rw [← he2, h, hm]))
  have hne : ∀ x : R, x ∉ P → localQuotMap P U x ≠ 0 := fun x hx h => hx ((hker x).1 h)
  have hloc' := h₆ (localQuot P U) hchain' (localQuotMap P U f) (localQuotMap P U g)
    (localQuotMap P U s) (localQuotMap P U u) (localQuotMap P U v) (hne f hf) (hne g hg) (hne s hs)
    ((hunit _).2 fun h => hu (hUc ▸ Ideal.mem_comap.mpr h))
    (by rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]; exact (hker _).2 huv) ?_
  swap
  ·
    intro W hW
    have hWm := hmin' hW
    have := hWm.1.1
    obtain ⟨hPW, hWU, hWe⟩ := hdown W hWm.1.1
    have h := hno (W.comap (localQuotMap P U)) hWU
    rw [h₃ R P U _ _ le_sup_left inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {f}) _ le_sup_left
      inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {g}) _ le_sup_left inferInstance hPW hWU,
      hmapx, hmapx, hmapx, hWe] at h
    exact h hW
  rw [hm] at hloc'
  convert hloc' using 1
  ·
    apply h₅ R P U hPU
    · intro G hG
      have hGU : G ≤ U := le_sup_left.trans (hmin (right_ne_zero_of_mul hG)).1.2
      have h2 := left_ne_zero_of_mul hG
      by_cases h : locCycle (P ⊔ Ideal.span {f}) G = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact ⟨(hmin h2).1.1, le_sup_left.trans (hmin h2).1.2, hGU⟩
      · exact ⟨(hmin h).1.1, le_sup_left.trans (hmin h).1.2, hGU⟩
    · intro p hp
      have h2 := left_ne_zero_of_mul hp
      by_cases h : locCycle (Ideal.span {localQuotMap P U f}) p = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact (hmin' h2).1.1
      · exact (hmin' h).1.1
    · intro G hG hPG hGU
      rw [h₃ R P U _ G le_sup_left hG hPG hGU, h₃ R P U (P ⊔ Ideal.span {g}) G le_sup_left hG hPG hGU,
        h₃ R P U (G ⊔ Ideal.span {s}) U (le_sup_of_le_left hPG) hU hPU le_rfl, hmapx, hmapx,
        Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ·
    apply h₅ R P U hPU
    · intro W hW
      have h1 := hmin (left_ne_zero_of_mul hW)
      have h2 := hmin (right_ne_zero_of_mul hW)
      exact ⟨h1.1.1, le_sup_left.trans h1.1.2, le_sup_left.trans h2.1.2⟩
    · intro p hp
      exact (hmin' (left_ne_zero_of_mul hp)).1.1
    · intro W hW hPW hWU
      rw [h₃ R P U _ W le_sup_left hW hPW hWU, h₃ R P U (W ⊔ _) U (le_sup_of_le_left hPW) hU hPU le_rfl,
        hmapx, Ideal.map_sup, h₄ R P U f g]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open Classical in
def SegreFlagCutDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsMultiHomog s cs → IsMultiHomog h ch →
      (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
      s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
      ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
        ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W = if 0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k) then 1 else 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
