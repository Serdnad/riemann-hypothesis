module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem regAt_of_isIntegrallyClosed_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  intro X _ _ p hp y hy f hf
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨y, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_under (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ y := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this

  haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl := by
    ext s; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by
    rw [← hs]; exact hU.isLocalization_stalk z
  let e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X))
      (Localization.AtPrime q)).toRingEquiv
  haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) :=
    ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2
      ⟨inferInstance, inferInstance⟩).2
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by
    have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X)) := krullDimLE_of_coheight_le hc.le
    have hf : ¬ IsField (X.presheaf.stalk (z : X)) := fun h => by
      have := ringKrullDim_eq_zero_of_isField h
      rw [ringKrullDim_stalk_eq_coheight, hc] at this
      simp at this
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
    have h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧
        ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 1 4).mpr h3
  obtain ⟨E, hE⟩ := DivOver.exists_isAt (p := p) (z : X)
  obtain ⟨a, rfl⟩ := (hE f).1 (hf z hzx E hE)
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

end GlobalTheory.Discrepancy
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem kltAt_lcAt_of_specializes (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ) (Γ : X → ℚ) (x z : X) (hzx : z ⤳ x) :
    (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  ⟨fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩,
    fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩⟩

theorem kltAt_lcAt_generisation :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ),
      ∀ (Γ : X → ℚ) (x z : X), z ⤳ x →
        (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  fun X _ _ p n Γ x z h => kltAt_lcAt_of_specializes X p n Γ x z h

end GlobalTheory.Discrepancy
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.MonoOrd

variable {Y : Scheme.{0}} [IsIntegral Y]

def schOrdHom [IsLocallyNoetherian Y] (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem schOrd_prod_zpow [IsLocallyNoetherian Y] {ι : Type} (s : Finset ι)
    (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ s, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ s, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (schOrdHom v) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

theorem schOrd_inv [IsLocallyNoetherian Y] (g : Y.functionFieldˣ) (v : Y) :
    Scheme.ord ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) v =
      - Scheme.ord (g : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_inv (schOrdHom v) g)
  rw [toAdd_inv] at h
  exact h

variable {k : Type} [Field k] {q : Y ⟶ Sp k}

def divOrdHom (E : DivOver q) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (E.ord g)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul, ofAdd_add]

theorem divOrd_prod_zpow (E : DivOver q) {ι : Type} (s : Finset ι) (u : ι → Y.functionFieldˣ)
    (m : ι → ℤ) : E.ord (∏ j ∈ s, u j ^ m j) = ∑ j ∈ s, m j * E.ord (u j) := by
  have h := congrArg Multiplicative.toAdd (map_prod (divOrdHom E) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

end GlobalTheory.Discrepancy.MonoOrd


open GlobalTheory.Discrepancy.MonoOrd in
theorem GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  intro k _ Y _ _ _ q E y hE ι _ w u hw _ _ hself hother φ hφ
  classical
  set a : ι → ℤ := fun j => Scheme.ord (φ : Y.functionField) (w j) with ha
  set ψ : Y.functionFieldˣ := φ * ∏ j, u j ^ (-a j) with hψ
  have hord : ∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (ψ : Y.functionField) v = 0 := by
    intro v hv h1
    rw [hψ, Units.val_mul, Scheme.ord_mul φ.ne_zero (Units.ne_zero _), schOrd_prod_zpow]
    by_cases h : ∃ i, v = w i
    · obtain ⟨i, rfl⟩ := h
      rw [Finset.sum_eq_single i]
      · rw [hself i, ha]
        ring
      · intro j _ hji
        rw [hother j (w i) hv h1 (fun e => hji (hw e.symm)), mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => by rw [hother j v hv h1 (h j), mul_zero],
        hφ v hv h1 h, add_zero]
  have hreg : ∀ g : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (g : Y.functionField) v = 0) →
        0 ≤ E.ord g := fun g hg =>
    (E.ord_nonneg_iff g).2 (hE _ (regAt_of_forall_coheight_eq_one fun z hz h1 =>
      (GlobalTheory.RegCodimOne.regAt_iff_ord_nonneg h1 g.ne_zero).2 (hg z hz h1).ge))
  have h0 := hreg ψ hord
  have h0' := hreg ψ⁻¹ fun v hv h1 => by rw [schOrd_inv, hord v hv h1, neg_zero]
  rw [E.ord_inv] at h0'
  have hψ0 : E.ord ψ = 0 := by omega
  rw [hψ, E.ord_mul, divOrd_prod_zpow] at hψ0
  simp only [neg_mul, Finset.sum_neg_distrib] at hψ0
  rw [ha] at hψ0
  linarith
end
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.MoyalPointwise

variable {l : Type} [Fintype l]

def ambU (g g' : Sch l) (p : EuclideanSpace ℝ l) : Sch l :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) g'.hasTemperateGrowth
    (SchwartzMap.compSubConstCLM ℂ (-p) (GlobalTheory.ConjSch.conjSch g))

theorem ambU_apply (g g' : Sch l) (p t : EuclideanSpace ℝ l) :
    ambU g g' p t = starRingEnd ℂ (g (t + p)) * g' t := by
  simp [ambU, SchwartzMap.bilinLeftCLM_apply, GlobalTheory.ConjSch.conjSch_apply, sub_neg_eq_add]

end GlobalTheory.MoyalPointwise

noncomputable section

namespace GlobalTheory.MoyalPointwise

open Complex
open scoped Real RealInnerProductSpace FourierTransform

variable {l : Type} [Fintype l]

theorem integrand_eq (g g' f : Sch l) (x : EuclideanSpace ℝ l) (w : l ⊕ l → ℝ) :
    starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      cexp (((2 * π * ⟪qPart w, x⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' (pPart w)) (qPart w) * f (x + pPart w) := by
  have h1 : ∀ t, starRingEnd ℂ (rhoFun w ⇑g t * starRingEnd ℂ (g' t)) =
      cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) *
        (cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) • ambU g g' (pPart w) t) := by
    intro t
    rw [ambU_apply, smul_eq_mul, rhoFun, phase, map_mul, map_mul, Complex.conj_conj, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    have e : cexp (((2 * π * ⟪qPart w, t⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * -I) =
        cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) * cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add, real_inner_comm t (qPart w)]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  have h2 : 𝓕 (ambU g g' (pPart w)) (qPart w) =
      ∫ t, cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) • ambU g g' (pPart w) t := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  have h3 : starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) =
      cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' (pPart w)) (qPart w) := by
    rw [← integral_conj, integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul, h2]
  have key : cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) *
      cexp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) =
      cexp (((2 * π * ⟪qPart w, x⟫ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h3, rhoFun, phase]
  linear_combination (𝓕 (ambU g g' (pPart w)) (qPart w) * f (x + pPart w)) * key

theorem measurePreserving_pq :
    MeasurePreserving (fun w : l ⊕ l → ℝ => (pPart w, qPart w)) volume volume ∧
      MeasurableEmbedding (fun w : l ⊕ l → ℝ => (pPart w, qPart w)) := by
  let e : (l ⊕ l → ℝ) ≃ᵐ EuclideanSpace ℝ l × EuclideanSpace ℝ l :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : l ⊕ l => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (l → ℝ)) (MeasurableEquiv.toLp 2 (l → ℝ)))
  have he : ⇑e = fun w : l ⊕ l → ℝ => (pPart w, qPart w) := rfl
  rw [← he]
  refine ⟨?_, e.measurableEmbedding⟩
  exact ((PiLp.volume_preserving_toLp l).prod (PiLp.volume_preserving_toLp l)).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : l ⊕ l => ℝ))

theorem integral_phase_fourier (u : Sch l) (x : EuclideanSpace ℝ l) :
    ∫ q, cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * 𝓕 u q = u x := by
  have h := congrFun (u.continuous.fourierInv_fourier_eq u.integrable (𝓕 u).integrable) x
  rw [Real.fourierInv_eq'] at h
  simpa [SchwartzMap.fourier_coe] using h

theorem moyal_pointwise : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  intro n f g g' x
  obtain ⟨hmp, hme⟩ := measurePreserving_pq (l := Fin n)
  set G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℂ := fun z =>
    cexp (((2 * π * ⟪z.2, x⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' z.1) z.2 * f (x + z.1) with hG
  have hI : (fun w : Fin n ⊕ Fin n → ℝ =>
      starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x) =
      G ∘ fun w => (pPart w, qPart w) := by
    funext w
    exact integrand_eq g g' f x w
  have hint : Integrable (fun w : Fin n ⊕ Fin n → ℝ =>
      starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x) := by
    obtain ⟨hc, hd⟩ := GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g'
    obtain ⟨C, hC⟩ := hd (2 * n + 1)
    have hr : (Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      push_cast
      linarith
    have hB := (integrable_one_add_norm (E := Fin n ⊕ Fin n → ℝ) (μ := volume) hr).const_mul
      (C * SchwartzMap.seminorm ℂ 0 0 f)
    have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
      unfold pPart; fun_prop
    have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
      unfold qPart; fun_prop
    have hcont : Continuous (fun w : Fin n ⊕ Fin n → ℝ => rhoFun w ⇑f x) := by
      simp only [rhoFun, phase]
      have := f.continuous
      fun_prop
    refine hB.mono' (((Complex.continuous_conj.comp hc).mul hcont).aestronglyMeasurable)
      (.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ ≤ C * (1 + ‖w‖) ^ (-((2 * n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos _)]
      exact hC w
    have e2 : ‖f (x + pPart w)‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := SchwartzMap.norm_le_seminorm ℂ f _
    simp only [Function.comp_apply, norm_mul, RCLike.norm_conj, rhoFun, norm_phase, one_mul]
    calc _ ≤ C * (1 + ‖w‖) ^ (-((2 * n + 1 : ℕ) : ℝ)) * SchwartzMap.seminorm ℂ 0 0 f :=
          mul_le_mul e1 e2 (norm_nonneg _) (le_trans (norm_nonneg _) e1)
      _ = _ := by ring
  have hGint : Integrable G := (hmp.integrable_comp_emb hme).1 (hI ▸ hint)
  calc _ = ∫ w : Fin n ⊕ Fin n → ℝ, G (pPart w, qPart w) := by rw [hI]; rfl
    _ = ∫ z, G z := hmp.integral_comp hme G
    _ = ∫ p, ∫ q, G (p, q) := integral_prod G hGint
    _ = ∫ p, starRingEnd ℂ (g (x + p)) * g' x * f (x + p) := by
        congr 1
        funext p
        dsimp only [G]
        rw [integral_mul_const, integral_phase_fourier, ambU_apply]
    _ = ∫ p, (fun y => f y * starRingEnd ℂ (g y)) (x + p) * g' x := by
        congr 1
        funext p
        ring
    _ = _ := by
        rw [integral_mul_const]
        exact congrArg (· * g' x) (integral_add_left_eq_self (fun y => f y * starRingEnd ℂ (g y)) x)

end GlobalTheory.MoyalPointwise
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_of_lie_intertwine_l2 : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  first | exact @GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound | exact GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound | (intros; apply GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.derived_action_intertwines_of_group : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w (f f' : GlobalTheory.RealWeil.Sch l), ⇑f' = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(A' f') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' f)) →
    ∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f) := by
  first | exact @GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine | exact GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine | (intros; apply GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardAddChar_archimedean_exp_realLinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    ∃ β : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧
      ∀ a, β a = -(∑ ρ, θ ρ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) ⊗ₜ[D.host.F]
        (1 : D.host.E))).re := by
  exact @GlobalTheory.StdCharLin.stdChar_mixed_linear
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adelicSide_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  first | exact @GlobalTheory.AdelicSide.exists_thAd_of_models | exact GlobalTheory.AdelicSide.exists_thAd_of_models | (intros; apply GlobalTheory.AdelicSide.exists_thAd_of_models <;> assumption)
end
