module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle003
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle001
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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

@[expose] public section

section

universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type u) [Field k] [CharZero k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (ι : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
    [AlgebraicGeometry.Smooth (ι ≫ p)]

theorem base_mem_orderAtLeastLocus_of_mem_comap
    (m : ℕ) (hm : 1 ≤ m) (A : X.IdealSheafData) (K : ℕ → X.IdealSheafData)
    (hdom : derivIdealSheafIterate k p (m - 1) A
      ≤ ⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l))
    (hbal : ∀ l < m, K l ^ m ≤ A ^ (m - l))
    (y : S) (hy : y ∈ orderAtLeastLocus (A.comap ι) m) :
    ι.base y ∈ orderAtLeastLocus A m := by
  have hsupp : ι.base y ∈
      (⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)).support := by
    refine mem_support_iSup_le_nat (m - 1)
      (fun l => logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)) (ι.base y) ?_
    intro l hl
    have hlm : l < m := by omega
    have hml : 1 ≤ m - l := by omega
    apply (Scheme.IdealSheafData.mem_support_comap).mp
    refine Scheme.IdealSheafData.support_antitone
      (comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate k p ι (K l) (m - 1 - l)) ?_
    have hpow : ((K l).comap ι) ^ m ≤ (A.comap ι) ^ (m - l) := by
      have h1 : (K l ^ m).comap ι ≤ (A ^ (m - l)).comap ι :=
        Scheme.IdealSheafData.comap_mono ι (hbal l hlm)
      rwa [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow] at h1
    have hy2 : y ∈ orderAtLeastLocus ((K l).comap ι) (m - l) :=
      orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le k (ι ≫ p) ((K l).comap ι) (A.comap ι) l m hlm hpow hy
    have hstep := support_derivIdealSheafIterate_eq_orderAtLeastLocus k (ι ≫ p) ((K l).comap ι) hml
    rw [← hstep] at hy2
    have hexp : m - 1 - l = m - l - 1 := by omega
    rw [hexp]
    exact hy2
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p A hm]
  exact Scheme.IdealSheafData.support_antitone hdom hsupp

end

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem imageIdealSheaf_eq_ker_subschemeι_comp {S X : Scheme.{u}} (f : S ⟶ X) (Z : S.IdealSheafData) :
    imageIdealSheaf f Z = Scheme.Hom.ker (Z.subschemeι ≫ f) :=
  rfl

theorem support_imageIdealSheaf_eq_image_support {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (↑(imageIdealSheaf ι Z).support : Set ↥X) = ⇑ι '' (↑Z.support : Set ↥S) := by
  have hqc : AlgebraicGeometry.QuasiCompact (Z.subschemeι ≫ ι) := inferInstance
  have hcl := AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι
  have hrange : Set.range ⇑Z.subschemeι = (↑Z.support : Set ↥S) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι Z
  have hcomp : Set.range ⇑(Z.subschemeι ≫ ι) = ⇑ι '' (↑Z.support : Set ↥S) := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⇑Z.subschemeι y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hclosed : IsClosed (⇑ι '' (↑Z.support : Set ↥S)) :=
    hcl.isClosedMap _ Z.support.2
  have hsup : (↑(AlgebraicGeometry.Scheme.Hom.ker (Z.subschemeι ≫ ι)).support : Set ↥X)
      = closure (Set.range ⇑(Z.subschemeι ≫ ι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, hsup, hcomp, hclosed.closure_eq]

private theorem exists_iso_ker_subscheme {W X : Scheme.{u}} (g : W ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ e : W ≅ (Scheme.Hom.ker g).subscheme,
      e.hom ≫ (Scheme.Hom.ker g).subschemeι = g :=
  ⟨asIso (Scheme.Hom.toImage g), Scheme.Hom.toImage_imageι g⟩

private theorem smooth_of_smooth_iso_hom_comp {A A' B : Scheme.{u}} (e : A ≅ A') (p : A' ⟶ B)
    (h : AlgebraicGeometry.Smooth (e.hom ≫ p)) : AlgebraicGeometry.Smooth p := by
  have : AlgebraicGeometry.Smooth (e.hom ≫ p) := h
  have h2 : AlgebraicGeometry.Smooth (e.inv ≫ e.hom ≫ p) := inferInstance
  simpa using h2

theorem smooth_imageIdealSheaf_subschemeι_comp {S X B : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (Z : S.IdealSheafData) (f : X ⟶ B)
    (h : AlgebraicGeometry.Smooth (Z.subschemeι ≫ ι ≫ f)) :
    AlgebraicGeometry.Smooth ((imageIdealSheaf ι Z).subschemeι ≫ f) := by
  have : AlgebraicGeometry.IsClosedImmersion (Z.subschemeι ≫ ι) := inferInstance
  obtain ⟨e, he⟩ := exists_iso_ker_subscheme (Z.subschemeι ≫ ι)
  rw [imageIdealSheaf_eq_ker_subschemeι_comp ι Z]
  refine smooth_of_smooth_iso_hom_comp e _ ?_
  rw [← Category.assoc, he, Category.assoc]
  exact h

namespace BlowupSequenceData

theorem projectionToBase_prepend_zero {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = CategoryStruct.id X := by
  rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.prepend_isoObjZero, CategoryTheory.Iso.refl_hom]

theorem projectionToBase_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (t + 1) = d.projectionToBase t := by
  induction t with
  | zero =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (0 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map 0 ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0
    have e2 : (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = (BlowupSequenceData.prepend Z hZ d).isoZero.hom :=
      BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)
    have e3 : (BlowupSequenceData.prepend Z hZ d).isoZero = Iso.refl X :=
      BlowupSequenceData.prepend_isoObjZero Z hZ d
    have e4 : (BlowupSequenceData.prepend Z hZ d).map 0 = d.isoZero.hom :=
      BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d
    have e5 : d.projectionToBase 0 = d.isoZero.hom := BlowupSequenceData.projectionToBase_zero d
    rw [e1, e2, e3, e4, e5]
    exact Category.comp_id _
  | succ n ih =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map (n + 1) ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (n + 1)
    have e2 : (BlowupSequenceData.prepend Z hZ d).map (n + 1) = d.map n :=
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n
    rw [e1, e2, ih]
    exact (BlowupSequenceData.projectionToBase_succ d n).symm

theorem controlledTransform_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)
    (I I₁ : X.IdealSheafData) (m : ℕ)
    (h1 : (BlowupSequenceData.prepend Z hZ d).controlledTransform I m 1 = I₁.comap d.isoZero.hom) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).controlledTransform I m (t + 1) = d.controlledTransform I₁ m t := by
  induction t with
  | zero => exact h1.trans (d.controlledTransform_zero I₁ m).symm
  | succ n ih =>
    rewrite [BlowupSequenceData.controlledTransform_succ (BlowupSequenceData.prepend Z hZ d) I m (n + 1),
      BlowupSequenceData.controlledTransform_succ d I₁ m n, ih,
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n, BlowupSequenceData.prepend_center_succ Z hZ d n]
    rfl

theorem boundary_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)
    (E E₁ : List X.IdealSheafData)
    (h1 : (BlowupSequenceData.prepend Z hZ d).boundaryFrom E 1
      = List.map (fun D => D.comap d.isoZero.hom) E₁) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).boundaryFrom E (t + 1) = d.boundaryFrom E₁ t := by
  induction t with
  | zero =>
      rw [BlowupSequenceData.boundary_zero]
      exact h1
  | succ n ih =>
      rw [BlowupSequenceData.boundary_succ (BlowupSequenceData.prepend Z hZ d) E (n + 1),
        BlowupSequenceData.boundary_succ d E₁ n, ih, BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n,
        BlowupSequenceData.prepend_center_succ Z hZ d n]
      all_goals rfl

end BlowupSequenceData

namespace DivisorReduction

theorem smooth_ambientBlowupSeq_center_comp (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    AlgebraicGeometry.Smooth
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).subschemeι ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)) := by
  have hsm := s.center_smooth t ht
  have hemb := embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t
  have h2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
      = s.projectionToBase t ≫ (divisorEmbedding T j hj I₀ E₀ ≫ T.structMap) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
          (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme) => g ≫ T.structMap)
          hemb).trans (Category.assoc _ _ _))
  have key : AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap))) :=
    Eq.mpr
      (congrArg
        (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ Spec (CommRingCat.of T.base)) =>
          AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫ g)) h2)
      hsm
  exact Eq.mpr
    (congrArg
      (fun Z : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData =>
        AlgebraicGeometry.Smooth (Z.subschemeι ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)))
      (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t))
    (smooth_imageIdealSheaf_subschemeι_comp (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) key)

theorem support_ambientBlowupSeq_center_eq_image (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) =
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ''
        (↑((MarkedBlowupSequenceData.ofMarkedSequence s).center t).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj t)) := by
  have h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t) :=
    ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t
  have h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).center t = s.center t :=
    MarkedBlowupSequenceData.ofMarkedSequence_center s t
  rw [h1, h2]
  exact support_imageIdealSheaf_eq_image_support
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁))
    (hV₁ : (T.withBoundary L₁).IsAdmissible) (hV₂ : (T.withBoundary L₂).IsAdmissible) :
    IsStrictPullbackBlowupSeq (𝟙 T.scheme)
      (((canonicalAlgorithmRules hres).divisorFamily L j₂ (T.withBoundary L₂)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j₁ (T.withBoundary L₁)).toSequenceOfBlowups) := by
  classical
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · have hN : AlgebraicGeometry.IsNoetherian T.scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
    have hN₁ : AlgebraicGeometry.IsNoetherian (T.withBoundary L₁).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₁
    have hN₂ : AlgebraicGeometry.IsNoetherian (T.withBoundary L₂).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₂
    have hflat : AlgebraicGeometry.Flat (𝟙 T.scheme) := inferInstance
    have hjb₁ : j₁ < (T.withBoundary L₁).boundary.length := hj₁
    have hjb₂ : j₂ < (T.withBoundary L₂).boundary.length := hj₂
    have hpre : DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ =
        DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ :=
      DivisorReduction.containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    have hs₁ : _ ∨ _ := hshape j₁ (T.withBoundary L₁) hV₁ hjb₁ hdim hO hbal hcs
    have hs₂ : _ ∨ _ := hshape j₂ (T.withBoundary L₂) hV₂ hjb₂ hdim hO hbal hcs
    simp only [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
    rcases hs₁ with ⟨hZ₁, hpr₁, hmk₁, he₁⟩ | ⟨hZ₁, hb₁, hpr₁, hmk₁, he₁⟩
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₂))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₂))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁)) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hstep
      · exact absurd (hpre.symm.trans hZ₁) hZ₂
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · exact absurd (hpre.trans hZ₂) hZ₁
      · have hcomap : (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
            (𝟙 (T.withBoundary L₁).scheme) =
            DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ := by
          rw [Scheme.IdealSheafData.comap_id]
        have hZZ : DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ =
            (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme) := hpre.symm.trans hcomap.symm
        have hb₁' : Blowup.IsBlowupAlongIdealSheaf (𝟙 (T.withBoundary L₁).scheme)
            ((DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme)) := by
          rw [hcomap]
          exact hb₁
        have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        have hfin : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂) hb₂
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂
                hjb₂ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)).toSequenceOfBlowups
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁) hb₁
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁
                hjb₁ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁)).toSequenceOfBlowups := by
          rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZZ hb₂ hb₁'
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)]
          exact IsStrictPullbackBlowupSeq.prepend hstep _ hb₁ hb₁'
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfin
  · have hcs0 : orderAtLeastLocus T.ideal T.mult = ∅ := Set.not_nonempty_iff_eq_empty.mp hcs
    exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₂ (T.withBoundary L₂) hV₂ hdim hO hbal
        hj₂ hcs0)
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₁ (T.withBoundary L₁) hV₁ hdim hO hbal
        hj₁ hcs0)

theorem strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) :
    DivisorReduction.StrictBoundaryReindexingInvariance hres n L :=
  ⟨fun T hV hdim hO hbal L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂ =>
    isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq hres hfacts hbc hsh n L O hL hshape T hV hdim hO hbal
      L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂⟩

theorem isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  DivisorReduction.isBoundaryPositionInvariant_divisorFamily hres n L
    (strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient hres hfacts hbc hsh n L O hL hshape)

end FunctorialResolution.EmbeddedResolution

end
end
