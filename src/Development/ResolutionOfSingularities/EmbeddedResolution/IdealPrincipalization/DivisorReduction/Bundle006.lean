module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Bundle001
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

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isAdmissible_of_withBoundary_isAdmissible
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible)
    (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hV : (T.withBoundary E').IsAdmissible) : T.IsAdmissible := by
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary (T.withBoundary E').boundary T.boundary := hBE.symm
  have h := hvbr (T.withBoundary E') T.boundary hV hBE'
  have he : (T.withBoundary E').withBoundary T.boundary = T := MarkedIdealWithBoundary.withBoundary_self T
  rwa [he] at h

private theorem containedComponentsIdeal_withBoundary_of_get_eq (S : MarkedIdealWithBoundary.{u})
    (E' : List S.scheme.IdealSheafData) (j : ℕ) (hjE : j < E'.length)
    (hj : j < S.boundary.length)
    (hget : E'.get ⟨j, hjE⟩ = S.boundary.get ⟨j, hj⟩) :
    DivisorReduction.containedComponentsIdeal (S.withBoundary E') j hjE = DivisorReduction.containedComponentsIdeal S j hj := by
  rw [DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal (S.withBoundary E') j hjE,
    DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal S j hj]
  exact congrArg (fun D => DivisorReduction.componentsInOrderLocusIdeal S.ideal S.mult D) hget

private theorem lowerIdealWithoutBlowup_eq_ideal (S : MarkedIdealWithBoundary.{u}) :
    DivisorReduction.lowerIdealWithoutBlowup S = S.ideal := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  simp [Scheme.IdealSheafData.comap_id]

theorem containedComponentsIdeal_withBoundary_baseChange
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
        (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
            DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
              (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) := by
  intro T hV K iK iCZ f E' hBE j hj hjE htake hV'
  have hVb : (T.baseChange K f).IsAdmissible :=
    isAdmissible_of_withBoundary_isAdmissible hvbr (T.baseChange K f) E' hBE hV'
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    rw [List.length_take, List.length_take] at h
    omega
  have hget : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  rw [containedComponentsIdeal_withBoundary_of_get_eq (T.baseChange K f) E' j hjE hj' hget]
  exact hfacts.preIdeal_baseChange T hV K f hVb j hj hj'

theorem lowerIdealWithoutBlowup_withBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      DivisorReduction.lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (DivisorReduction.lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f) := by
  intro T K iK iCZ f E'
  rw [lowerIdealWithoutBlowup_eq_ideal, lowerIdealWithoutBlowup_eq_ideal, MarkedIdealWithBoundary.withBoundary_ideal]
  exact MarkedIdealWithBoundary.baseChange_ideal T K f

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem ker_embeddingIntoAmbientBlowupSequence_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0) =
      (AlgebraicGeometry.Scheme.Hom.ker ι).comap
        (ambientBlowupSequence ι s hres hno hcen).isoZero.hom := by
  have h1 : embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι :=
    embeddingIntoAmbientBlowupSequence_zero ι s hres hno hcen
  have h2 : (AlgebraicGeometry.Scheme.Hom.ker ι).comap
      (ambientBlowupSequence ι s hres hno hcen).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker ι := by
    rw [ambientBlowupSequence_isoObjZero]
    exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  rw [h1, h2]
  exact Scheme.Hom.ker_comp_of_isIso s.isoZero.hom ι

private theorem forall_le_ker_embeddingIntoAmbient_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι) :
    ∀ t : ℕ, t ≤ s.length →
      ∀ hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length,
        AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
          ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ := by
  intro t
  induction t with
  | zero =>
      intro _ hjt
      simp only [List.get_eq_getElem] at hE ⊢
      rw [ker_embeddingIntoAmbientBlowupSequence_zero]
      simp only [BlowupSequenceData.boundary_zero, List.getElem_map, hE]
  | succ n ih =>
      intro hn hjt
      have hn' : n < s.length := hn
      have hjn : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E n).length := by
        rw [BlowupSequenceData.boundary_length]; omega
      rw [ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen n hn', ih (le_of_lt hn') hjn]
      simp only [List.get_eq_getElem, BlowupSequenceData.boundary_succ]
      rw [List.getElem_append_left (by simpa using hjn), List.getElem_map]

theorem ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι)
    (t : ℕ) (ht : t ≤ s.length)
    (hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
      ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ :=
  forall_le_ker_embeddingIntoAmbient_eq_boundary_get ι s hres hno hcen E j hj hE t ht hjt

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

theorem ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr 0) =
      (T.boundary.get ⟨j, hj⟩).comap (pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  exact h0

theorem ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0) =
      ((T.boundary.get ⟨j, hj⟩).comap
          (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0) := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  have hA : (T.boundary.get ⟨j, hj⟩).comap
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0
      = (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).isoZero.hom := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism,
      BlowupSequenceData.prepend_blowupMorphism_zero]
    exact rfl
  rw [hA, hB]
  exact h0

theorem isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hob : T.IsOrderBoundedByMult) (_hbal : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length) (_hpre : containedComponentsIdeal T j hj = ⊤)
    (_hlow : (restrictToDivisor T j hj).IsAdmissible)
    [AlgebraicGeometry.IsNoetherian T.scheme] (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (t : ℕ) (ht : t ≤ s.length) :
    IsSmoothDivisor ((pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
      (AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t)) := by
  have hjt : j < ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).length := by
    rw [BlowupSequenceData.boundary_length]; omega
  have htS : t ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact ht
  have hker : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) =
      ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).get
          ⟨j, hjt⟩ :=
    ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr T.boundary j hj
      (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _).symm t htS hjt
  have hbd : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    exact rfl
  have hpl : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).length =
      s.toSequenceOfBlowups.length := by
    have hh := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length] at hh
    exact hh
  have htlen : t ≤ (pushedMarkedSeq hres hno T j hj s hpr hmk).toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hpl]
    exact ht
  have hsnc := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hV
    (pushedMarkedSeq hres hno T j hj s hpr hmk) t htlen
  have key : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [hker]
    exact List.getElem_mem _
  have key2 : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t := by
    rw [hbd]
    exact key
  exact ((inStrictNormalCrossingPosition_iff _ _).mp hsnc).1 _ key2

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
