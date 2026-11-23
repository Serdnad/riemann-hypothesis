module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle005
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle002
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerDimensionSmoothPullback
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem filter_map_eq_of_filter_eq {α : Type*} (p : α → Bool) (g : α → α)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List α}
    (hAB : List.filter p A = List.filter p B) :
    List.filter p (A.map g) = List.filter p (B.map g) := by
  have key : ∀ L : List α,
      List.filter p (L.map g) = List.filter p ((List.filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        have hga : p (g a) = false := hpg a ha'
        simp [ha', hga, ih]
  rw [key A, key B, hAB]

private theorem sameNontrivialBoundary_map {X : Scheme.{u}} (g : X.IdealSheafData → X.IdealSheafData)
    (hg : g ⊤ = ⊤) {A B : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (A.map g) (B.map g) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  unfold MarkedIdealWithBoundary.nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

private theorem sameNontrivialBoundary_take_eraseIdx_strictTransform {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A B : List X.IdealSheafData) (a b : ℕ) (ha : a < A.length) (hb : b < B.length)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (A.eraseIdx a) (B.eraseIdx b)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (A.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) A)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (List.take (B.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤
      = (⊤ : X.IdealSheafData) := by
    show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length →
      List.take (C.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c)
        = List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (List.map (fun D : X.IdealSheafData =>
        Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1 := by
      rw [List.length_map]
      exact List.length_eraseIdx_of_lt hc
    have hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length := by
      intro f
      rw [List.length_map]
      exact hc
    simp only [List.map_map, Function.comp_def]
    rw [List.eraseIdx_append_of_lt_length (hmap _)]
    rw [List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
    hgtop h

theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  rfl

theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
      (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁)) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform
    (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE

theorem boundaryReindexingInvariance : BoundaryReindexingInvariance.{u} :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

structure DivisorReductionHypotheses (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : Prop where
  trivial_of_coSupport_empty :
    ∀ (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      j < T.boundary.length →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h],
        h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          (orderAtLeastLocus T.ideal T.mult).Nonempty →
          orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
          ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
            IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  baseChange : SmoothPullbackCompatibility.{u}
  smoothImpliesFlat : FlatOfSmooth.{u}
  degenerateTransversal : EmptyPulledBackCenterCompatibility.{u}
  fieldBaseChangeCompatibility : FieldBaseChangeCompatibility.{u}
  boundaryReindexingInvariance : BoundaryReindexingInvariance.{u}
  fieldLower : DivisorRestrictionFieldBaseChange.{u}
  divisorReduction : DivisorReductionStepProperties hres blowupPreservesNoetherian
  pushedBlowupSequenceProperties : PushedBlowupSequenceProperties hres blowupPreservesNoetherian

theorem DivisorReductionHypotheses.divisorReductionTerminationProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) :
    DivisorReductionTerminationProperties hres blowupPreservesNoetherian :=
  hin.divisorReduction.toDivisorReductionTerminationProperties

theorem DivisorReductionHypotheses.trivialPullbackBlowupSequence {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups hres L j
    (fun T hV hj Y q h _ hq E' hV' hcs hcs' B' hB' =>
      hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hcs' B' hB')

theorem DivisorReductionHypotheses.divisorReductionSeqEqAmbient {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (_hL : IsMaxOrderReduction (fun d => d < n) L O) :
    ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj := by
  intro j T hV hj _hdim hO hD hcs
  have : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have h := divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReductionTerminationProperties L j T hV hj hO hD hcs.ne_empty
  rcases h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩
  · exact Or.inl ⟨hZ, hpr, hmk, hstep hmk⟩
  · exact Or.inr ⟨hZ, hb, hpr, hmk, hstep hmk⟩

end DivisorReduction

private theorem strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.StrictPullbackOfSmoothBaseChangeOnDivisor n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'

theorem isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      ∀ (j : ℕ),
        IsBoundaryDivisorReduction (fun d => d ≤ n) j ((canonicalAlgorithmRules hres).divisorFamily L j) L := by
  intro n L O hL j
  have hshapeN : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs
  have hshapeE : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs =>
      hshapeN T hV hj hdim hO hbal (Set.nonempty_iff_ne_empty.mpr hcs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake
      hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties
      hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E'
      hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj i hi x
    exact divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReductionTerminationProperties n L j T hV hdim hO hbal hj i hi x
  · intro T hV hdim hO hbal hj i hi
    exact divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO hbal
      hj i hi
  · intro T hV hdim hO hbal hj hm J hVJ hdimJ him
    exact isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO
      (fun _ => hbal) hj hm J hVJ hdimJ him
  · intro T hV hdim hO hbal hj
    obtain ⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO
        hbal hj
    refine ⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩
    · intro t ht hb
      exact h5 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
    · intro t ht hb
      exact h7 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
  · intro T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j (hin.trivialPullbackBlowupSequence L j)
      (restrictedSmoothPullback_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
        hin.degenerateTransversal n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j
      (strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj hcs
    exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs

theorem isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  fun n L O hL =>
    isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hin.divisorReductionTerminationProperties hin.baseChange hin.boundaryReindexingInvariance
      n L O hL (hin.divisorReductionSeqEqAmbient n L O hL)

end FunctorialResolution.EmbeddedResolution

end
end
