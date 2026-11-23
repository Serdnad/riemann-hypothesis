module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderPullbackInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure MarkedPullbackSquare (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) where
  baseScheme : Scheme.{u}
  topScheme : Scheme.{u}
  bottom : baseScheme ⟶ T.scheme
  structMap : baseScheme ⟶ Spec (CommRingCat.of T.base)
  ideal : baseScheme.IdealSheafData
  mult : ℕ
  boundary : List baseScheme.IdealSheafData
  left : topScheme ⟶ baseScheme
  top : topScheme ⟶ Y
  bottom_structMap : bottom ≫ T.structMap = structMap
  dim_le : krullDimSucc baseScheme ≤ T.krullDimSucc
  isPullback : IsPullback left top bottom g
  valid : (MarkedIdealWithBoundary.mk T.base baseScheme structMap ideal mult boundary).IsAdmissible

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} {g : Y ⟶ T.scheme}

abbrev lowerTriple (S : MarkedPullbackSquare T g) : MarkedIdealWithBoundary.{u} :=
  MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal S.mult S.boundary

abbrev upperTriple (S : MarkedPullbackSquare T g) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (E : List S.topScheme.IdealSheafData) :
    MarkedIdealWithBoundary.{u} :=
  (S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).withBoundary E

theorem orderAt_comap_verticalMap (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g) (A : S.baseScheme.IdealSheafData) (y : ↥S.topScheme) :
    orderAt (A.comap S.left) y = orderAt A (S.left.base y) := by
  have hval :
      (MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal T.mult S.boundary).IsAdmissible :=
    { charZero := S.valid.charZero
      locallyOfFiniteType := S.valid.locallyOfFiniteType
      nonzeroOnComponents := S.valid.nonzeroOnComponents
      one_le_mult := hT.one_le_mult
      quasiCompact := S.valid.quasiCompact
      smooth := S.valid.smooth
      snc := S.valid.snc }
  exact hg S.baseScheme S.bottom S.structMap S.ideal S.boundary hval S.bottom_structMap
    S.topScheme S.left S.top S.isPullback A y

theorem orderAt_comap_verticalMap_le (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g) (A : S.baseScheme.IdealSheafData) (c : ℕ∞)
    (hA : ∀ x : ↥S.baseScheme, orderAt A x ≤ c) (y : ↥S.topScheme) :
    orderAt (A.comap S.left) y ≤ c := by
  rw [S.orderAt_comap_verticalMap hT hg A y]
  exact hA (S.left.base y)

theorem flat_verticalMap (S : MarkedPullbackSquare T g) [AlgebraicGeometry.Flat g] :
    AlgebraicGeometry.Flat S.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) S.isPullback.flip ‹AlgebraicGeometry.Flat g›

end MarkedPullbackSquare

def NonMonomialPartBaseChange (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g) (E : List S.topScheme.IdealSheafData),
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
    (S.upperTriple k' q E).IsAdmissible →
      nonMonomialPart E (S.ideal.comap S.left)
        = (nonMonomialPart S.boundary S.ideal).comap S.left

def PrincipalizationBaseChange (F : PrincipalizationAssignment.{u}) (n : ℕ) (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    (∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) →
    ∀ (E : List S.topScheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
      (S.upperTriple k' q E).IsAdmissible →
      krullDimSucc S.topScheme ≤ n →
        IsPullbackBlowupSequence S.left (F (S.upperTriple k' q E)).toSequenceOfBlowups (F S.lowerTriple).toSequenceOfBlowups

def MonomialPrincipalizationBaseChange (τ : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    MonomialCenter.IsLocallyMonomialTriple S.lowerTriple →
    ∀ (E : List S.topScheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
      MonomialCenter.IsLocallyMonomialTriple (S.upperTriple k' q E) →
        IsPullbackBlowupSequence S.left
          (monomialPrincipalization τ (S.upperTriple k' q E)).toSequenceOfBlowups
          (monomialPrincipalization τ S.lowerTriple).toSequenceOfBlowups

structure BaseChangeCompatible (τ : ComapIsoInvariance.{u}) (F : PrincipalizationAssignment.{u}) (n : ℕ)
    (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) : Prop where
  rule : PrincipalizationBaseChange F n T g k' q
  flat : AlgebraicGeometry.Flat g
  monomialBody : MonomialPrincipalizationBaseChange τ T g k' q
  nonMonomial : NonMonomialPartBaseChange T g k' q
  order : OrderAtPullbackInvariant T g

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem orderAt_controlledTransform_le_of_orderAt_eq_on_center :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
                (∀ x ∈ Z.support, orderAt J x = (c : ℕ∞)) →
                  ∀ (J' : X'.IdealSheafData),
                    Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
                      ∀ x' ∈ (Blowup.exceptionalIdeal π Z).support, orderAt J' x' ≤ (c : ℕ∞) := by
  intro T hT Z hZsm hZsnc X' π hπ J c hJ J' hJ' x' hx'
  have : CharZero T.base := hT.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have hN : AlgebraicGeometry.IsNoetherian T.scheme := hT.isNoetherian
  have hlocNoeth : AlgebraicGeometry.IsLocallyNoetherian T.scheme := inferInstance
  have hLN' : AlgebraicGeometry.IsLocallyNoetherian X' :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  have hsub : (Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus J c := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff J c x).2 (hJ x hx).ge
  have hI : J ≤ Z ^ c :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap Z J T.boundary hZsnc c hsub
  have hJ'eq : J' = controlledTransform π Z J c hπ hI :=
    eq_controlledTransform_of_mul_eq_comap π Z J c hπ hI J' hJ'
  rw [hJ'eq]
  refine orderAt_controlledTransform_le_of_orderAt_image_le T.base T.structMap π Z T.boundary
    hZsnc hπ J c hI x' ?_
  have h1 : π x' ∈ (Z.support : Set ↥T.scheme) :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1
      (by rw [← Blowup.exceptionalIdeal_eq_comap π Z]; exact hx')
  exact le_of_eq (hJ _ h1)

structure StrictTransformAndMonomialCaseHypotheses : Prop where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)
  monomial : MonomialCaseHypotheses.{u}

theorem OrderReductionHypotheses.of_strictTransformHypotheses (h : StrictTransformAndMonomialCaseHypotheses.{u}) :
    OrderReductionHypotheses.{u} := by
  exact {
    controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
    strictTransform_components := h.strictTransform_components
    monomial := h.monomial
  }

end FunctorialResolution.EmbeddedResolution

end
end
