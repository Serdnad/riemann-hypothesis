module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryAfterBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle004
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem orderAt_le_mult (T : MarkedIdealWithBoundary.{u}) (hOB : T.IsOrderBoundedByMult) (x : ↥T.scheme) :
    orderAt T.ideal x ≤ (T.mult : ℕ∞) := hOB x

private theorem isDerivBalanced_of_isBalanced (T : MarkedIdealWithBoundary.{u})
    (h : AlgebraicGeometry.LocallyOfFiniteType T.structMap) (hbal : T.IsBalanced h) :
    IsDerivBalanced T.base T.structMap T.ideal T.mult := hbal

private theorem mem_support_of_mem_support_comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) {y : ↥Y} (hy : y ∈ (I.comap f).support) : f y ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap] at hy
  exact hy

private theorem disjoint_irreducibleComponents_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        C₁ ≠ C₂ → Disjoint C₁ C₂ := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have h := irreducibleComponentsDisjointOfSmooth
  unfold IrreducibleComponentsDisjointOfSmooth at h
  exact h T.base _ _ hsm

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := by
  have hex : ∃ B, DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * B = T.ideal :=
    exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  have h := pow_mul_residualByPow T.ideal (DivisorReduction.containedComponentsIdeal T j hj) T.mult hex
  simpa [DivisorReduction.lowerIdealAfterBlowup, exceptionalIdeal_id,
    Scheme.IdealSheafData.comap_id] using h

theorem nonzeroOnComponents_comap_lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hOB : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealAfterBlowup T j hj).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    EmbeddedResolution.noetherianSpace_boundary_subscheme T hV j hj
  have hfact : DivisorReduction.containedComponentsIdeal T j hj ^ T.mult *
      DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup T hV j hj
  have horder : ∀ x : ↥T.scheme, orderAt T.ideal x =
      (T.mult : ℕ∞) * orderAt (DivisorReduction.containedComponentsIdeal T j hj) x +
        orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj) x := by
    intro x
    rw [← hfact, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
  rw [nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hx⟩ := hC.1.1
  by_cases hcase : ∀ y ∈ C, (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal T.mult
  · have hsep := disjoint_irreducibleComponents_boundary_subscheme T hV j hj
    have hcc : connectedComponent x ⊆ C :=
      connectedComponent_subset_of_mem_irreducibleComponents hsep hC hx
    have hxrel : x ∈ divisorComponentsInOrderLocus T j hj := by
      intro z hz
      exact hcase z (hcc hz)
    have hopen : IsOpen (divisorComponentsInOrderLocus T j hj) := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
    have hcl : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hZsupp : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
        (DivisorReduction.containedComponentsIdeal T j hj).support := by
      rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen]
      have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
          ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
            ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).support : Set ↥T.scheme) := by
        rw [support_openSubschemeKer _ _ hcl]
        exact ⟨x, hxrel, rfl⟩
      exact hmem
    have hxsupp : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
        (DivisorReduction.lowerIdealAfterBlowup T j hj).support :=
      mem_support_of_mem_support_comap _ _ (hsub hx)
    have h1 : (1 : ℕ∞) ≤ orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι x) :=
      (one_le_orderAt_iff_mem_support _ _).mpr hxsupp
    have h2 : (1 : ℕ∞) ≤ orderAt (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι x) :=
      (one_le_orderAt_iff_mem_support _ _).mpr hZsupp
    have h3 : (T.mult : ℕ∞) + 1 ≤ orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) := by
      calc (T.mult : ℕ∞) + 1 = (T.mult : ℕ∞) * 1 + 1 := by rw [mul_one]
        _ ≤ (T.mult : ℕ∞) * orderAt (DivisorReduction.containedComponentsIdeal T j hj)
              ((T.boundary.get ⟨j, hj⟩).subschemeι x) +
            orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
              ((T.boundary.get ⟨j, hj⟩).subschemeι x) := by
          gcongr
        _ = orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) := (horder _).symm
    have h4 : orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) ≤ (T.mult : ℕ∞) :=
      orderAt_le_mult T hOB _
    have h5 : (T.mult : ℕ∞) + 1 ≤ (T.mult : ℕ∞) := le_trans h3 h4
    have h6 : T.mult + 1 ≤ T.mult := by exact_mod_cast h5
    omega
  · push Not at hcase
    obtain ⟨y, hyC, hy⟩ := hcase
    have hy0 : orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι y) = 0 := by
      by_contra h0
      have hm : 1 ≤ T.mult := by
        by_contra hn
        have : T.mult = 0 := by omega
        apply hy
        rw [mem_orderAtLeastLocus_iff, this]
        exact zero_le
      have hlt : T.mult - 1 < T.mult := by omega
      have hbal' := isDerivBalanced_of_isBalanced T hV.locallyOfFiniteType hbal
      have hpow := IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal' hlt
      have hsub : T.mult - (T.mult - 1) = 1 := by omega
      rw [hsub, pow_one] at hpow
      have hord := orderAt_le_of_le hpow ((T.boundary.get ⟨j, hj⟩).subschemeι y)
      rw [orderAt_pow T.base T.structMap] at hord
      have hne : orderAt (derivIdealSheafIterate T.base T.structMap (T.mult - 1) T.ideal)
          ((T.boundary.get ⟨j, hj⟩).subschemeι y) ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hord
        exact h0 (le_antisymm hord zero_le)
      have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈
          (derivIdealSheafIterate T.base T.structMap (T.mult - 1) T.ideal).support := by
        by_contra hc
        exact hne ((orderAt_eq_zero_iff_not_mem_support _ _).mpr hc)
      apply hy
      rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus T.base T.structMap T.ideal hm]
      exact hmem
    have hle : orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) ≤ 0 := by
      rw [← hy0, horder]
      exact le_add_self
    have hJ0 : orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) = 0 := le_antisymm hle zero_le
    have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈
        (DivisorReduction.lowerIdealAfterBlowup T j hj).support :=
      mem_support_of_mem_support_comap _ _ (hsub hyC)
    rw [← one_le_orderAt_iff_mem_support, hJ0] at hmem
    simp at hmem

theorem isAdmissible_restrictTwistedToDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hOB : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) (_hZ : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤) :
    (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have := hV.smooth
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have := hsm
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : AlgebraicGeometry.QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  exact
    { charZero := hV.charZero
      locallyOfFiniteType := hlft
      nonzeroOnComponents := nonzeroOnComponents_comap_lowerIdealAfterBlowup T hV hOB hbal j hj
      one_le_mult := hV.one_le_mult
      quasiCompact := hqc
      smooth := hsm
      snc := DivisorReductionBoundary.inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup T hV j hj }

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem smooth_of_isPullback (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S) (hpb : IsPullback σ' ψ φ σ) (hφ : AlgebraicGeometry.Smooth φ) :
    AlgebraicGeometry.Smooth ψ :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) hpb hφ

theorem orderAtLeastLocus_comap_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (_hq : h ≫ T.structMap = q) (m : ℕ) :
    orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap T.base T.structMap h T.ideal m

private theorem withBoundary_withBoundary (T : MarkedIdealWithBoundary.{u})
    (E F : List T.scheme.IdealSheafData) :
    (T.withBoundary E).withBoundary F = T.withBoundary F := rfl

private theorem isAdmissible_of_withBoundary_isAdmissible (S : MarkedIdealWithBoundary.{u})
    (E : List S.scheme.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary E)
    (hV : (S.withBoundary E).IsAdmissible) : S.IsAdmissible := by
  have h1 : ((S.withBoundary E).withBoundary S.boundary).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary _ _ hV hBE.symm
  rw [withBoundary_withBoundary, MarkedIdealWithBoundary.withBoundary_self] at h1
  exact h1

theorem isAdmissible_pullbackAlong_of_withBoundary_isAdmissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible := by
  intro T Y q h E' hBE hV
  exact isAdmissible_of_withBoundary_isAdmissible (T.pullbackAlong Y q h) E' hBE hV

theorem containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV'
  have : AlgebraicGeometry.Smooth h := hsm
  have hj' : j < (T.pullbackAlong Y q h).boundary.length := by
    change j < (T.boundary.map (fun D => D.comap h)).length
    simpa only [List.length_map] using hj
  have hVal : (T.pullbackAlong Y q h).IsAdmissible := hvbr T Y q h E' hBE hV'
  rw [containedComponentsIdeal_withBoundary T j Y q h E' hjE hj' htake]
  exact hfacts.preIdeal_pullbackAlong T hV Y q h hq hVal j hj hj'

theorem containedComponentsIdeal_pullbackAlong_of_smooth {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (hfacts : DivisorReductionTerminationProperties hres hno) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h :=
  containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong hfacts
    isAdmissible_pullbackAlong_of_withBoundary_isAdmissible

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem sameNontrivialBoundary_take_eraseIdx_comap {X Y : Scheme.{u}} (p : Y ⟶ X)
    (B : List X.IdealSheafData) (E' : List Y.IdealSheafData) (j : ℕ)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap p) B) E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (List.map (fun D => D.comap p) B))
    (hj : j < B.length) (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E'.eraseIdx j))
      (List.map (fun D => D.comap p) (List.take (B.length - 1) (B.eraseIdx j))) := by
  have hE : List.take (E'.length - 1) (E'.eraseIdx j) = E'.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hjE))
  have hB : List.take (B.length - 1) (B.eraseIdx j) = B.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))
  rw [hE, hB, ← List.eraseIdx_map]
  exact hBE.symm.eraseIdx j htake

private theorem isClosed_setOf_connectedComponent_subset {X : Type u} [TopologicalSpace X]
    (hop : ∀ x : X, IsOpen (connectedComponent x)) (P : Set X) :
    IsClosed {x : X | connectedComponent x ⊆ P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, hop x, mem_connectedComponent⟩
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
  intro hsub
  apply hx
  rw [connectedComponent_eq hy]
  exact hsub

theorem lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E')).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  rw [lowerBoundaryWithoutBlowup_eq ((T.baseChange K f).withBoundary E'), lowerBoundaryWithoutBlowup_eq T]
  exact sameNontrivialBoundary_take_eraseIdx_comap (fieldBaseChangeProjection T K f) T.boundary E' j hBE htake hj hjE

theorem preimageSupportEqComponentsInOrderLocus_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) : PreimageSupportEqComponentsInOrderLocus T j hj := by
  intro h
  have := hV.isNoetherian
  have := FunctorialResolution.Blowup.noetherianSpace_subscheme (T.boundary.get ⟨j, hj⟩)
  have hnsU : TopologicalSpace.NoetherianSpace
      ↥((boundaryComponentsInOrderLocusOpens T j hj h).toScheme) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(boundaryComponentsInOrderLocus T j hj))
  have hqc : AlgebraicGeometry.QuasiCompact
      ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) := by
    constructor
    intro V _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hclosed : IsClosed (boundaryComponentsInOrderLocus T j hj) :=
    isClosed_setOf_connectedComponent_subset
      (fun x => Blowup.isOpen_connectedComponent_of_noetherianSpace _ x) _
  have hinj : Function.Injective ⇑(T.boundary.get ⟨j, hj⟩).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).injective
  have himg : IsClosed (⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj) :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).isClosedMap _ hclosed
  have hU : Set.range ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι = boundaryComponentsInOrderLocus T j hj :=
    Scheme.Opens.range_ι _
  have hcomp : ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
      = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ∘ ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι := by
    funext x
    simp
  have hrange :
      Set.range ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
        = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj := by
    rw [hcomp, Set.range_comp, hU]
  have hsupp : ((AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme)
      = closure (Set.range
          ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [hsupp, hrange, himg.closure_eq]
  exact Set.preimage_image_eq _ hinj

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end
