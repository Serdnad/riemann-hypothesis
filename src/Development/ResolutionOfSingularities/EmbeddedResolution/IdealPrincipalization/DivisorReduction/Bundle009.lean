module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SubschemeMapFlatness
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle005
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle007
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle004
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle002
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantSucc
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isIrreducible_connectedComponent_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (z : ↥(T.boundary.get ⟨j, hj⟩).subscheme) :
    IsIrreducible (connectedComponent z) := by
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    isSmoothDivisor_boundary_get T hV j hj
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp hsd).2
  have hsep := irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have h1 : connectedComponent z ⊆ irreducibleComponent z :=
    connectedComponent_subset_of_mem_irreducibleComponents hsep
      (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent
  have h2 : irreducibleComponent z ⊆ connectedComponent z :=
    (isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

theorem openSubschemeKer_comap_of_flat_of_noetherian {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (D : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (hirr : ∀ w : ↥D.subscheme, IsIrreducible (connectedComponent w))
    (hN : TopologicalSpace.NoetherianSpace ↥D.subscheme)
    (hN' : TopologicalSpace.NoetherianSpace ↥(D.comap g).subscheme)
    (hopen : IsOpen {w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A})
    (hopen' : IsOpen {w : ↥(D.comap g).subscheme |
      connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}) :
    openSubschemeKer (D.comap g)
        ⟨{w : ↥(D.comap g).subscheme |
            connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}, hopen'⟩ =
      (openSubschemeKer D
        ⟨{w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A}, hopen⟩).comap g := by
  have := hN
  have := hN'
  exact openSubschemeKer_comap g D A hA ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥D.subscheme
      (⇑D.subschemeι.base ⁻¹' A))
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
      ↥(D.comap g).subscheme
      (⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A))) hirr

private theorem get_eq_comap_get_of_eq_map {X Y : Scheme.{u}} (g : Y ⟶ X) (E : List X.IdealSheafData)
    (F : List Y.IdealSheafData) (hF : F = E.map (fun D => D.comap g)) (j : ℕ)
    (hj : j < E.length) (hj' : j < F.length) :
    F.get ⟨j, hj'⟩ = (E.get ⟨j, hj⟩).comap g := by
  subst hF
  simp [List.get_eq_getElem]

private theorem containedComponentsIdeal_comap_of_flat (T T' : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hV' : T'.IsAdmissible) (g : T'.scheme ⟶ T.scheme) (hflat : AlgebraicGeometry.Flat g) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < T'.boundary.length)
    (hD : T'.boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap g)
    (hcs : orderAtLeastLocus T'.ideal T'.mult = ⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)
    (hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)) :
    DivisorReduction.containedComponentsIdeal T' j hj' = (DivisorReduction.containedComponentsIdeal T j hj).comap g := by
  have := hflat
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  have hopen' := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'
  have hirr : ∀ w : ↥(T.boundary.get ⟨j, hj⟩).subscheme, IsIrreducible (connectedComponent w) :=
    fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w
  have hN : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hN' : TopologicalSpace.NoetherianSpace ↥(T'.boundary.get ⟨j, hj'⟩).subscheme :=
    noetherianSpace_boundary_subscheme T' hV' j hj'
  have key : ∀ (D' : T'.scheme.IdealSheafData), D' = (T.boundary.get ⟨j, hj⟩).comap g →
      ∀ (S' : Set ↥D'.subscheme),
        S' = {w : ↥D'.subscheme | connectedComponent w ⊆
            ⇑D'.subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} →
        ∀ (hop' : IsOpen S'), TopologicalSpace.NoetherianSpace ↥D'.subscheme →
          openSubschemeKer D' ⟨S', hop'⟩ =
            (openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).comap g := by
    rintro D' rfl S' rfl hop' hNN
    exact openSubschemeKer_comap_of_flat_of_noetherian g (T.boundary.get ⟨j, hj⟩)
      (orderAtLeastLocus T.ideal T.mult) hcl hirr hN hNN hopen hop'
  have hset : divisorComponentsInOrderLocus T' j hj' =
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹'
          (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} :=
    congrArg (fun A : Set ↥T'.scheme =>
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' A}) hcs
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']
  exact key _ hD _ hset hopen' hN'

theorem containedComponentsIdeal_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (hq : h ≫ T.structMap = q) (hV' : (T.pullbackAlong Y q h).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap h := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat h := inferInstance
  have hD : (T.pullbackAlong Y q h).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_of_eq_map h T.boundary (T.pullbackAlong Y q h).boundary
      (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h) j hj hj'
  have hcs : orderAtLeastLocus (T.pullbackAlong Y q h).ideal (T.pullbackAlong Y q h).mult =
      ⇑h.base ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.pullbackAlong Y q h) hV hV' h hfl j hj hj' hD hcs hcl

theorem containedComponentsIdeal_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) (hV' : (T.baseChange L f).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    flat_fieldBaseChangeProjection T L f
  have hD : (T.baseChange L f).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    get_eq_comap_get_of_eq_map (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.boundary
      (T.baseChange L f).boundary (MarkedIdealWithBoundary.baseChange_boundary T L f) j hj hj'
  have hcs : orderAtLeastLocus (T.baseChange L f).ideal (T.baseChange L f).mult =
      ⇑(pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base ⁻¹'
        orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.baseChange L f) hV hV'
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hfl j hj hj' hD hcs hcl

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

theorem IsMarked.of_comap_isoObjZero_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {d : BlowupSequenceData X} {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
    {I I' : X.IdealSheafData} {E E' : List X.IdealSheafData}
    (hI : I.comap d.isoZero.hom = I'.comap d.isoZero.hom)
    (hE : List.map (fun D => D.comap d.isoZero.hom) E =
      List.map (fun D => D.comap d.isoZero.hom) E')
    (h : d.IsMarked p I m E) : d.IsMarked p I' m E' := by
  have hIc : ∀ t : ℕ, d.controlledTransform I m t = d.controlledTransform I' m t := fun t =>
    d.controlledTransform_congr I I' (by rw [d.projectionToBase_zero]; exact hI) m t
  have hEc : ∀ t : ℕ, d.boundaryFrom E t = d.boundaryFrom E' t := fun t =>
    d.boundary_congr E E' (by simp only [d.projectionToBase_zero]; exact hE) t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [← hIc i]
    exact h.divisible i hi
  · intro i hi
    rw [← hIc i]
    exact h.center_order i hi
  · exact h.center_smooth
  · intro i hi
    rw [← hEc i]
    exact h.center_snc i hi

end BlowupSequenceData

namespace DivisorReduction

theorem goingUpInvariant_of_le (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
    (t : ℕ) (ht : t ≤ s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t := by
  induction t with
  | zero => exact goingUpInvariant_zero hres hno T j hj I₀ E₀ s hpr hE₀ hjE hget htrunc
  | succ n ih =>
      exact GoingUpInvariant.succ (ih (Nat.le_of_succ_le ht)) hbal hm hV hlift (Nat.lt_of_succ_le ht)

theorem isMarked_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).IsMarked T.structMap I₀ T.mult E₀ := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      (i + 1) hi).exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i (Nat.lt_succ_self i)
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).support_center_subset_orderAtLeastLocus hbal hm hV hi
  · intro i hi
    rw [hlen] at hi
    exact smooth_ambientBlowupSeq_center_comp hres hno T j hj I₀ E₀ s hpr i hi
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).hasStrictNormalCrossingsWith_center_boundary hlift hi

theorem comap_controlledTransform_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
    t ht).comap_controlledTransform ht

private theorem lowerIdealWithoutBlowup_eq_ideal (T : MarkedIdealWithBoundary.{u}) :
    lowerIdealWithoutBlowup T = T.ideal :=
  Scheme.IdealSheafData.comap_id T.ideal

theorem isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [AlgebraicGeometry.IsNoetherian T.scheme]
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj = ⊤)
    (hVlow : (restrictToDivisor T j hj).IsAdmissible)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := isMarked_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc
  exact BlowupSequenceData.IsMarked.of_comap_isoObjZero_eq (by simp only [hideal]) (by simp only [hbdry]) main

theorem comap_controlledTransform_of_containedComponentsIdeal_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [AlgebraicGeometry.IsNoetherian T.scheme]
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj = ⊤)
    (hVlow : (restrictToDivisor T j hj).IsAdmissible)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        T.ideal T.mult t).comap
      (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) = s.ideal t := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := comap_controlledTransform_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc t ht
  have hc := BlowupSequenceData.controlledTransform_congr
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr)
    (lowerIdealWithoutBlowup T) T.ideal (by simp only [hideal]) T.mult t
  rw [← hc]
  exact main

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
