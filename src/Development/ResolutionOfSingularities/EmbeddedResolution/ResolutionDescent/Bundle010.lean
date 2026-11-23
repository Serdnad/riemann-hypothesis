module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle002
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle009
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
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

@[expose] public section

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

theorem isAdmissible_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) : (T.baseChange L f).IsAdmissible := by
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base L f) :=
    instFlatSpecMapOfFieldHom T.base L f
  have hfst : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  refine
    { charZero := ‹CharZero L›
      locallyOfFiniteType := ?_
      nonzeroOnComponents := ?_
      one_le_mult := hV.one_le_mult
      quasiCompact := ?_
      smooth := ?_
      snc := ?_ }
  · exact
      (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact hV.nonzeroOnComponents.comap_of_flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  · exact
      (inferInstance : AlgebraicGeometry.QuasiCompact
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact smooth_pullbackSnd_specMap T.structMap (CommRingCat.ofHom f)
  · exact inStrictNormalCrossingPosition_comap_pullback_specMap T.structMap (CommRingCat.ofHom f) T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

theorem isAdmissible_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q]
    (hq : h ≫ T.structMap = q) :
    (T.pullbackAlong Y q h).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hqc : AlgebraicGeometry.QuasiCompact q := inferInstance
  subst hq
  have : AlgebraicGeometry.Smooth (h ≫ T.structMap) := inferInstance
  have : AlgebraicGeometry.Flat h := inferInstance
  refine ⟨hV.charZero, ?_, ?_, hV.one_le_mult, hqc, ?_, ?_⟩
  · show AlgebraicGeometry.LocallyOfFiniteType (h ≫ T.structMap)
    infer_instance
  · exact hV.nonzeroOnComponents.comap_of_flat h
  · show AlgebraicGeometry.Smooth (h ≫ T.structMap)
    infer_instance
  · exact inStrictNormalCrossingPosition_comap T.structMap h T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem affineSpace_reindex_symm_comp_reindex {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e.symm : m → n) S ≫ AffineSpace.reindex (e : n → m) S =
      𝟙 (AffineSpace n S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

theorem affineSpace_reindex_comp_reindex_symm {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e : n → m) S ≫ AffineSpace.reindex (e.symm : m → n) S =
      𝟙 (AffineSpace m S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

def affineSpaceIsoOfEquiv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex (e.symm : m → n) S
  inv := AffineSpace.reindex (e : n → m) S
  hom_inv_id := affineSpace_reindex_symm_comp_reindex e S
  inv_hom_id := affineSpace_reindex_comp_reindex_symm e S

theorem affineSpaceIsoOfEquiv_hom_comp_over {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom ≫ (AffineSpace m S ↘ S) = (AffineSpace n S ↘ S) := by
  simp [affineSpaceIsoOfEquiv, AffineSpace.reindex]

theorem affineSpaceIsoOfEquiv_hom_comp_toSpec (k : Type u) [Field k] {n m : Type u} (e : n ≃ m) :
    (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom ≫ affineSpaceIndexedByToSpec k m =
      affineSpaceIndexedByToSpec k n := by
  exact affineSpaceIsoOfEquiv_hom_comp_over e (Spec (CommRingCat.of k))

def uliftFinSumOneEquiv (n : ℕ) : ULift.{u, 0} (Fin n ⊕ Fin 1) ≃ ULift.{u, 0} (Fin (n + 1)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

def toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (n + 1))) :=
  φ.hom ≫ affineSpaceInl k n 1 ≫
    (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom

theorem isClosedImmersion_toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    AlgebraicGeometry.IsClosedImmersion (toAffineSpaceOfAmbientIso G n φ) := by
  have h : AlgebraicGeometry.IsClosedImmersion
      (φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  exact h

theorem toAffineSpaceOfAmbientIso_comp_toSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    toAffineSpaceOfAmbientIso G n φ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))) =
      G.ambientStruct := by
  have h : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [h]
  simp only [Category.assoc]
  rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, hφ]

theorem hasSmoothCoordCodim_toAffineSpaceOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u}
    [Field k] [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (toAffineSpaceOfAmbientIso G n φ) 1 := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin 1)))
      (affineSpaceInl k n 1) 1 := hasSmoothCoordCodim_affineSpaceInl hsm k n 1
  have h2 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) 1 :=
    h1.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumOneEquiv.{u} n))
  have hdef : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [hdef]
  exact h2.iso_hom_comp φ

def presentationOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    ClosedEmbeddingIntoAffineSpace G where
  codimBound := 1
  dim := n + 1
  toAffine := toAffineSpaceOfAmbientIso G n φ
  one_le_codimBound := le_rfl
  one_le_dim := Nat.succ_le_succ (Nat.zero_le n)
  isClosedImmersion_toAffine := isClosedImmersion_toAffineSpaceOfAmbientIso G n φ
  toAffine_comp := toAffineSpaceOfAmbientIso_comp_toSpec G n φ hφ
  locallyConstCodim := hasSmoothCoordCodim_toAffineSpaceOfAmbientIso hsm G n φ

def affineSpaceChartPresentation (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    ClosedEmbeddingIntoAffineSpace (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) :=
  presentationOfAmbientIso hsm (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) ((hemb k Y pY).choose)
    (Iso.refl _) (by exact Category.id_comp _)

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def NilIsStrictNormalCrossingsOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
    (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []

theorem nilIsStrictNormalCrossingsOfSmooth : NilIsStrictNormalCrossingsOfSmooth.{u} := by
  intro k _ _ A q hq
  have : AlgebraicGeometry.Smooth q := hq
  exact inStrictNormalCrossingPosition_nil q

theorem hasProperCenters_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A) :
    (embeddedResolutionRuleOfPrincipalization A h).HasProperCenters := by
  intro k _ _ Y p _ _ _ _ D i hi
  have hi' : i < ((D.toEmbeddedBlowupSequence A).inducedBlowups (h k Y p D)).withoutIsoBlowups.length := hi
  exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top _ hi'

theorem toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) :
    (embeddedResolutionRuleOfPrincipalization A h).toAffineResolutionRule (affineSpaceEmbeddingChoice hemb hsnc hsm) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw := by
  funext k _ _ Y p _ _ _ _
  rw [EmbeddedResolutionRule.toAffineResolutionRule_apply, affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum]
  exact embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum A h hemb hsnc hsm hw k Y p

end FunctorialResolution.EmbeddedResolution

end
end
