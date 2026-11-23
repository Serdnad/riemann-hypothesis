module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

universe u

theorem isIntegral_of_smooth_field_of_connectedSpace {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] [ConnectedSpace Z] : IsIntegral Z := by
  have hK : IsNormalScheme (Spec (.of K)) := inferInstance
  have : IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsNormalScheme.isIntegral_of_connectedSpace Z

theorem geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹_›
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact isIntegral_of_smooth_field_of_connectedSpace snd

theorem grpObj_geometricallyIntegral_of_smooth (S : Scheme.{0}) (H : Over S) [GrpObj H]
    [Smooth H.hom] [GeometricallyConnected H.hom] : GeometricallyIntegral H.hom :=
  geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Compare.AbelianSchemeTorusCompare

theorem isAbelianScheme_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (e : A ≅ B) (he : IsMonHom e.hom) (hB : IsAbelianScheme B) : IsAbelianScheme A := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom e.hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]
    have hbc : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{0})
        @GeometricallyConnected := inferInstance
    have hri : MorphismProperty.RespectsIso (C := Scheme.{0}) @GeometricallyConnected :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).2 this

end GlobalTheory.Compare.AbelianSchemeTorusCompare
end
