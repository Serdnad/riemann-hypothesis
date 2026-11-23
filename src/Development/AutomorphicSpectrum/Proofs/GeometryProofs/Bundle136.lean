module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle119
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle125
public import Mathlib.AlgebraicGeometry.FunctionField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle050
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg


theorem _root_.GlobalTheory.T.line_bundle_section_divisible : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X) (s : LB.Sec M) (δ : R), sc π ⊤ δ ≠ 0 → (∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W → ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) → ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue.sec_eq_smul_of_local | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue.sec_eq_smul_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue.sec_eq_smul_of_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  intro Z _ p _ _ hN J U n h a₀ _ hn ⟨r, hr⟩
  have hg : genericPoint Z ∈ U a₀ := ((genericPoint_spec Z).mem_open_set_iff (U a₀).isOpen).mpr (by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (U a₀)›
    exact ⟨z, trivial, hz⟩)
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  have hp : (p : Γ(Z, ⊤)) = 0 := by
    apply Z.germToFunctionField_injective ⊤
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero _ p
  obtain ⟨s, hs⟩ := GlobalTheory.CechRoot.exists_root Z (fun b => (hN b).2) p hp J U h n
    (fun a b => (hn a b).symm) a₀ (genericPoint Z) hg (algebraMap Z.functionField _ r)
    (by rw [← map_pow, hr])
  exact ⟨s, fun a b => (hs a b).symm⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank

theorem finrank_la_eq_two_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
      (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsPeriod D ty P →
      Module.finrank ℤ D.La = 2 * g :=
  fun _ _ _ _ _ _ _ _ _ hP => (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Coords

theorem dense_point_lift (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)

  let ζ₀ : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U)
  have hζ₀ : ζ₀ ≫ (f ∣_ U ≫ U.ι) = ξ := by
    simp only [ζ₀, Category.assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hT : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  have hfac : (ζ₀ ≫ (f ⁻¹ᵁ U).ι) ≫ f = ξ := by
    rw [Category.assoc, ← hT, hζ₀]
  refine ⟨ζ₀ ≫ (f ⁻¹ᵁ U).ι, hfac, ⟨?_⟩, ?_⟩
  ·
    rw [DenseRange, dense_iff_inter_open]
    intro W hW hne
    obtain ⟨v, hvW, hvU⟩ := hd.inter_open_nonempty W hW hne
    let T : (f ⁻¹ᵁ U).toScheme ⟶ X := f ∣_ U ≫ U.ι
    have hTo : IsOpenImmersion T := inferInstance
    let W' : Set (f ⁻¹ᵁ U).toScheme := (f ⁻¹ᵁ U).ι ⁻¹' W
    have hW' : IsOpen W' := hW.preimage (f ⁻¹ᵁ U).ι.continuous
    have himg : IsOpen (T '' W') := T.isOpenEmbedding.isOpenMap _ hW'
    have hne' : (T '' W').Nonempty :=
      ⟨T ⟨v, hvU⟩, ⟨v, hvU⟩, by
        change (f ⁻¹ᵁ U).ι ⟨v, hvU⟩ ∈ W
        exact hvW, rfl⟩
    obtain ⟨y, hyT, p, rfl⟩ := (ξ.denseRange).inter_open_nonempty _ himg hne'
    obtain ⟨w, hwW, hw⟩ := hyT
    have hp : T (ζ₀ p) = ξ p := by
      rw [← hζ₀]; simp [T]
    have hwp : w = ζ₀ p := T.isOpenEmbedding.injective (hw.trans hp.symm)
    refine ⟨(ζ₀ ≫ (f ⁻¹ᵁ U).ι) p, ?_, p, rfl⟩
    subst hwp
    simpa [W'] using hwW
  · intro x _
    have hx : ξ x ∈ U := hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)
    rw [← hfac] at hx
    exact hx

end GlobalTheory.CompanionTheory.Ar.Coords
end
