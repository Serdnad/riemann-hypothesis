module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.SplittingField.Construction
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem geometricallyIntegral_of_isOpenImmersion_comp_surjective :
    ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  intro O Z T j f _ _ hs
  refine ⟨fun {K} _ y P fst snd h => ?_⟩
  have hZf : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (IsPullback.of_hasPullback f y)
  let fst' : P ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc]; exact h.w)
  have sq : IsPullback fst fst' j (pullback.fst f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) (h₃₁ := y) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
    have e : fst' ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
    rw [e]; exact h
  have : IsOpenImmersion fst' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hsn : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h hs
  have : Nonempty P := by
    obtain ⟨z, -⟩ := snd.surjective (Nonempty.some inferInstance : Spec (.of K))
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion fst'

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory

theorem surjective_inf_of_geometricallyIntegral :
    ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens),
      Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  intro Z T f _ O O' hO hO'
  refine ⟨fun t => ?_⟩
  have hint : IsIntegral (f.fiber t) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback f (T.fromSpecResidueField t))
  have hi : IsPreirreducible (f ⁻¹' {t}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ (f.fiberι t).continuous.continuousOn
  obtain ⟨x, hx⟩ := (O.ι ≫ f).surjective t
  obtain ⟨x', hx'⟩ := (O'.ι ≫ f).surjective t
  obtain ⟨y, hy, k₁, k₂⟩ := hi _ _ O.2 O'.2
    ⟨x.1, by rw [← hx]; rfl, x.2⟩ ⟨x'.1, by rw [← hx']; rfl, x'.2⟩
  exact ⟨⟨y, k₁, k₂⟩, hy⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsRational

open Polynomial

theorem exists_ext_factor (K R : Type) [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (φ : R →+* Ω), φ.comp (algebraMap K R) = σ.comp (algebraMap K K'') →
        ∃ φ'' : R →+* K'', σ.comp φ'' = φ := by
  classical
  let b := Module.finBasis K R
  let f : K[X] := ∏ i, minpoly K (b i)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  have hroot : ∀ r ∈ Set.range b, aeval r f = 0 := by
    rintro _ ⟨i, rfl⟩
    simp only [f, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K _)
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K'' Ω _ _ _ _ _ σ φ hφ
  have hs : (f.map (algebraMap K K'')).Splits := by
    rw [IsScalarTower.algebraMap_eq K f.SplittingField K'', ← Polynomial.map_map]
    exact (SplittingField.splits f).map _
  have hmem : ∀ r, φ r ∈ σ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      refine hs.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) ?_
      rw [Polynomial.map_map, ← hφ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hroot x hx, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ⟨algebraMap K K'' c, ?_⟩ hx
      rw [← RingHom.comp_apply, ← hφ, RingHom.comp_apply]
  let e := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => σ.injective (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict σ.range hmem), ?_⟩
  ext r
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict σ.range hmem r))

theorem exists_ext_points (K : Type) [Field K] (T : Over (Sp K)) (hT : IsFinite T.hom) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (t : Sp Ω ⟶ T.left), t ≫ T.hom = spMap (σ.comp (algebraMap K K'')) →
        ∃ w : Sp K'' ⟶ T.left, spMap σ ≫ w = t := by
  haveI : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ρ.hom.toAlgebra
  haveI : Module.Finite K Γ(T.left, ⊤) := by
    have : IsFinite (Spec.map ρ) := by rw [hρ]; infer_instance
    exact (IsFinite.SpecMap_iff ρ).1 this
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_factor K Γ(T.left, ⊤)
  refine ⟨K', _, _, hfin, fun K'' Ω _ _ _ _ _ σ t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ T.left.isoSpec.hom)
  have h1 : φ.hom.comp (algebraMap K Γ(T.left, ⊤)) = σ.comp (algebraMap K K'') := by
    have : Spec.map (ρ ≫ φ) = Spec.map (CommRingCat.ofHom (σ.comp (algebraMap K K''))) := by
      rw [Spec.map_comp, hφ, hρ, Category.assoc, Iso.hom_inv_id_assoc, ht]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨φ'', hφ''⟩ := H K'' Ω σ φ.hom h1
  refine ⟨Spec.map (CommRingCat.ofHom φ'') ≫ T.left.isoSpec.inv, ?_⟩
  have e : CommRingCat.ofHom φ'' ≫ CommRingCat.ofHom σ = φ := by
    ext r
    exact congrArg (fun g => g r) hφ''
  rw [← Category.assoc, spMap, ← Spec.map_comp, e, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TorsRational
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatCodimOne

theorem coheight_map_le_one {X Y : Scheme.{0}} (q : Y ⟶ X) (hq : GeneralizingMap q) (y : Y)
    (hy : Order.coheight y ≤ 1) : Order.coheight (q y) ≤ 1 := by
  have hy' := (Order.coheight_le_coe_iff (n := 1)).1 hy
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun z hz ↦ ?_
  obtain ⟨y', h₁, rfl⟩ := hq (show z ⤳ q y from hz.le)
  have hlt : y < y' := ⟨h₁, fun h ↦ hz.not_ge (Specializes.map h q.continuous)⟩
  have hm : IsMax y' := by simpa using hy' y' hlt
  have : IsMax (q y') := fun w hw ↦ by
    obtain ⟨y'', h₂, rfl⟩ := hq (show w ⤳ q y' from hw)
    exact Specializes.map (hm (show y' ≤ y'' from h₂)) q.continuous
  simpa using this

theorem preimage_contains_codim_le_one : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  intro X Y q _ W hW y hy
  show q y ∈ W
  apply hW
  rw [ringKrullDim_stalk_eq_coheight] at hy ⊢
  have h1 : Order.coheight y ≤ 1 := by exact_mod_cast hy
  have := coheight_map_le_one q (Flat.generalizingMap q) y h1
  exact_mod_cast this

end GlobalTheory.FlatCodimOne
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift


open MvPolynomial in
theorem standardSmoothRelDim_lift_of_sqZero {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (B₀ : Type) [CommRing B₀]
    [Algebra R₀ B₀] (hB₀ : Algebra.IsStandardSmoothOfRelativeDimension g R₀ B₀) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀),
      (∀ r, p (algebraMap R B r) = algebraMap R₀ B₀ (π r)) ∧ Function.Surjective p ∧
      (∀ b, p b = 0 → b ∈ I.map (algebraMap R B)) ∧ Algebra.IsStandardSmoothOfRelativeDimension g R B := by
  obtain ⟨κ, τ, _, _, P, hP⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 → b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    intro h0
    rw [hp, hφ] at h0
    have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
      rw [P.span_range_relation_eq_ker]
      first
        | exact h0
        | exact RingHom.mem_ker.mpr h0
        | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
    let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
    have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
    have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by

      rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
      simp [hc', hv]
    rw [MvPolynomial.ker_map, hk] at hg
    have hs : ∑ j, c' j * v j ∈ J :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
    rw [this]
    have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
    rwa [Ideal.map_map] at hmm
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ hker _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have hdim : Q'.dimension = g := hP
  exact ⟨_, inferInstance, inferInstance, p, halg, hsurj, hker, Q'.isStandardSmoothOfRelativeDimension hdim⟩

theorem isPushout_of_surjective {R C C₀ : Type} [CommRing R] [CommRing C] [CommRing C₀] (J : Ideal R)
    [Algebra (R ⧸ J) C₀] (σ : R →+* C) (p : C →+* C₀) (hp : Function.Surjective p)
    (hσ : ∀ r, p (σ r) = algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J r))
    (hker : ∀ c, p c = 0 → c ∈ J.map σ) :
    IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom p)
      (CommRingCat.ofHom (algebraMap (R ⧸ J) C₀)) := by
  have hinv : Function.RightInverse (Function.surjInv hp) p := Function.surjInv_eq hp
  have hle : ∀ (T : CommRingCat.{0}) (u : C →+* T) (w : R ⧸ J →+* T),
      (∀ a, u (σ a) = w (Ideal.Quotient.mk J a)) → RingHom.ker p ≤ RingHom.ker u := by
    intro T u w huw c hc
    have h : J.map σ ≤ RingHom.ker u := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, huw, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact h (hker c hc)
  have hcond : ∀ (s : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J))) (a : R),
      s.inl.hom (σ a) = s.inr.hom (Ideal.Quotient.mk J a) := fun s a => congr($(s.condition) a)
  refine ⟨⟨by ext a; exact hσ a⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (p.liftOfRightInverse _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩)) ?_ ?_ ?_⟩⟩
  · intro s; ext c
    exact p.liftOfRightInverse_comp_apply _ hinv _ c
  · intro s; ext a
    show p.liftOfRightInverse _ hinv _ (algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J a)) = _
    rw [← hσ, p.liftOfRightInverse_comp_apply]
    exact hcond s a
  · intro s m h₁ _
    ext b
    obtain ⟨c, rfl⟩ := hp b
    have e : m.hom (p c) = s.inl.hom c := congr($h₁ c)
    rw [e]
    exact (p.liftOfRightInverse_comp_apply _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩ c).symm

theorem exists_chart_lift : ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (g : ℕ) (B : Over (Sp R))
    (b : B ⟶ Over.mk (spMap (Ideal.Quotient.mk J))), SmoothOfRelativeDimension g b.left → ∀ x : B.left,
    ∃ (C : Type) (_ : CommRing C) (σ : R →+* C)
      (j : Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)) ⟶ B),
      SmoothOfRelativeDimension g (spMap σ) ∧ j ≫ b = snd _ _ ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  intro R _ J hJ g B b hsm x
  let s₀ : B.left ⟶ Sp (R ⧸ J) := b.left
  have hsm₀ : SmoothOfRelativeDimension g s₀ := hsm
  obtain ⟨U₂, hU₂, V₂, hV₂, hx₂, e₂, h₂⟩ := hsm₀.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨r, s, hxs, e, hf⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).2
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves g).away x
    ⟨⊤, isAffineOpen_top _⟩ ⟨U₂, hU₂⟩ ⟨V₂, hV₂⟩ ⟨V₂, hV₂⟩ hx₂ hx₂ e₂ h₂ trivial
  let V : B.left.affineOpens := ⟨B.left.basicOpen s, hV₂.basicOpen s⟩
  have hle : V.1 ≤ s₀ ⁻¹ᵁ ⊤ := le_top
  have htop : RingHom.IsStandardSmoothOfRelativeDimension g (s₀.appLE ⊤ V.1 hle).hom := by
    have : IsLocalization.Away r Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r) :=
      (isAffineOpen_top _).isLocalization_basicOpen r
    have heq : s₀.appLE ⊤ V.1 hle = CommRingCat.ofHom (algebraMap Γ(Sp (R ⧸ J), ⊤)
        Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r)) ≫ s₀.appLE _ _ e := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Scheme.Hom.map_appLE]
    rw [heq]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).1 _ r _ hf
  have hC₀ : Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ J) (Sec s₀ V.1) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).symm.commRingCatIsoToRingEquiv htop
  obtain ⟨C, _, _, p, hpσ, hp, hker, hC⟩ := standardSmoothRelDim_lift_of_sqZero J (by rw [hJ]; rfl)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.mk_ker) g (Sec s₀ V.1) hC₀
  let σ : R →+* C := algebraMap R C
  have hpo := isPushout_of_surjective J σ p hp hpσ hker
  have H1 := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  let A : Over (Sp R) := Over.mk (spMap σ)
  let A' : Over (Sp R) := Over.mk (spMap (Ideal.Quotient.mk J))
  have H0 : IsPullback (fst A A').left (snd A A').left A.hom A'.hom := IsPullback.of_hasPullback _ _
  let k := H0.isoIsPullback _ _ H1
  have hk₂ : k.hom ≫ spMap (algebraMap (R ⧸ J) (Sec s₀ V.1)) = (snd A A').left :=
    H0.isoIsPullback_hom_snd _ _ H1
  have hw : (k.hom ≫ affPt s₀ V) ≫ B.hom = (A ⊗ A').hom := by
    rw [← Over.w b, ← Over.w (snd A A'), ← hk₂]
    simp only [Category.assoc]
    rw [← Category.assoc (affPt s₀ V), affPt_w]
  let j : A ⊗ A' ⟶ B := Over.homMk (k.hom ≫ affPt s₀ V) hw
  have hjl : j.left = k.hom ≫ affPt s₀ V := rfl
  refine ⟨C, inferInstance, σ, j, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hC))
  · ext1
    rw [Over.comp_left, hjl, Category.assoc]
    exact (congrArg (k.hom ≫ ·) (affPt_w s₀ V)).trans hk₂
  · rw [hjl]; infer_instance
  · have hxV : x ∈ Set.range (affPt s₀ V) := by rw [GlobalTheory.LiftSys.Coh.range_affPt]; exact hxs
    obtain ⟨z, hz⟩ := hxV
    refine ⟨k.inv z, ?_⟩
    rw [hjl, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, hz]

end GlobalTheory.LBLift
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Tube

theorem exists_affine_preimage_le :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [UniversallyClosed f] (s : S) (W : X.Opens), (∀ x, f x = s → x ∈ W) → ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  intro X S f _ s W hW
  have hc : IsClosed (f '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  have hs : s ∈ (f '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hW x rfl)
  obtain ⟨U, hU, hsU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show s ∈ (⟨_, hc.isOpen_compl⟩ : S.Opens) from hs)
  refine ⟨U, hU, hsU, fun x hx => ?_⟩
  by_contra hxW
  exact hUV hx ⟨x, hxW, rfl⟩

end GlobalTheory.Tube
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LamPull

theorem lbIso_pull_lift : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (M : LB A.left), P.IsLB → M.IsLB → LBIso P (cubeLB A ![fst A A, snd A A] M) → ∀ (T : Over (Sp ℂ)) (a b : T ⟶ A), LBIso (P.pull (lift a b).left) (cubeLB A ![a, b] M) := by
  intro A _ _ P M hP hM e T a b
  have hc : ∀ {T' : Over (Sp ℂ)} (x : Fin 2 → (T' ⟶ A)), (cubeLB A x M).IsLB := fun x => by
    unfold cubeLB; exact LB.isLB_linComb hM _ _
  have h₁ : LBIso (P.pull (lift a b).left) ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) :=
    GlobalTheory.GenSpread.lbIso_pullback e _
  have h₂ : LBIso ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) (cubeLB A ![a, b] M) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (GlobalTheory.PrimNorm.chartSquare M (lift a b) (lift_fst a b).symm (lift_snd a b).symm) (GlobalTheory.lbIso_refl (hc _))
  exact LBIso.trans (pull_isLB hP _) (pull_isLB (hc _) _) (hc _) h₁ h₂

end GlobalTheory.LamPull
end
end
