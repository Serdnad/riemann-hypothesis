module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle033
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.Analysis.Complex.Cardinality
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.smooth_open_immersion_range : ∀ (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ), SmoothOfRelativeDimension n (j ≫ g) → SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | exact GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LbMarking

theorem linearLift_bijective_of_discrete_kernels : ∀ (M : Type) [Group M] (g g' : ℕ) (ex : (Fin g' → ℂ) → M) (r : (Fin g → ℂ) → M) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z w, ex (z + w) = ex z * ex w) → (∀ x, ex (h x) = r x) → Function.Surjective r → (∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x‖ < δ → r x = 1 → x = 0) → (∃ δ : ℝ, 0 < δ ∧ ∀ y, ‖y‖ < δ → ex y = 1 → y = 0) → Function.Bijective h := by
  intro M _ g g' ex r h hadd hr hsurj ⟨δ, hδ, hsep⟩ ⟨ε, hε, hsep'⟩
  have hex0 : ex 0 = 1 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact left_eq_mul.mp h0
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have hs : 0 < δ / (2 * ‖x‖) := by positivity
    have ht : ((δ / (2 * ‖x‖) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hs.ne'
    have h1 : r (((δ / (2 * ‖x‖) : ℝ) : ℂ) • x) = 1 := by
      rw [← hr, map_smul, hx, smul_zero, hex0]
    have h2 : ‖((δ / (2 * ‖x‖) : ℝ) : ℂ) • x‖ < δ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      have : δ / (2 * ‖x‖) * ‖x‖ = δ / 2 := by
        field_simp
      rw [this]
      linarith
    have h3 := hsep _ h2 h1
    exact hne ((smul_eq_zero.mp h3).resolve_left ht)
  · intro v
    by_contra hv
    have hsub : ∀ a b, ex a = 1 → ex b = 1 → a ≠ b → ε ≤ ‖a - b‖ := by
      intro a b ha hb hab
      by_contra hlt
      have h1 : ex (a - b) = 1 := by
        have h2 := hadd (a - b) b
        rw [sub_add_cancel, ha, hb, _root_.mul_one] at h2
        exact h2.symm
      exact hab (sub_eq_zero.mp (hsep' _ (not_le.mp hlt) h1))
    have hK : {y | ex y = 1}.Countable := by
      have hdisj : ({y | ex y = 1} : Set (Fin g' → ℂ)).PairwiseDisjoint
          (fun y => ball y (ε / 2)) := by
        intro a ha b hb hab
        refine Set.disjoint_left.mpr ?_
        intro z hza hzb
        have h1 := hsub a b ha hb hab
        have h2 : dist z a < ε / 2 := hza
        have h3 : dist z b < ε / 2 := hzb
        have h4 : dist a b ≤ dist z a + dist z b := dist_triangle_left a b z
        rw [dist_eq_norm a b] at h4
        linarith
      exact hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
        (fun y _ => ⟨y, mem_ball_self (half_pos hε)⟩)
    choose x hx using fun t : ℂ => hsurj (ex (t • v))
    have hkK : ∀ t, ex (t • v - h (x t)) = 1 := by
      intro t
      have h2 := hadd (t • v - h (x t)) (h (x t))
      rw [sub_add_cancel, hr, hx t] at h2
      exact right_eq_mul.mp h2
    have hinj : Function.Injective (fun t : ℂ =>
        (⟨t • v - h (x t), hkK t⟩ : {y | ex y = 1})) := by
      intro s t hst
      by_contra hne
      have h1 : s • v - h (x s) = t • v - h (x t) := congrArg Subtype.val hst
      have hc : s - t ≠ 0 := sub_ne_zero.mpr hne
      apply hv
      refine ⟨(s - t)⁻¹ • (x s - x t), ?_⟩
      have h2 : (s - t) • v = h (x s - x t) := by
        rw [map_sub, sub_smul]
        rw [sub_eq_sub_iff_add_eq_add] at h1 ⊢
        rw [h1, add_comm]
      rw [map_smul, ← h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    haveI : Countable {y | ex y = 1} := hK.to_subtype
    have hC : Countable ℂ := hinj.countable
    have hle := Cardinal.mk_le_aleph0_iff.mpr hC
    rw [Cardinal.mk_complex] at hle
    exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr hle)

end GlobalTheory.CompanionTheory.Ar.LbMarking
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ExtExists

theorem exists_dvr_in_finite_ext (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra O L] [IsScalarTower O K L]
    (z : L) (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' L) (_ : IsScalarTower O O' L) (ζ : O'),
      Function.Injective (algebraMap O' L) ∧ IsPrimitiveRoot ζ n ∧ algebraMap O' L ζ = z := by
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  haveI : IsFractionRing (integralClosure O L) L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : Algebra.IsIntegral O (integralClosure O L) := inferInstance
  have hinjOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  have hinjA : Function.Injective (algebraMap O (integralClosure O L)) := fun a b h =>
    hinjOL (congrArg (fun w : integralClosure O L => (w : L)) h)
  have hinjAL : Function.Injective (algebraMap (integralClosure O L) L) := Subtype.val_injective
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure O L) (IsLocalRing.maximalIdeal O)
    (fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [hinjA (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖP : algebraMap O (integralClosure O L) ϖ ∈ P := by
    change ϖ ∈ Ideal.under O P
    rw [hPover, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖP
    exact hϖ.ne_zero (hinjA (hϖP.trans (map_zero _).symm))
  haveI := hPmax.isPrime
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _
  have hAW : Function.Injective (algebraMap (integralClosure O L) (Localization.AtPrime P)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap (integralClosure O L) L y) := fun y =>
    IsUnit.mk0 _ fun h => y.2 (by
      have : (y : integralClosure O L) = 0 := hinjAL (h.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  let f : Localization.AtPrime P →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hf : ∀ a, f (algebraMap (integralClosure O L) (Localization.AtPrime P) a) =
      algebraMap (integralClosure O L) L a := fun a => IsLocalization.lift_eq hunit a
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf] at h1
    have ha : a = 0 := hinjAL (h1.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at h
    have hs : algebraMap (integralClosure O L) (Localization.AtPrime P) s ≠ 0 :=
      (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    exact (mul_eq_zero.1 h).resolve_right hs
  letI algWL : Algebra (Localization.AtPrime P) L := f.toAlgebra
  have hOW : ∀ x : O, algebraMap O (Localization.AtPrime P) x =
      algebraMap (integralClosure O L) (Localization.AtPrime P) (algebraMap O (integralClosure O L) x) :=
    fun x => IsScalarTower.algebraMap_apply O (integralClosure O L) (Localization.AtPrime P) x
  have hWL : ∀ x, algebraMap (Localization.AtPrime P) L x = f x := fun _ => rfl
  haveI tower : IsScalarTower O (Localization.AtPrime P) L :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := Localization.AtPrime P) (A := L) fun x => by
      rw [hOW, hWL, hf]; rfl
  have hloc : IsLocalHom (algebraMap O (Localization.AtPrime P)) := ⟨fun x hx => by
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hxu
    rw [← hPover, Ideal.mem_comap] at hxm
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hxm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (by rw [← hOW]; exact hx)⟩
  haveI hOLalg : Algebra.IsAlgebraic O L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := K) (C := L)).2 inferInstance
  have halg : Algebra.IsAlgebraic O (Localization.AtPrime P) :=
    ⟨fun x => (isAlgebraic_algebraMap_iff (A := L) hfinj).1 (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have hzint : _root_.IsIntegral O z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  let zA : integralClosure O L := ⟨z, hzint⟩
  have hfz : f (algebraMap (integralClosure O L) (Localization.AtPrime P) zA) = z := hf zA
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, hdvr, inferInstance, hloc, halg, algWL, tower,
    algebraMap (integralClosure O L) (Localization.AtPrime P) zA, hfinj, ?_, hfz⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := f) (by rw [hfz]; exact hz) hfinj

theorem exists_dvr_of_generator (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω))
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O Ω'] [IsScalarTower O Ω Ω']
    (z : Ω') (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) (htop : Algebra.adjoin Ω {z} = ⊤) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' Ω') (_ : IsScalarTower O O' Ω') (ζ : O'),
      Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧
        Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
  letI algKΩ : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω
  haveI towKΩ : IsScalarTower O (FractionRing O) Ω := FractionRing.isScalarTower_liftAlgebra O Ω
  haveI : CharZero (FractionRing O) :=
    ((algebraMap (FractionRing O) Ω).charZero_iff (algebraMap (FractionRing O) Ω).injective).2 inferInstance
  letI algKΩ' : Algebra (FractionRing O) Ω' :=
    ((algebraMap Ω Ω').comp (algebraMap (FractionRing O) Ω)).toAlgebra
  haveI towK : IsScalarTower O (FractionRing O) Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = algebraMap Ω Ω' (algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x))
    rw [← IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← IsScalarTower.algebraMap_apply O Ω Ω']
  have hzi : _root_.IsIntegral (FractionRing O) z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  haveI : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) :=
    IntermediateField.adjoin.finiteDimensional hzi
  have hgen : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω')
      (by rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hz)
      (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, hinjL, hζ, hζz⟩ :=
    exists_dvr_in_finite_ext O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z})
      (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n hn hgen
  haveI towL : IsScalarTower O (IntermediateField.adjoin (FractionRing O) {z}) Ω' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω',
        IsScalarTower.algebraMap_apply O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}),
        ← IsScalarTower.algebraMap_apply (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  letI algO'Ω' : Algebra O' Ω' :=
    ((algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').comp
      (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}))).toAlgebra
  have hO'Ω' : ∀ x : O', algebraMap O' Ω' x =
      algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω'
        (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}) x) := fun _ => rfl
  haveI tow : IsScalarTower O O' Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hO'Ω', ← IsScalarTower.algebraMap_apply O O' (IntermediateField.adjoin (FractionRing O) {z}),
      ← IsScalarTower.algebraMap_apply O (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  refine ⟨O', i1, i2, i3, i4, i5, i6, algO'Ω', tow, ζ, ?_, hζ, ?_⟩
  · have : (algebraMap O' Ω' : O' → Ω') =
        (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω') ∘
          (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z})) := rfl
    rw [this]
    exact (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective.comp hinjL
  · rw [hO'Ω', hζz, IntermediateField.AdjoinSimple.algebraMap_gen]
    exact htop

end GlobalTheory.CompanionTheory.Ar.Num.ExtExists

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_ext_primitive_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ n : ℕ, 0 < n → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O') (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (_ : Algebra O' Ω') (_ : Algebra O Ω') (_ : IsScalarTower O O' Ω') (_ : IsScalarTower O Ω Ω') (ζ : O'), Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧ Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  intro O _ _ _ Ω _ _ _ hinj n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have hz := IsCyclotomicExtension.zeta_spec n Ω (CyclotomicField n Ω)
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, h1, h2, h3⟩ :=
    ExtExists.exists_dvr_of_generator O Ω hinj (CyclotomicField n Ω) _ n hn hz
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz)
  exact ⟨O', i1, i2, i3, i4, i5, i6, CyclotomicField n Ω, inferInstance, inferInstance, i7, inferInstance, i8, inferInstance, ζ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Ar.Num
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Rescar

theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (n : ℕ) (hn : n ≠ 0) (hmem : (n : R) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : R) ∈ P := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    exact absurd (by simpa using hmem : (1 : R) ∈ P) (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h))
  | prime p hp => exact ⟨p, hp, hmem⟩
  | mul a b iha ihb =>
    have ha : a ≠ 0 := fun h => hn (by simp [h])
    have hb : b ≠ 0 := fun h => hn (by simp [h])
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact iha ha h
    · exact ihb hb h

theorem exists_prime_div_uniformiser (F' : Type) [Field F'] [NumberField F']
    (v : HeightOneSpectrum (𝓞 F')) (π : F') (hπ : v.valuation F' π = WithZero.exp (-1 : ℤ)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F') ∈ v.asIdeal := by
    simpa using Ideal.absNorm_mem v.asIdeal
  obtain ⟨ℓ, hℓ, hℓmem⟩ := exists_prime_natCast_mem v.asIdeal _ hne hmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hlt : v.valuation F' (ℓ : F') < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F') (ℓ : 𝓞 F')).2 hℓmem
    simpa using this
  have hle : v.valuation F' (ℓ : F') ≤ WithZero.exp (-1 : ℤ) := by
    rcases eq_or_ne (v.valuation F' (ℓ : F')) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, v.valuation F' (ℓ : F') = WithZero.exp a :=
        ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
      rw [ha] at hlt ⊢
      have h1 : a < 0 := by
        rw [← WithZero.exp_zero] at hlt
        exact WithZero.exp_lt_exp.1 hlt
      exact WithZero.exp_le_exp.2 (by omega)
  rw [map_div₀, hπ]
  exact div_le_one_of_le₀ hle zero_le'

end GlobalTheory.CompanionTheory.Ar.Rescar
end
