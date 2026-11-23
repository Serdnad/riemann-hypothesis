module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle003
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in
theorem _root_.GlobalTheory.exists_monHom_factor_of_flat_surjective : ∀ (S : Scheme.{0}) (G G' G'' : Over S) [GrpObj G] [GrpObj G'] [GrpObj G''] (Φ : G ⟶ G') (f : G ⟶ G''), IsMonHom Φ → IsMonHom f → Flat Φ.left → Surjective Φ.left → QuasiCompact Φ.left → (∀ (T : Over S) (x : T ⟶ G), x ≫ Φ = 1 → x ≫ f = 1) → (∃ ψ : G' ⟶ G'', IsMonHom ψ ∧ Φ ≫ ψ = f) ∧ Epi Φ := by
  intro S G G' G'' _ _ _ Φ f hΦ hf hflat hsurj hqc hker
  haveI := hΦ
  haveI := hf
  haveI : EffectiveEpi Φ := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left Φ
  haveI : Flat (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.flat_tensorHom Φ Φ
  haveI : Surjective (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.surjective_tensorHom Φ Φ
  haveI : QuasiCompact (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.quasiCompact_tensorHom Φ Φ
  haveI : EffectiveEpi (Φ ⊗ₘ Φ) := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left _
  have hcompat : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ G), g₁ ≫ Φ = g₂ ≫ Φ → g₁ ≫ f = g₂ ≫ f := by
    intro Z g₁ g₂ h
    have h1 : (g₁ / g₂) ≫ Φ = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hker Z _ h1
    rwa [GrpObj.div_comp, div_eq_one] at h2
  refine ⟨⟨EffectiveEpi.desc Φ f hcompat, ⟨?_, ?_⟩, EffectiveEpi.fac Φ f hcompat⟩, inferInstance⟩
  · rw [← IsMonHom.one_hom (f := Φ), Category.assoc, EffectiveEpi.fac, IsMonHom.one_hom]
  · rw [← cancel_epi (Φ ⊗ₘ Φ), ← Category.assoc, ← IsMonHom.mul_hom (f := Φ), Category.assoc,
      EffectiveEpi.fac, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, EffectiveEpi.fac]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem range_eq_valuationRing_iff_isLocalization :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) (R : Type) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) R K], (∀ y : K, y ∈ Set.range (algebraMap R K) ↔ p.valuation K y ≤ 1) ↔ IsLocalization p.asIdeal.primeCompl R := by
  intro K _ _ p R _ _ _ _ _ _
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have htow : ∀ a : 𝓞 K, algebraMap R K (algebraMap (𝓞 K) R a) = algebraMap (𝓞 K) K a :=
    fun a => (IsScalarTower.algebraMap_apply (𝓞 K) R K a).symm
  have hone : ∀ s : p.asIdeal.primeCompl, p.valuation K (algebraMap (𝓞 K) K s) = 1 :=
    fun s => (p.valuation_eq_one_iff_notMem (K := K)).2 s.2
  have hne : ∀ s : p.asIdeal.primeCompl, algebraMap (𝓞 K) K s ≠ 0 := by
    intro s h
    have := hone s
    rw [h, map_zero] at this
    exact zero_ne_one this
  constructor
  · intro h
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · intro s
      obtain ⟨r, hr⟩ := (h (algebraMap (𝓞 K) K s)⁻¹).2 (by rw [map_inv₀, hone s, inv_one])
      refine IsUnit.of_mul_eq_one r (hinj ?_)
      rw [map_mul, htow, hr, map_one, mul_inv_cancel₀ (hne s)]
    · intro z
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer (algebraMap R K z)
        ((h _).1 ⟨z, rfl⟩)
      refine ⟨(n, d), hinj ?_⟩
      rw [map_mul, htow, htow]
      exact hnd
    · intro x y hxy
      refine ⟨1, ?_⟩
      have h2 : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K y := by
        rw [← htow, ← htow, hxy]
      rw [IsFractionRing.injective (𝓞 K) K h2]
  · intro h y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj p.asIdeal.primeCompl z
      have h2 := congrArg (fun t => p.valuation K (algebraMap R K t)) hnd
      simp only [map_mul, htow, hone] at h2
      rw [(_root_.mul_one _).symm.trans h2]
      exact p.valuation_le_one n
    · intro hy
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer y hy
      refine ⟨IsLocalization.mk' R n d, ?_⟩
      apply mul_right_cancel₀ (hne d)
      rw [hnd, ← htow, ← htow, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.LamF
end
