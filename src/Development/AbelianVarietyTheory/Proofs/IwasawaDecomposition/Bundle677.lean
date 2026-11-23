module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle662
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle663
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCount
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bounded_combination_of_span_coordinate_rows : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  first | exact @GlobalTheory.combo_of_bounded_rows_bounded | exact GlobalTheory.combo_of_bounded_rows_bounded | (intros; apply GlobalTheory.combo_of_bounded_rows_bounded <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.matrix_mul_bounded_poly_growth | exact GlobalTheory.matrix_mul_bounded_poly_growth | (intros; apply GlobalTheory.matrix_mul_bounded_poly_growth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polynomial_growth_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.growth_bound_of_spanning_combinations | exact GlobalTheory.growth_bound_of_spanning_combinations | (intros; apply GlobalTheory.growth_bound_of_spanning_combinations <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.linearIndependent_real_combinations_of_independent : ∀ (g r d : ℕ) (x : Fin r → Fin g → ℂ) (e : Fin d → Fin r → ℝ), LinearIndependent ℝ x → LinearIndependent ℝ e → LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  first | exact @GlobalTheory.linearIndependent_real_combination | exact GlobalTheory.linearIndependent_real_combination | (intros; apply GlobalTheory.linearIndependent_real_combination <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rat_linearIndependent_coords_of_real_independent : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  first | exact @GlobalTheory.rowsInd_rat_of_real | exact GlobalTheory.rowsInd_rat_of_real | (intros; apply GlobalTheory.rowsInd_rat_of_real <;> assumption)
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem siegel_unipotent_inv_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  intro n
  refine ⟨(Nat.factorial n : ℝ), ?_⟩
  intro u hdiag hlow hup
  have hbt : u.BlockTriangular id := fun i j hij => hlow i j hij
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    simp [hdiag]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  refine ⟨u⁻¹, Matrix.nonsing_inv_mul u hunit, Matrix.mul_nonsing_inv u hunit, ?_, ?_⟩
  · intro i j hij
    letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
    exact Matrix.blockTriangular_inv_of_blockTriangular hbt hij
  · intro i j
    have hinv : u⁻¹ = u.adjugate := by
      rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have hb : ∀ a b, |(u.updateRow j (Pi.single i 1)) a b| ≤ 1 := by
      intro a b
      by_cases ha : a = j
      · subst ha
        rw [Matrix.updateRow_self]
        by_cases hb : b = i
        · subst hb; simp
        · simp [Pi.single_apply, hb]
      · rw [Matrix.updateRow_ne ha]
        rcases lt_trichotomy a b with h | h | h
        · linarith [hup a b h]
        · subst h; simp [hdiag]
        · simp [hlow a b h]
    have := Matrix.det_le (abv := AbsoluteValue.abs) hb
    simpa using this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  first | exact @GlobalTheory.familyIsotropicDual_linearIndependent_and_card | exact GlobalTheory.familyIsotropicDual_linearIndependent_and_card | (intros; apply GlobalTheory.familyIsotropicDual_linearIndependent_and_card <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  first | exact @GlobalTheory.exists_lagrangian_dual_in_coisotropic | exact GlobalTheory.exists_lagrangian_dual_in_coisotropic | (intros; apply GlobalTheory.exists_lagrangian_dual_in_coisotropic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.coisotropic_sublattice_of_torsion_count : ∀ (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ), M.det ≠ 0 → LinearIndependent ℚ (fun i j => (A i j : ℚ)) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i)) → ∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  first | exact @GlobalTheory.CoisoCount.coisotropic_of_torsion_count | exact GlobalTheory.CoisoCount.coisotropic_of_torsion_count | (intros; apply GlobalTheory.CoisoCount.coisotropic_of_torsion_count <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem exists_bilinForm_descend_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (hf : Function.Surjective f) (β : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x, f x = 0 → ∀ y, β x y = 0) (h2 : ∀ x, f x = 0 → ∀ y, β y x = 0) :
    ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  classical
  set g := Function.surjInv hf with hgdef
  have hg : ∀ y, f (g y) = y := Function.surjInv_eq hf
  have key1 : ∀ a b, f a = f b → ∀ y, β a y = β b y := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h1 (a - b) hk y
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have key2 : ∀ a b, f a = f b → ∀ y, β y a = β y b := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h2 (a - b) hk y
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨LinearMap.mk₂ ℤ (fun y y' => β (g y) (g y')) ?_ ?_ ?_ ?_, ?_⟩
  · intro y1 y2 y'
    rw [key1 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add (f := _), hg, hg, hg]), map_add (f := _),
      LinearMap.add_apply]
  · intro c y y'
    rw [key1 (g (c • y)) (c • g y) (by rw [map_zsmul, hg, hg]), map_smul, LinearMap.smul_apply]
  · intro y y1 y2
    rw [key2 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add (f := _), hg, hg, hg]), map_add (f := _)]
  · intro c y y'
    rw [key2 (g (c • y')) (c • g y') (by rw [map_zsmul, hg, hg]), map_smul]
  · intro x y
    rw [LinearMap.mk₂_apply, key1 (g (f x)) x (hg _), key2 (g (f y)) y (hg _)]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem essFiniteType_int_stalk (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) : Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum F := s x
  have h2 : (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hF : Algebra.EssFiniteType ℚ F := inferInstance
  have hZF : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  have h3 : (algebraMap ℤ F).EssFiniteType := RingHom.essFiniteType_algebraMap.2 hZF
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem exists_ringHom_stalk (F : Type) [Field F] (X : Scheme.{0}) (s : X ⟶ Sp F) (x : X) :
    Nonempty (F →+* X.presheaf.stalk x) := by
  let p : PrimeSpectrum F := s x
  exact ⟨(s.stalkMap x).hom.comp (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p))⟩

theorem stalk_factor_eq {X : Scheme.{0}} {R : CommRingCat.{0}} {x y : X} (hy : y = x) (φ : X.presheaf.stalk x ⟶ R)
    (ψ : X.presheaf.stalk y ⟶ R) (h : Spec.map ψ ≫ X.fromSpecStalk y = Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ e : X.presheaf.stalk y →+* X.presheaf.stalk x, Function.Bijective e ∧ ψ.hom = φ.hom.comp e := by
  subst hy
  refine ⟨RingHom.id _, Function.bijective_id, ?_⟩
  have : ψ = φ := Spec.map_injective ((cancel_mono _).1 h)
  subst this
  rfl

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

end GlobalTheory.GenFan
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 1 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

end GlobalTheory.CdvrExt
end
