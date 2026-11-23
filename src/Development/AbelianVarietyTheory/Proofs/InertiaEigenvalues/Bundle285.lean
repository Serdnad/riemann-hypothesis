module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Mathlib.RingTheory.Flat.Basic
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle259
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Mathlib.Analysis.Normed.Group.Ultra
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

section

open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

theorem integ_det_le {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {m : ℕ}
    (y : Matrix (Fin m) (Fin m) E) (hy : ∀ i j, ‖y i j‖ ≤ 1) : ‖y.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hy _ _)

theorem isUnit_and_integ_inv_of_norm_det_eq_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ = 1 →
      IsUnit x ∧ ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro E _ _ n x hx hdet
  have hne : x.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hne)
  refine ⟨hu, fun i j => ?_⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hdet, inv_one, one_mul, Matrix.adjugate_apply]
  apply integ_det_le
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hx a b

end GlobalTheory.UnitDiscAlg
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.exists_family_adapted_to_separated_filtration : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  first | exact @GlobalTheory.exists_family_adapted_filtration | exact GlobalTheory.exists_family_adapted_filtration | (intros; apply GlobalTheory.exists_family_adapted_filtration <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.isBaseChange_comap_of_exact_flat : ∀ (A E : Type) [CommRing A] [CommRing E] [Algebra A E] [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂] [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂] (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂), Function.Injective j → Function.Exact j q → Function.Surjective q → IsBaseChange E N₁.subtype → IsBaseChange E N₂.subtype → (∀ x ∈ N₁, q x ∈ N₂) → IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  first | exact @GlobalTheory.isBaseChange_comap_of_exact | exact GlobalTheory.isBaseChange_comap_of_exact | (intros; apply GlobalTheory.isBaseChange_comap_of_exact <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finIso_dualLattice_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.FinIso := by
  first | exact @GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality | exact GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality | (intros; apply GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality <;> assumption)
end
