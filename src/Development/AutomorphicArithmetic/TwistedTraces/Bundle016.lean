module

public import GroundTheory.AutomorphicForms.L2LocalComponents.CuspSmooth
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle002
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle009
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle003
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle013
import GroundTheory.AutomorphicForms.Bundle004
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

@[expose] public section

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology


theorem UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (C : ℝ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (S : Submodule ℂ (cuspForms K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → S ≤ centralCuspForms K n → (∀ φ ∈ S, ∀ u ∈ U, finRepCusp K n (u : AdelicGLn.integralFiniteGL K n) φ = φ) → (∀ φ ∈ S, ∀ i, ‖cuspVecL μ ((gkModuleCusp K n).ρ (b i) φ)‖ ≤ C * ‖cuspVecL μ φ‖) → FiniteDimensional ℂ S := by
  intro K _ _ n μ _ d b C U S hU hS hfix hbound
  obtain ⟨N, hN, hNv⟩ := UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound _ _ _ (isExpLieAlgebra K n) d b C
  obtain ⟨N', hN', hN'd⟩ := UpperTheory.exists_nhds_one_normOneGL_factorization K n N U hN hU
  have hApprox := UpperTheory.exists_approximate_identity_integrated
    (normOneGL (K := K) (n := n)) (CuspL2 μ) (cuspRepT μ) μ N' hN'
  obtain ⟨f, hf⟩ := hApprox
  have key : ∀ v ∈ S.map (cuspVecL μ),
      ‖(cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ 1 / 2 * ‖v‖ := by
    rintro _ ⟨φ, hφ, rfl⟩
    apply hf (cuspVecL μ φ) (1 / 2 * ‖cuspVecL μ φ‖)
    intro g hg
    obtain ⟨a, ha, u, hu, rfl⟩ := hN'd g hg
    have hφ' : φ ∈ centralCuspForms K n := hS hφ
    have hfx : cuspRepT μ (retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n))) (cuspVecL μ φ) =
        cuspVecL μ φ := by
      rw [← cuspToL2_finRepCusp μ _ hφ', hfix φ hφ u hu]
    rw [(cuspRepT μ).map_mul_apply, hfx, ← archRepT_apply]
    refine hNv (CuspL2 μ) (archRepT μ) (cuspVecL μ φ) (fun g w => ?_)
      (isSmoothVector_cuspToL2 μ hφ') (fun i => ?_) a ha
    · rw [archRepT_apply]
      exact UnitaryRep.norm_map _ _ _
    · rw [derivOp_cuspVecL μ hφ']
      exact hbound φ hφ i
  haveI : FiniteDimensional ℂ (S.map (cuspVecL μ)) :=
    UpperTheory.finiteDimensional_of_compact_near_identity (CuspL2 μ) _ (S.map (cuspVecL μ)) (isCompactOperator_cuspRep μ f) key
  exact UnitaryAdmissible.finiteDimensional_of_map_mem (E := S.map (cuspVecL μ)) (cuspVecL μ)
    (fun x hx => Submodule.mem_map_of_mem hx)
    (fun x hx h => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hS hx) h)
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem pow_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (k : archCompact K n) (m : ℕ) :
    ∀ φ ∈ centralCuspForms K n, (archRepT μ (k : archGroup K n) ^ m) (cuspVecL μ φ) =
      cuspVecL μ (((gkModuleCusp K n).σ k ^ m) φ) := by
  induction m with
  | zero =>
    intro φ _
    simp
  | succ m ih =>
    intro φ hφ
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ← cuspToL2_sigma μ k hφ,
      ih _ (σ_mem_centralCuspForms k hφ)]

private theorem aeval_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (k : archCompact K n) (q : ℂ[X]) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) :
    aeval (archRepT μ (k : archGroup K n)) q (cuspVecL μ φ) =
      cuspVecL μ (aeval ((gkModuleCusp K n).σ k) q φ) := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add (f := _), ContinuousLinearMap.add_apply, LinearMap.add_apply, ha, hb]
  | monomial m c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, ContinuousLinearMap.mul_apply,
      pow_cuspVecL μ k m φ hφ]
    simp [Algebra.algebraMap_eq_smul_one]

theorem UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (d : ℕ) (p : archCompact K n → ℂ[X]) (Y : (isExpLieAlgebra K n).lieSubalgebra), (∀ k, p k ≠ 0 ∧ (p k).natDegree ≤ d) → (∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y) ∈ archCompact K n) → ∃ M : ℝ, ∀ φ ∈ centralCuspForms K n, (∀ k, aeval ((gkModuleCusp K n).σ k) (p k) φ = 0) → ‖cuspVecL μ ((gkModuleCusp K n).ρ Y φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
  intro K _ _ n μ _ d p Y hp hk
  let kk : ℝ → archCompact K n := fun t => ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y), hk t⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_isRoot_exp_mul_forall d (fun t => p (kk t)) (fun t => hp _)
  refine ⟨M, fun φ hφ hkill => ?_⟩
  have hy := (isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) (isSmoothVector_cuspToL2 μ hφ)
    ((isExpLieAlgebra K n).ofLie Y)
  have e := derivOp_cuspVecL μ hφ ((isExpLieAlgebra K n).ofLie Y)
  rw [IsExpLieAlgebra.toLie_ofLie] at e
  rw [e] at hy
  have hu : ∀ t : ℝ, (archRepT μ ((kk t : archCompact K n) : archGroup K n)) =
      archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) := fun t => rfl
  refine UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated (CuspL2 μ)
    (fun t => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)))
    (fun t => p (kk t)) M (cuspVecL μ φ) _ ?_ ?_ ?_ ?_ hy ?_ hM
  · ext1 x
    simp [(isExpLieAlgebra K n).expG_zero]
  · intro s t
    ext1 x
    rw [(isExpLieAlgebra K n).expG_add_smul, BanachRep.map_mul_apply]
    rfl
  · intro t x
    rw [archRepT_apply]
    exact UnitaryRep.norm_map _ _ _
  · have hfin := (gkModuleCusp K n).locallyFinite φ
    have hle : Submodule.span ℂ (Set.range fun t : ℝ =>
        archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) (cuspVecL μ φ)) ≤
        (Submodule.span ℂ (Set.range fun k => (gkModuleCusp K n).σ k φ)).map (cuspVecL μ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨kk t, rfl⟩, cuspToL2_sigma μ (kk t) hφ⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro t
    have := aeval_cuspVecL μ (kk t) (p (kk t)) hφ
    rw [hkill, map_zero] at this
    exact this
end
