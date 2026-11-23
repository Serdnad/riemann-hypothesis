module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountGrowthExponentialRadii
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle312
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeries
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle272
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.RingTheory.TensorProduct.Free
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr

@[expose] public section

section

open Filter Topology

theorem _root_.GlobalTheory.T.count_growth_exponential_radii : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  first | exact @GlobalTheory.hsGrowth_exp_radius | exact GlobalTheory.hsGrowth_exp_radius | (intros; apply GlobalTheory.hsGrowth_exp_radius <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots : ∀ (g h e₁ e₂ e₃ : ℂ), 4 * e₁ ^ 3 - g * e₁ - h = 0 → 4 * e₂ ^ 3 - g * e₂ - h = 0 → 4 * e₃ ^ 3 - g * e₃ - h = 0 → e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ → (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧ 16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4)) = -(g ^ 3 - 27 * h ^ 2) := by
  first | exact @GlobalTheory.CMModel.cubic_three_roots | exact GlobalTheory.CMModel.cubic_three_roots | (intros; apply GlobalTheory.CMModel.cubic_three_roots <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed : ∀ (F : IntermediateField ℚ ℂ) (x : ℂ), (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := by
  first | exact @GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed | exact GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed | (intros; apply GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_lifts_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  first | exact @GlobalTheory.HenselSplitPS.exists_lifts_of_separable | exact GlobalTheory.HenselSplitPS.exists_lifts_of_separable | (intros; apply GlobalTheory.HenselSplitPS.exists_lifts_of_separable <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
end

section

open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_semilinear : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V]
    [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V),
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ →
    ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V),
      (∀ i v, a' i (f v) = f (a i v)) →
      finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) =
        finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  intro K V ι _ _ _ _ σ N f hli hsp a a' ha
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Module K V := Module.compHom V σ
  haveI : IsScalarTower K ℂ V := ⟨fun k c v => by
    show (σ k * c) • v = σ k • c • v
    rw [mul_smul]⟩
  let g : (Fin N → K) →ₗ[K] V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }
  have hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩

    rw [← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [f.map_smulₛₗ, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis (Fin N) ℂ V := Basis.mk hli hsp'.ge
  have hc : ∀ k, c k = f (Pi.single k 1) := fun k => Basis.mk_apply _ _ _
  let e := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)
  have hbc : IsBaseChange ℂ g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g := by
      refine (Pi.basisFun K (Fin N)).ext fun k => ?_
      have := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hc, Pi.basisFun_apply]
      rfl
    exact congrArg (fun φ => φ m) h
  exact (finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1

end GlobalTheory.BadCount
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem : ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  first | exact @GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | exact GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | (intros; apply GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries <;> assumption)
end

section

open Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ), M ∈ Matrix.unitaryGroup (Fin N) ℂ → (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} => (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈ Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  first | exact @GlobalTheory.minorsMatrix_mem_unitaryGroup | exact GlobalTheory.minorsMatrix_mem_unitaryGroup | (intros; apply GlobalTheory.minorsMatrix_mem_unitaryGroup <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)), ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  first | exact @GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | exact GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | (intros; apply GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime <;> assumption)
end

section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

theorem _root_.GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  first | exact @GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | exact GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | (intros; apply GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' : ∀ (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F), j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) → Function.Injective (j₁.comp (algebraMap B A)) → ∀ a : A, j₁ a ≠ j₂ a → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ, y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_separate | exact GlobalTheory.exists_ne_zero_forall_complexPoint_separate | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_separate <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l → ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ), ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 → ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  first | (exact @GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (exact GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (intros; apply GlobalTheory.cyclo_sum_mul_star_eq_one_single <;> assumption)
end
