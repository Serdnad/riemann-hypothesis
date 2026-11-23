module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle011
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle012
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le : ∀ q n : ℕ, 2 ≤ q → 0 < n → ((Finset.Ioo 0 (q ^ n - 1)).filter (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤ ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  first | exact @GlobalTheory.CuspGL.card_nonregular_residues_le | exact GlobalTheory.CuspGL.card_nonregular_residues_le | (intros; apply GlobalTheory.CuspGL.card_nonregular_residues_le <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.separation_numerical_ineq_cuspidalGL : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  first | exact @GlobalTheory.CuspGL.sep_numerical_ineq | exact GlobalTheory.CuspGL.sep_numerical_ineq | (intros; apply GlobalTheory.CuspGL.sep_numerical_ineq <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField : ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ, ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  first | exact @GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | exact GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | (intros; apply GlobalTheory.CuspGL.TeichEmb.exists_teichmuller <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.frobeniusTorus_character_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.CuspGL.torus_orthogonality | exact GlobalTheory.CuspGL.torus_orthogonality | (intros; apply GlobalTheory.CuspGL.torus_orthogonality <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank : ∀ (k : Type) [Field k] [IsAlgClosed k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ), (N : k) ≠ 0 → g ^ N = 1 → ∀ h : k → ℂ, ((LinearMap.charpoly g).roots.map h).sum = ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  first | exact @GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace | exact GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace | (intros; apply GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.finrank_eigenspace_monomial_matrix_lift : ∀ (k : Type) [Field k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → ∀ μ : k, μ ≠ 0 → Module.finrank k (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ) = Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then θ (c j) else 0)) (θ μ)) := by
  first | exact @GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift | exact GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift | (intros; apply GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ) (Φ' : Module.End F (V ⧸ W) → ℂ), ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W}, Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) = (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) * ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by
  first | exact @GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks | exact GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks | (intros; apply GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_int_relation_of_isIntegral_relation : ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) → ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  first | exact @GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral | exact GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral | (intros; apply GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  first | exact @GlobalTheory.parsevalSep_bound | exact GlobalTheory.parsevalSep_bound | (intros; apply GlobalTheory.parsevalSep_bound <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 → (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | exact GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | (intros; apply GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_twelve_order_sixtythree | exact GlobalTheory.no_norm_twelve_order_sixtythree | (intros; apply GlobalTheory.no_norm_twelve_order_sixtythree <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  first | exact @GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow | exact GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow | (intros; apply GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow <;> assumption)
end
