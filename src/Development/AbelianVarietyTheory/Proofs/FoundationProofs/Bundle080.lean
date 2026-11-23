module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle042
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Mathlib.Geometry.Manifold.StructureGroupoid
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004

@[expose] public section

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.eisenstein_wronskian_ne_zero : ∀ τ : ℍ, 2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ - 3 * E₆ τ * deriv (⇑E₄ ∘ ofComplex) τ ≠ 0 := by
  first | exact @GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | exact GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | (intros; apply GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n → ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | exact GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.strip_eval_decay <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound : ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) + 4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤ 12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  first | exact @GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | exact GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | (intros; apply GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem disc_pow_mul_slash : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  intro w f γ
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : (UpperHalfPlane.denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ReciprocityTheory.ChartRestriction.L1.DD_smul, mul_pow, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  field_simp

end GlobalTheory
end
