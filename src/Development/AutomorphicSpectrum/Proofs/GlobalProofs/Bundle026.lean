module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle020
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017

@[expose] public section

section


theorem _root_.GlobalTheory.T.jacquet_module_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | (intros; apply GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_values_negative_integer_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.high_difference_vanishes_negative_integer : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.finite_difference_cone_term_eq : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.finite_difference_cone_term_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ), Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable <;> assumption)
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.exists_unit_power_in_congruence : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits <;> assumption)
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.finite_units_bounded_embedding_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio <;> assumption)
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.totally_positive_basis_ratio_bound : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone <;> assumption)
end
