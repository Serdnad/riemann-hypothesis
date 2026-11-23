module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle011
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem different_sum_eq_neg_finrank_mul_log_rootDiscr : ∀ (E : Type) [Field E] [NumberField E], {p : Nat.Primes | ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≠ 0}.Finite ∧ ∑ᶠ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = -(Module.finrank ℚ E : ℝ) * Real.log (rootDiscr E) := by
  intro E _ _
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (discr E).natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := hn ▸ Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hsum : ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p],
      GlobalTheory.CompanionTheory.Ar.Fl.logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        Real.log ‖((n : ℚ) : ℂ_[p])‖ := by
    intro p
    rw [GlobalTheory.T.sum_logIdeal_eq_log_absNorm E _ hD p, absNorm_differentIdeal E (𝓞 E), ← hn,
      Rat.cast_natCast]
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.rat_product_formula (n : ℚ) hq
  have h1 : ‖((n : ℚ) : ℂ)‖ = (n : ℝ) := by rw [Rat.cast_natCast, Complex.norm_natCast]
  have hpos : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero E))
  have h2 : Real.log (rootDiscr E) = (Module.finrank ℚ E : ℝ)⁻¹ * Real.log (n : ℝ) := by
    rw [rootDiscr_def, Real.log_rpow hpos, hn, Nat.cast_natAbs]
  have hk : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  simp only [hsum]
  refine ⟨hfin, ?_⟩
  rw [h1] at hprod
  rw [h2, ← mul_assoc, neg_mul, mul_inv_cancel₀ hk.ne', neg_one_mul]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

theorem _root_.GlobalTheory.T.gram_matrix_pos_def_conjugate : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (i : ℕ) (f : Fin i → B.carrier), LinearIndependent (𝓞 L) f → (∀ σ, (gramMat B σ f).PosDef) ∧ ∀ σ, gramMat B (ComplexEmbedding.conjugate σ) f = (gramMat B σ f).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | exact GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj <;> assumption)
end

section

open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

theorem _root_.GlobalTheory.T.baseChange_inner_self_eq_gramMat_form : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)), (∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j) → ∀ (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Fin i → K), x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) '' (LinearMap.range c : Submodule (𝓞 L) (Fin i → L))) → ∃ X : (B.baseChange K).carrier, ∀ τ : K →+* ℂ, ((B.baseChange K).metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) = star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length | exact GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length <;> assumption)
end

end

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.different_ideal_log_sum_root_discriminant : ∀ (E : Type) [Field E] [NumberField E], {p : Nat.Primes | ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≠ 0}.Finite ∧ ∑ᶠ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = -(Module.finrank ℚ E : ℝ) * Real.log (rootDiscr E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.different_sum_eq_neg_finrank_mul_log_rootDiscr | exact GlobalTheory.CompanionTheory.Ar.Fl.different_sum_eq_neg_finrank_mul_log_rootDiscr | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.different_sum_eq_neg_finrank_mul_log_rootDiscr <;> assumption)

end
end
