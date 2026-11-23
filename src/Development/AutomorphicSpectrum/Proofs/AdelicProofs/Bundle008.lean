module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle006
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

theorem product_formula_embeddings (k : Type) [Field k] [NumberField k] (x : k) (hx : x ≠ 0) :
    {p | (LogNorms.ofElt x).finSum p ≠ 0}.Finite ∧
      (∑ s : k →+* ℂ, Real.log ‖s x‖) + ∑ᶠ p, (LogNorms.ofElt x).finSum p = 0 := by
  have hN : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have hfin : ∀ p : Nat.Primes, (LogNorms.ofElt x).finSum p =
      Real.log ‖((Algebra.norm ℚ x : ℚ) : ℂ_[p])‖ := fun p =>
    sum_log_norm_embeddings_eq_log_norm k ℂ_[p] x hx
  have hinf := sum_log_norm_embeddings_eq_log_norm k ℂ x hx
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rat_product_formula (Algebra.norm ℚ x) hN
  simp only [hfin]
  exact ⟨h1, by rw [hinf]; exact h2⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.ideal_line_lattice_index : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)), M.FG → Submodule.span K (M : Set (Fin n → K)) = ⊤ → ∀ v : Fin n → K, v ≠ 0 → ∃ (I : Ideal (𝓞 K)) (d : 𝓞 K), I ≠ ⊥ ∧ d ≠ 0 ∧ (∀ t ∈ I, ((t : K) / (d : K)) • v ∈ M) ∧ genIndex (M ⊓ (Submodule.span K (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K)).toAddSubgroup (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => v)).toAddSubgroup = |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| / (I.absNorm : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.SatLine.saturatedLine_eq_ideal_div | exact GlobalTheory.CompanionTheory.Adelic.SatLine.saturatedLine_eq_ideal_div | (intros; apply GlobalTheory.CompanionTheory.Adelic.SatLine.saturatedLine_eq_ideal_div <;> assumption)
end
