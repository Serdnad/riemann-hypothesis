module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Formalism.DegreeFormula.PointDegree.FlagDeg
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle001
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.WeilBound.CoreStatements.FlagImmersions.LinearRootPowerLipschitz
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle002
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

@[expose] public section

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.flag_shift_total_lin_root_power : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow | exact GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow <;> assumption)
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_integral_permutations : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F :=
  @RootFieldNumerics.degFl_symmetry_invariance

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flagDeg_eq_weyl : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (lam : Wt Ψ N), flagDeg lam = ((dimFl Ψ N).factorial : ℝ) * ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) ∧ (RegDominant lam → 0 < flagDeg lam) ∧ (Dominant lam → 0 ≤ flagDeg lam) := by
  intro Ψ _ _ N lam
  have hf : flagDeg lam = ((dimFl Ψ N).factorial : ℝ) *
      ∏ τ, ∏ i : Fin N, ∏ k : Fin N,
        (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) :=
    Formalism.DegreeFormula.flagDegFormula_statement Ψ N lam
  have hD : (0 : ℝ) < ((dimFl Ψ N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hki : ∀ i k : Fin N, i < k → (0 : ℝ) < (k : ℝ) - (i : ℝ) := by
    intro i k h
    have h' : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast h
    exact sub_pos.mpr h'
  refine ⟨hf, fun hr => ?_, fun hd => ?_⟩
  · rw [hf]
    refine mul_pos hD (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k _ => ?_)
    split_ifs with h
    · exact div_pos (sub_pos.mpr (hr τ i k h)) (hki i k h)
    · exact one_pos
  · rw [hf]
    refine mul_nonneg hD.le (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
      Finset.prod_nonneg fun k _ => ?_)
    split_ifs with h
    · exact div_nonneg (sub_nonneg.mpr (hd τ i k h.le)) (hki i k h).le
    · exact zero_le_one

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem degFl_pk_mul_eq_zero : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (k : ℕ) (G : RP Ψ N), 1 ≤ k → degFl (pk τ k * G) = 0 :=
  fun Ψ _ _ N τ k G hk => Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k G hk

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem testForms_sh_tot : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 :=
  RootFieldNumerics.exists_degree_one_class

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linA_pow_continuous_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) :=
  @RootFieldNumerics.linear_root_power_lipschitz

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.generic_point_field_iso : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X), IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq | exact GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq <;> assumption)
end
