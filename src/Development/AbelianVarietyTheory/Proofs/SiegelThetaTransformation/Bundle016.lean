module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeat
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryMoveHermitianHalfSpaceHigh
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle009
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

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ), IsHeat Ψ D → (∀ Z ∈ Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by
  first | exact @GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | exact GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | (intros; apply GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  first | exact @GlobalTheory.SW.exists_move_high | exact GlobalTheory.SW.exists_move_high | (intros; apply GlobalTheory.SW.exists_move_high <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem exists_weil_mul {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (h : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ')
    (h' : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ' φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ') :
    ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS (σ * σ') φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨ω, hω⟩ := h
  obtain ⟨ω', hω'⟩ := h'
  refine ⟨fun φ => ω (ω' φ), fun φ hφ => ?_⟩
  obtain ⟨hs', ht', hi'⟩ := hω' φ hφ
  obtain ⟨hs, ht, hi⟩ := hω (ω' φ) hs'
  refine ⟨hs, GlobalTheory.T.siegelThetaTransformationLaw_mul κ ι σ' σ hσ' hσ φ (ω' φ) (ω (ω' φ)) ht' ht, fun φ' hφ' => ?_⟩
  rw [hi _ (hω' φ' hφ').1, hi' φ' hφ']

theorem exists_weil_of_symplectic :
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  intro κ ι _ _ _ σ hκ hσ
  obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, l₁, l₂, l₃, rfl⟩ := GlobalTheory.T.symplectic_eq_parabolic_J_parabolic_J_parabolic' ι σ hσ
  have hJ : Matrix.J ι ℚ ∈ Matrix.symplecticGroup ι ℚ := SymplecticGroup.J_mem ι ℚ
  have w₁ := GlobalTheory.T.siegelTheta_transformation_siegelParabolic κ ι p₁ hκ h₁ l₁
  have w₂ := GlobalTheory.T.siegelTheta_transformation_siegelParabolic κ ι p₂ hκ h₂ l₂
  have w₃ := GlobalTheory.T.siegelTheta_transformation_siegelParabolic κ ι p₃ hκ h₃ l₃
  have wJ := GlobalTheory.T.exists_unitary_siegelThetaTransformationLaw_standardJ κ ι hκ
  have a₁ := mul_mem h₁ hJ
  have a₂ := mul_mem a₁ h₂
  have a₃ := mul_mem a₂ hJ
  exact exists_weil_mul a₃ h₃
    (exists_weil_mul a₂ hJ (exists_weil_mul a₁ h₂ (exists_weil_mul h₁ hJ w₁ wJ) w₂) wJ) w₃

end GlobalTheory.SW
end
