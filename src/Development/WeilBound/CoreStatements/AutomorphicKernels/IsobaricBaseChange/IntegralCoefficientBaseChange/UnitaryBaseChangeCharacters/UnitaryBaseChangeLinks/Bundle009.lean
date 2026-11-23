module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryMassFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_place_norm_centraliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  first | exact @GlobalTheory.NormHasseCent.main | (intros; apply GlobalTheory.NormHasseCent.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.unitary_mass_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n, γ.1.val.charpoly ∈ Ell E n → mass (MonoidHom.id _) (ratFinU E n) (finPt γ) = kap γ.1.val.charpoly * 2 ^ nfac γ.1.val.charpoly := by
  first | exact @GlobalTheory.BCT.MassU.mass_unitary | (intros; apply GlobalTheory.BCT.MassU.mass_unitary <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.finite_elliptic_charpolys_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinPolySupp.finpoly | (intros; apply GlobalTheory.FinPolySupp.finpoly <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hermitian_form_signature_realisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  first | exact @GlobalTheory.UnitaryClasses.refSign_prod | exact GlobalTheory.UnitaryClasses.refSign_prod | (intros; apply GlobalTheory.UnitaryClasses.refSign_prod <;> assumption)
end
