module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle163
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle157
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  first | exact @GlobalTheory.FN.cmp_ringEquiv | exact GlobalTheory.FN.cmp_ringEquiv | (intros; apply GlobalTheory.FN.cmp_ringEquiv <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionRingOver_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  first | exact @GlobalTheory.FN.ring_isDomain | exact GlobalTheory.FN.ring_isDomain | (intros; apply GlobalTheory.FN.ring_isDomain <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasSomeLevelOver_of_integral_invariant : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (h : ℍ → ℂ) (r : Fin n → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, h (γ • τ) = h τ) → (∀ j, InR ε.range (r j)) → (∀ τ, h τ ^ n + ∑ j, r j τ * h τ ^ (j : ℕ) = 0) → InR ε.range h := by
  first | exact @GlobalTheory.FN.inR_of_integral | exact GlobalTheory.FN.inR_of_integral | (intros; apply GlobalTheory.FN.inR_of_integral <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.fractionField_ext_closure_injective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ (L : Type) [CommRing L] (φ ψ : T.K →+* L), (∀ a, φ (T.io a) = ψ (T.io a)) → φ = ψ) ∧ (∀ (g : GQ) (a : GlobalTheory.FN.ring ε.range), ∃ a' : GlobalTheory.FN.ring ε.range, (a' : ℍ → ℂ) = GlobalTheory.FN.cmp g a ∧ T.sl g (T.io a) = T.io a') ∧ Function.Injective T.exp ∧ Function.Injective T.an := by
  first | exact @GlobalTheory.FN.frac_ext_clo_inj | exact GlobalTheory.FN.frac_ext_clo_inj | (intros; apply GlobalTheory.FN.frac_ext_clo_inj <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.fractionField_exists_gamma_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  first | exact @GlobalTheory.FN.frac_exists_level | exact GlobalTheory.FN.frac_exists_level | (intros; apply GlobalTheory.FN.frac_exists_level <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  first | exact @GlobalTheory.FN.frac_isAlgebraic_adjoin_j | exact GlobalTheory.FN.frac_isAlgebraic_adjoin_j | (intros; apply GlobalTheory.FN.frac_isAlgebraic_adjoin_j <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  first | exact @GlobalTheory.EisM.qs_injective | exact GlobalTheory.EisM.qs_injective | (intros; apply GlobalTheory.EisM.qs_injective <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.zs_monomial_ratio_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  first | exact @GlobalTheory.zs_eq_mul_dep_eis | exact GlobalTheory.zs_eq_mul_dep_eis | (intros; apply GlobalTheory.zs_eq_mul_dep_eis <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV : ∀ (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ), l.Prime → ((∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) → (∀ y, b (l * y) = t * b y) → ∀ n, n ≠ 0 → eis j c a b (l * n) = t * eis j c a b n) ∧ (1 ≤ j → (∀ x, a (l * x) = t * a x) → ∀ n, n ≠ 0 → eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n) := by
  first | exact @GlobalTheory.eis_U_V | exact GlobalTheory.eis_U_V | (intros; apply GlobalTheory.eis_U_V <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a → PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  first | exact @GlobalTheory.EisM.Vo_polyB_qs | exact GlobalTheory.EisM.Vo_polyB_qs | (intros; apply GlobalTheory.EisM.Vo_polyB_qs <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite : ∀ (S : Set (ℕ → ℂ)) (B : ℕ) (φ : (ℕ → ℂ) → ℂ), 0 ∈ S → (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ φ (a + b) = φ a + φ b) → (∀ c : ℂ, ∀ a ∈ S, c • a ∈ S ∧ φ (c • a) = c * φ a) → (∀ a ∈ S, (∀ n < B, a n = 0) → a = 0) → ∃ c : ℕ → ℂ, ∀ a ∈ S, φ a = lam B c a := by
  first | exact @GlobalTheory.func_eq_lam | exact GlobalTheory.func_eq_lam | (intros; apply GlobalTheory.func_eq_lam <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sum_periodic_cot_eq_qExpansion_fourier : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) = -2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  first | exact @GlobalTheory.CotQExp.sum_cot_eq_qexp | exact GlobalTheory.CotQExp.sum_cot_eq_qexp | (intros; apply GlobalTheory.CotQExp.sum_cot_eq_qexp <;> assumption)
end
