module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle013
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem siegel_weil_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  intro E _ _ _ Ψ hΨ n N hn
  induction N with
  | zero =>
    intro _ M R φ _ Z _
    rw [Base.swd_zero, Base.swDiff_deg_zero]
  | succ N ih =>
    intro h
    exact GlobalTheory.T.siegelWeil_formula_degree_succ E Ψ hΨ n N hn h (ih (by omega))

end GlobalTheory.SW
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.weil_doubledTestFunction_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  first | exact @GlobalTheory.SW.weil_dbl_zero_eq_zero | exact GlobalTheory.SW.weil_dbl_zero_eq_zero | (intros; apply GlobalTheory.SW.weil_dbl_zero_eq_zero <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker


open GlobalTheory.SW.DblZero in
theorem schur_heisG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ A : TF n g → TF n g, (∀ φ, IsSB φ → IsSB (A φ)) → (∀ φ ψ, IsSB φ → IsSB ψ → A (φ + ψ) = A φ + A ψ) → (∀ (a : ℂ) φ, IsSB φ → A (a • φ) = a • A φ) → (∀ (y : Matrix (Fin n) (Fin r) E) φ, IsSB φ → A (heisG X bas y φ) = heisG X bas y (A φ)) → ∃ c : ℂ, ∀ φ, IsSB φ → A φ = c • φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs _ A hA hadd hsmul hcomm

  obtain ⟨c, hc⟩ := exists_eq_mul_ip (κ := Fin n) (ι := Fin g) (fun φ ψ => ip (A φ) ψ)
    (fun φ φ' ψ hφ hφ' hψ => by
      rw [hadd φ φ' hφ hφ', ip_add_left (hA φ hφ) (hA φ' hφ') hψ])
    (fun φ ψ ψ' hφ hψ hψ' => by
      exact ip_add_right (hA φ hφ) hψ hψ')
    (fun a b φ ψ hφ hψ => by
      rw [hsmul a φ hφ, ip_smul (hA φ hφ) hψ])
    (fun a b φ ψ hφ hψ => by
      obtain ⟨y, hy⟩ := exists_heisG (n := n) hs a b
      rw [← hy φ, hcomm y φ hφ, hy (A φ)]
      exact ((heisS_laws _ _ a b (A φ) (hA φ hφ)).2.2.2.2) ψ hψ)
  refine ⟨c, fun φ hφ => ?_⟩

  have hAφ := hA φ hφ
  have hcφ : IsSB (-c • φ) := ((isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1) (-c)
  have hd : IsSB (A φ + -c • φ) := (isSB_algebra_haar_linear _ _ _ (A φ) (-c • φ) hAφ hcφ).1
  have hzero : ip (A φ + -c • φ) (A φ + -c • φ) = 0 := by
    rw [ip_add_left hAφ hcφ hd, hc φ _ hφ hd]
    have h1 : ip (-c • φ) (A φ + -c • φ) = -c * ip φ (A φ + -c • φ) := by
      have := ip_smul hφ hd (-c) 1
      rw [one_smul, map_one, mul_one] at this
      exact this
    rw [h1]
    ring
  by_contra hne
  have hne' : A φ + -c • φ ≠ 0 := by
    intro h0
    apply hne
    have : A φ = -(-c • φ) := eq_neg_of_add_eq_zero_left h0
    rw [this, neg_smul, neg_neg]
  exact ip_self_ne_zero hd hne' hzero

end GlobalTheory.Ker
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.doubledHermitianTestFunction_zero_and_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∃ a : ℂ, a ≠ 0 ∧ ∃ b : ℝ, 0 < b ∧ ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂ ∧ ip (dbl X bas idx φ₁ φ₂) (dbl X bas idx φ₁ φ₂) = b * (ip φ₁ φ₁ * ip φ₂ φ₂) := by
  first | exact @GlobalTheory.SW.dbl_zero_and_norm | exact GlobalTheory.SW.dbl_zero_and_norm | (intros; apply GlobalTheory.SW.dbl_zero_and_norm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ := by
  first | exact @GlobalTheory.Ker.exists_test_of_fock | exact GlobalTheory.Ker.exists_test_of_fock | (intros; apply GlobalTheory.Ker.exists_test_of_fock <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ φ', SW.IsSB φ' → C.Th x (φ + φ') = C.Th x φ + C.Th x φ' ∧ (C.Th x φ = C.Th x φ' → φ = φ')) ∧ (∀ a : ℂ, C.Th x (a • φ) = a • C.Th x φ) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.rho (finW S T y) (C.Th x φ) = C.Th x (heisG C.X C.bas (-y) φ)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ w, C.Th (lact ga x) (wG C.X C.bas C.idx ga φ) w = C.Th x φ (actO S T 1 γ⁻¹ w) := by
  first | exact @GlobalTheory.Ker.Ctx.th_laws | exact GlobalTheory.Ker.Ctx.th_laws | (intros; apply GlobalTheory.Ker.Ctx.th_laws <;> assumption)
end
