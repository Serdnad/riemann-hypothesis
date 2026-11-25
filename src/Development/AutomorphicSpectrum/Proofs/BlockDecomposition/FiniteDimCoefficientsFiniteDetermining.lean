module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.UniSol

theorem exists_finset_separating {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset K, ∀ c ∈ A, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  classical
  have key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n →
      ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0 := by
    apply _root_.GlobalTheory.Pc3.RS.exists_finset_sep <;> assumption
  obtain ⟨S, hS⟩ := key _ ⊤ rfl
  refine ⟨S, fun c hc hvan => ?_⟩
  have h0 := hS ⟨c, hc⟩ Submodule.mem_top hvan
  exact congrArg Subtype.val h0

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  apply _root_.GlobalTheory.AvgCoeff.coeffSpan_finiteDimensional <;> assumption

theorem coeffSpan_unisolvent : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  intro K W _ _ _ _ ρ
  haveI := finiteDimensional_coeffSpan ρ
  exact exists_finset_separating _

end GlobalTheory.CompanionTheory.CTFin.UniSol

end
