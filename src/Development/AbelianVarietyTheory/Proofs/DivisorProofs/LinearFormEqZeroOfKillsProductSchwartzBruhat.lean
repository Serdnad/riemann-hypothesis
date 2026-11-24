module

import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RemovableLogGrowthSingularity
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ActsFormula
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.BoxSpan

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  intros
  apply _root_.GlobalTheory.CompanionTheory.ThetaBox.box_mem_SB <;> assumption

theorem schr_boxFun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁)
      (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  apply _root_.PositivityTheory.KCo.schr_box <;> assumption

end GlobalTheory.BoxSpan


open GlobalTheory.BoxSpan in
theorem GlobalTheory.BoxSpan.boxSpan_ker : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  intro F _ _ v κ κ' _ _ ψ hψ h1 Λ hΛ Φ hΦ
  classical
  let N : Submodule ℂ ((κ ⊕ κ' → Fv F v) → ℂ) := Submodule.span ℂ
    {f | ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ' → Fv F v), f = boxFun φ₁ φ₂}
  have hN : N ≤ SB (κ ⊕ κ' → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact boxFun_mem_SB' h₁ h₂
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    intro w
    let Lw : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → Fv F v) → ℂ) :=
      { toFun := schr ψ w
        map_add' := fun f g => by funext x; simp [schr, mul_add]
        map_smul' := fun c f => by funext x; simp [schr]; ring }
    have : N ≤ N.comap Lw := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      show schr ψ w (boxFun φ₁ φ₂) ∈ N
      rw [schr_boxFun]
      exact Submodule.subset_span ⟨_, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₁, _,
        GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₂, rfl⟩
    exact fun φ hφ => this hφ
  let i₁ := Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
  let i₂ := Set.indicator {x : κ' → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ' → Fv F v) → ℂ)
  have h0 : boxFun i₁ i₂ ∈ N := Submodule.subset_span
    ⟨i₁, GlobalTheory.StdVacuum.indicator_mem_SB v, i₂, GlobalTheory.StdVacuum.indicator_mem_SB v, rfl⟩
  have hne : boxFun i₁ i₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [boxFun, i₁, i₂, zero_mem] at this
  have hall := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hN hS _ h0 hne
  have hk : N ≤ LinearMap.ker Λ := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact hΛ φ₁ h₁ φ₂ h₂
  rw [← hall] at hΦ
  exact hk hΦ
