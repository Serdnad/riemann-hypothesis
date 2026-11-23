module

public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.RealPlaceAnalysis.Bundle005
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bundle002
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

section

open Matrix UpperTheory.V.Weyl

open Formalism.REAL in
private theorem UpperTheory.V.Weyl.map_quantum_determinant {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : φ (qdet X u) = qdet (fun a b => φ (X a b)) u := by
  have hT : ∀ v a b, φ (Tm X v a b) = Tm (fun a b => φ (X a b)) v a b := fun v a b => by
    unfold Tm
    split_ifs <;> simp

  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem UpperTheory.V.Weyl.qdetHW :
    ∀ (n d : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (ν : Fin n → ℂ) (v : Fin d → ℂ), Formalism.REAL.GlRel E →
      (∀ a, E a a *ᵥ v = ν a • v) → (∀ a b, a < b → E a b *ᵥ v = 0) →
      ∀ u : ℂ, Formalism.REAL.qdet E u *ᵥ v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v := by
  intro n d E ν v hgl h1 h2 u
  let φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (Fin d → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have hφ : ∀ M w, φ M w = M *ᵥ w := fun M w => Matrix.toLinAlgEquiv'_apply M w
  have hgl' : Formalism.REAL.GlRel (fun a b => φ (E a b)) := by
    intro a b c e
    have := congrArg φ (hgl a b c e)
    simpa only [map_sub, map_mul, apply_ite φ, map_zero] using this
  have hw : Formalism.REAL.IsHW (fun a b => φ (E a b)) ν v :=
    ⟨fun a => (hφ _ _).trans (h1 a), fun a b hab => (hφ _ _).trans (h2 a b hab)⟩
  rw [← hφ, UpperTheory.V.Weyl.map_quantum_determinant]
  exact Formalism.REAL.qDetHW _ n _ ν v hgl' hw u
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.irrSub :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        0 < d' ∧ d' ≤ d ∧ B * A = 1 ∧ (∀ y, ρ' y = B * ρ y * A) ∧ (∀ y, ρ y * A = A * ρ' y) ∧
        ∀ W : Submodule ℂ (Fin d' → ℂ), (∀ y, ∀ v ∈ W, ρ' y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G _ d ρ hd
  classical
  have hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank ℂ S = m := by
    refine ⟨_, ⊤, fun y v _ => Submodule.mem_top, ?_, rfl⟩
    intro h
    have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0 := by
      rw [h]; exact finrank_bot ℂ (Fin d → ℂ)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨S, hSinv, hSne, hSrank⟩ := Nat.find_spec hex
  obtain ⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩ := subMat G d ρ S hSinv
  have hSpos : Module.finrank ℂ S ≠ 0 := fun h => hSne (Submodule.finrank_eq_zero.mp h)
  refine ⟨d', A, B, ρ', ?_, ?_, hBA, hρ', hint, ?_⟩
  · omega
  · have hle := Submodule.finrank_le S
    rw [Module.finrank_fin_fun] at hle
    omega
  · intro W hW
    by_cases hWb : W = ⊥
    · exact Or.inl hWb
    right
    have hinj : Function.Injective A.mulVecLin := by
      intro v w h
      have h2 := congrArg (fun u => B *ᵥ u) h
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA] using h2
    have hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
    have hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin := by
      intro y v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]
    have hW'ne : W.map A.mulVecLin ≠ ⊥ := by
      intro h
      apply hWb
      rw [← Submodule.finrank_eq_zero, ← hrank, h]
      exact finrank_bot ℂ (Fin d → ℂ)
    have hmin := Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le W
    rw [Module.finrank_fin_fun] at hle ⊢
    omega
end
