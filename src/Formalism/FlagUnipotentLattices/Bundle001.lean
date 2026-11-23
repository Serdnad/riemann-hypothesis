module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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

open Module NumberField nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def GramDetGen : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t t' : R),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -t else 0) W Z
        (Matrix.diagonal fun i => if i = Fin.last r then -t' else 0)).det =
      (-1) ^ (r + 1) *
        (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
          (W.submatrix Fin.castSucc Fin.castSucc).det)

def GramNondeg : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (B : V →ₗ[K] V →ₛₗ[σ] K) (v : ι → V),
    (Matrix.of fun i j => B (v i) (v j)).det ≠ 0 →
    LinearIndependent K v ∧
      finrank K (Submodule.span K (Set.range v)) = Fintype.card ι ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B y x = 0) → x = 0) ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B x y = 0) → x = 0)

def DetIndexProductInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g : ℝ) (e f : ℕ),
    0 < dPs₁ → 0 < dPs₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) →
    dLa₁ * i₁ ^ 2 ≤ G0₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dPs₁ * dPs₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂)

def DetIndexProductPlacesInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < K₁ → 0 < K₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT / (Nr₂ * K₂ ^ 2) ≤ P₁ → NT / (Nr₁ * K₁ ^ 2) ≤ P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end

section

noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def IotaDual : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : AddSubgroup U) (ι' : U → U),
    g ∈ O → star g = g → g ≠ 0 → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) → (∀ x ∈ L₀', ι' x ∈ L₀) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
      (∀ l' ∈ L₀', ∀ x ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' x - x = g • l) → h (g⁻¹ • (l' - ι' l')) x ∈ O) ∧
      (∀ l' ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' l' - l' = g • l) → g⁻¹ • (l' - ι' l') ∈ L₀)

def hdual {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (M : AddSubgroup U) : AddSubgroup U where
  carrier := {x | ∀ y ∈ M, h x y ∈ O}
  add_mem' := by
    intro a b ha hb y hy
    simpa using O.add_mem (ha y hy) (hb y hy)
  zero_mem' := by
    intro y _
    simp
  neg_mem' := by
    intro a ha y hy
    simpa using O.neg_mem (ha y hy)

def DualIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [FiniteDimensional E U] (h : U →ₗ[E] U →ₗ⋆[E] E)
    (M N : Submodule (𝓞 E) U), (∀ x : U, (∀ y : U, h x y = 0) → x = 0) → N ≤ M → M.FG →
    Submodule.span E (N : Set U) = ⊤ →
      (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup

end Formalism.HermitianLatticeCounting.S6
end
end

section

noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def EmbGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (A : Submodule (𝓞 E) V) (Q : Type) [AddCommGroup Q]
    [Module (𝓞 E) Q] [Finite Q] (φ : Q →ₗ[𝓞 E] V ⧸ A), Function.Injective φ →
      ∃ s : Fin (Module.finrank E V) → Q, Submodule.span (𝓞 E) (Set.range s) = ⊤

end Formalism.HermitianLatticeCounting.S6
end
end

section

open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def UnitsSquareIndex : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], (∀ w : InfinitePlace F, w.IsReal) →
    Nat.card ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range) = 2 ^ finrank ℚ F

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end
