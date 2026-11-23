module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def SeparateWeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
    (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
    (∀ m j, AnalyticAt ℂ (b m j) y₀) →
    (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
    AnalyticAt ℂ f (y₀, u₀) →
    ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
      (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀),
        f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
          ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedProperCountConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → IsPreconnected D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ N : ℕ, ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def WeierstrassFiniteness.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) →
    (∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j)) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (A z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticImplicitChart.Statement : Prop :=
  ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (h : ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ)),
    (∀ j, AnalyticAt ℂ (h j) a) → (∀ j, h j a = 0) →
    LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) → W ∈ 𝓝 a →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), d + Fintype.card ι = Fintype.card σ ∧ IsOpen O ∧ IsOpen V ∧ a ∈ V ∧
        V ⊆ W ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        {z | z ∈ V ∧ ∀ j, h j z = 0} = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AnalyticRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (t₀ : Fin d → ℂ) (τ₀ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) t₀) →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable →
    τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
    ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t₀ = τ₀ ∧
      ∀ t ∈ O, r t ^ N + ∑ j, a j t * r t ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolynomialRootPredicateFactor.Statement : Prop :=
  ∀ (d N : ℕ) (B : Set (Fin d → ℂ)) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
    (P : (Fin d → ℂ) → ℂ → Prop),
    IsOpen B → Convex ℝ B → (∀ j, AnalyticOnNhd ℂ (a j) B) → AnalyticOnNhd ℂ δ B → (∃ t ∈ B, δ t ≠ 0) →
    (∀ t ∈ B, δ t ≠ 0 →
      (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    (∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (P s (r s) ↔ P t₀ τ₀)) →
    ∃ C E : (Fin d → ℂ) → ℂ → ℂ,
      (∀ t ∈ B, ∀ T : ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => C u.1 u.2) (t, T) ∧
        AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => E u.1 u.2) (t, T)) ∧
      (∀ t ∈ B, ∀ T : ℂ, C t T * E t T = T ^ N + ∑ j, a j t * T ^ (j : ℕ)) ∧
      ∀ t ∈ B, δ t ≠ 0 → ∀ τ : ℂ, τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 →
        (C t τ = 0 ↔ P t τ) ∧ (E t τ = 0 ↔ ¬ P t τ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormRootFull {σ : Type} [Fintype σ] {d N : ℕ} (X W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (δ : (Fin d → ℂ) → ℂ)
    (q : σ → Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ) : Prop :=
  ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t = τ ∧
    ∀ s ∈ O, (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) ∈ X ∩ W ∧
      A (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) = s ∧
      ℓ (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) = r s

def PrimitiveFormSheetedIffRootFull.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
    (q : σ → Fin N → (Fin d → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
    (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
    (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
      (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 → ∀ W : Set (σ → ℂ), IsOpen W → z ∈ W →
      ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) ↔
        PrimitiveFormRootFull X W A ℓ δ q (A z) (ℓ z))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def PowerSumsEsymmAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (V : Set (σ → ℂ)) (d : ℕ) (Z : (σ → ℂ) → Multiset ℂ),
    IsOpen V → (∀ z ∈ V, Multiset.card (Z z) = d) →
    (∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((Z z).map fun a => a ^ k).sum) V) →
    ∀ k, AnalyticOnNhd ℂ (fun z => (Z z).esymm k) V

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperSheetedFibreEsymm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ F : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ F D ∧
      ∀ t ∈ D, δ t ≠ 0 → ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t} →
        F t = (s.val.map l).esymm j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def pointWithLast {σ : Type} (z : σ → ℂ) (t : ℂ) : Option σ → ℂ
  | none => t
  | some i => z i

def WeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f g : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * f x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GridProductLowerBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (N : ℕ) (Z : Set (σ → ℂ)) (z₀ : σ → ℂ),
    Bornology.IsBounded Z → z₀ ∉ closure Z →
    ∃ μ : ℝ, 0 < μ ∧ ∃ U ∈ 𝓝 z₀, ∀ z ∈ U, ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) ⊆ Z → s.card ≤ N →
      ∃ u : σ → Fin (N + 1), μ ≤ ‖∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)‖

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedProperCountLocallyConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.Finite ∧
      ∀ᶠ y' in 𝓝 y, {x | x ∈ Y ∧ A x = y'}.encard = {x | x ∈ Y ∧ A x = y}.encard

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
