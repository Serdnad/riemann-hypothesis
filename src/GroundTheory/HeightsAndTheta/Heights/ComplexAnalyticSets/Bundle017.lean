module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import Mathlib.FieldTheory.Separable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermPrimitiveForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ AnalyticAt ℂ δ (A x) ∧ (∀ i j, AnalyticAt ℂ (q i j) (A x)) ∧
      (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      (∀ᶠ z in 𝓝 x, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (∀ᶠ y in 𝓝 (A x), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      ∀ i, ∀ᶠ z in 𝓝 x, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormMinimalFactorPoints.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ n + ∑ j, b j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
          (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
        ∀ U ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
          (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U ∧
            A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
            ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedLocusCutOut.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ c e : (σ → ℂ) → ℂ, AnalyticAt ℂ c w ∧ AnalyticAt ℂ e w ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → c z * e z = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 →
          ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) ↔ c z = 0) ∧
          ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) → e z ≠ 0)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedOffDiscriminant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ M ∈ 𝓝 w, ∀ y ∈ X ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedPointsNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∀ U ∈ 𝓝 w, ∃ z ∈ X ∩ U, δ (A z) ≠ 0 ∧
          (∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormWindow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ Convex ℝ B ∧ A w ∈ B ∧
        IsOpen N' ∧ closure W ⊆ N' ∧ (∀ i, AnalyticOnNhd ℂ (f i) N') ∧
        X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} ∧
        (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) ∧
        (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ i, ∀ z ∈ X ∩ W, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) ∧
        (∀ j, AnalyticOnNhd ℂ (a j) B) ∧ AnalyticOnNhd ℂ δ B ∧ (∀ i j, AnalyticOnNhd ℂ (q i j) B) ∧
        (∀ y ∈ B, δ y ≠ 0 →
          (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem UnbranchedProperCountLocallyConstant.proof : UnbranchedProperCountLocallyConstant.Statement := by
  intro σ _ Y d A D δ hD _ hprop hchart y hyD hδy
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin, ?_⟩

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := ((hg p.1 hp.1.1 (hFδ _ hp.1)).continuousAt ((hO _ hp.1.1 (hFδ _ hp.1)).mem_nhds (hyO _ hp.1)))
    have c2 := ((hg p.2 hp.2.1 (hFδ _ hp.2)).continuousAt ((hO _ hp.2.1 (hFδ _ hp.2)).mem_nhds (hyO _ hp.2)))
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  have himg : {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' F := by
    ext z
    constructor
    · rintro ⟨hzY, hzy⟩
      obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
      exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
    · rintro ⟨x, hx, rfl⟩
      have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
      exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩
  rw [himg]
  refine InjOn.encard_image fun a ha b hb hab => ?_
  by_contra hne
  exact h2 (a, b) ⟨ha, hb⟩ hne hab

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem monic_simpleRoot_isolated {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ)
    (hcont : ∀ j, ContinuousAt (a j) t)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hroot : τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0) :
    ∃ ε > 0, ∀ s, dist s t < ε → ∀ T₁ T₂ : ℂ, dist T₁ τ < ε → dist T₂ τ < ε →
      T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ) = 0 → T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ) = 0 → T₁ = T₂ := by

  set D : (Fin d → ℂ) × ℂ × ℂ → ℂ := fun v =>
    ∑ m ∈ Finset.range N, v.2.1 ^ m * v.2.2 ^ (N - 1 - m) +
      ∑ j : Fin N, a j v.1 * ∑ m ∈ Finset.range (j : ℕ), v.2.1 ^ m * v.2.2 ^ ((j : ℕ) - 1 - m) with hDdef
  have hkey : ∀ s T₁ T₂, (T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ)) - (T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ)) =
      D (s, T₁, T₂) * (T₁ - T₂) := by
    intro s T₁ T₂
    rw [hDdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hc : ∀ j, ContinuousAt (fun v : (Fin d → ℂ) × ℂ × ℂ => a j v.1) (t, τ, τ) :=
    fun j => (hcont j).comp continuousAt_fst
  have hcD : ContinuousAt D (t, τ, τ) := by
    rw [hDdef]
    fun_prop (disch := assumption)
  have hD0 : D (t, τ, τ) ≠ 0 := by
    have h1 := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ) (by
      simpa [Polynomial.eval₂_finsetSum] using hroot)
    convert h1 using 1
    simp only [hDdef, geom_sum₂_self, Polynomial.derivative_add, Polynomial.derivative_X_pow,
      Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, RingHom.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcD.eventually_ne hD0)
  refine ⟨ε, hε, fun s hs T₁ T₂ h₁ h₂ hr₁ hr₂ => ?_⟩
  have hne : D (s, T₁, T₂) ≠ 0 := hball (by simp [Prod.dist_eq, hs, h₁, h₂])
  have h := hkey s T₁ T₂
  rw [hr₁, hr₂, sub_zero, eq_comm] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hne)

theorem PrimitiveFormSheetedIffRootFull.proof : PrimitiveFormSheetedIffRootFull.Statement := by
  intro σ _ X w d A ℓ N a δ q ha hδ hq hP hsep hQ

  obtain ⟨UA, hUA, hUAo, hwUA⟩ := eventually_nhds_iff.1
    ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt).and hsep)))

  obtain ⟨UX, hUX, hUXo, hwUX⟩ := eventually_nhds_iff.1 (hP.and (eventually_all.2 hQ))
  set S : Set (σ → ℂ) := UX ∩ A ⁻¹' UA with hSdef
  have hSo : IsOpen S := hUXo.inter (hUAo.preimage A.continuous)
  set D : Set (Fin d → ℂ) := UA ∩ δ ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hUA y hy).2.1.continuousAt.continuousWithinAt) hUAo isOpen_compl_singleton

  have hrep : ∀ x ∈ X, x ∈ S → δ (A x) ≠ 0 →
      (fun i => (∑ j, q i j (A x) * ℓ x ^ (j : ℕ)) / δ (A x)) = x := by
    intro x hxX hxS hδx
    funext i
    rw [← (hUX x hxS.1).2 i hxX, mul_div_cancel_left₀ _ hδx]
  filter_upwards [hSo.mem_nhds ⟨hwUX, hwUA⟩] with z hzS hzX hδz W hWo hzW
  have hzD : A z ∈ D := ⟨hzS.2, hδz⟩
  constructor
  · rintro ⟨O, V, g, hOo, hVo, hzV, hg, hAg, hXV⟩
    have hzg : z ∈ g '' O := by rw [← hXV]; exact ⟨hzX, hzV⟩
    obtain ⟨t₀, ht₀, hgt₀⟩ := hzg
    have hAz : A z = t₀ := by rw [← hgt₀, hAg t₀ ht₀]
    subst hAz
    have hO'o : IsOpen ((O ∩ g ⁻¹' (S ∩ W)) ∩ D) :=
      (hg.continuousOn.isOpen_inter_preimage hOo (hSo.inter hWo)).inter hDo
    refine ⟨(O ∩ g ⁻¹' (S ∩ W)) ∩ D, fun s => ℓ (g s), hO'o,
      ⟨⟨ht₀, by rw [Set.mem_preimage, hgt₀]; exact ⟨hzS, hzW⟩⟩, hzD⟩,
      fun s hs => (ℓ.analyticAt (g s)).comp (hg s hs.1.1), by simp only [hgt₀], fun s hs => ?_⟩
    have hgXV : g s ∈ X ∩ V := by rw [hXV]; exact Set.mem_image_of_mem g hs.1.1
    have hgs : (fun i => (∑ j, q i j s * ℓ (g s) ^ (j : ℕ)) / δ s) = g s := by
      have e := hrep (g s) hgXV.1 hs.1.2.1 (by rw [hAg s hs.1.1]; exact hs.2.2)
      rwa [hAg s hs.1.1] at e
    beta_reduce
    rw [hgs]
    exact ⟨⟨hgXV.1, hs.1.2.2⟩, hAg s hs.1.1, rfl⟩
  · rintro ⟨O, r, hOo, hzO, hr, hrz, hfull⟩
    set H : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hHdef
    have hfull' : ∀ s ∈ O, H s ∈ X ∩ W ∧ A (H s) = s ∧ ℓ (H s) = r s := hfull
    have hH : AnalyticOnNhd ℂ H (O ∩ D) := by
      intro s hs
      refine AnalyticAt.pi fun i => ?_
      exact (Finset.analyticAt_fun_sum _ fun j _ =>
        ((hUA s hs.2.1).2.2.1 i j).mul ((hr s hs.1).pow _)).div (hUA s hs.2.1).2.1 hs.2.2
    have hHz : H (A z) = z := by
      have e := hrep z hzX hzS hδz
      rw [← hrz] at e
      exact e
    obtain ⟨ε, hε, hiso⟩ := monic_simpleRoot_isolated a (A z) (ℓ z)
      (fun j => ((hUA (A z) hzS.2).1 j).continuousAt) ((hUA (A z) hzS.2).2.2.2 hδz) ((hUX z hzS.1).1 hzX)
    set B : Set (σ → ℂ) := S ∩ ℓ ⁻¹' Metric.ball (ℓ z) ε ∩ A ⁻¹' Metric.ball (A z) ε with hBdef
    have hBo : IsOpen B :=
      (hSo.inter (Metric.isOpen_ball.preimage ℓ.continuous)).inter (Metric.isOpen_ball.preimage A.continuous)
    have hzB : z ∈ B := ⟨⟨hzS, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩
    have hO₁o : IsOpen ((O ∩ D) ∩ H ⁻¹' B) := hH.continuousOn.isOpen_inter_preimage (hOo.inter hDo) hBo
    have hzO₁ : A z ∈ (O ∩ D) ∩ H ⁻¹' B := ⟨⟨hzO, hzD⟩, by rw [Set.mem_preimage, hHz]; exact hzB⟩
    refine ⟨(O ∩ D) ∩ H ⁻¹' B, B ∩ A ⁻¹' ((O ∩ D) ∩ H ⁻¹' B), H, hO₁o,
      hBo.inter (hO₁o.preimage A.continuous), ⟨hzB, hzO₁⟩, fun s hs => hH s hs.1,
      fun s hs => (hfull' s hs.1.1).2.1, ?_⟩
    ext x
    constructor
    · rintro ⟨hxX, hxB, hxO⟩
      refine ⟨A x, hxO, ?_⟩
      have hs := hfull' (A x) hxO.1.1
      have hHB : H (A x) ∈ B := hxO.2

      have hroot : r (A x) ^ N + ∑ j, a j (A x) * r (A x) ^ (j : ℕ) = 0 := by
        have e := (hUX _ hHB.1.1.1).1 hs.1.1
        rwa [hs.2.1, hs.2.2] at e
      have hℓx : ℓ x = r (A x) := hiso (A x) hxB.2 (ℓ x) (r (A x)) hxB.1.2
        (by rw [← hs.2.2]; exact hHB.1.2) ((hUX x hxB.1.1.1).1 hxX) hroot
      have e := hrep x hxX hxB.1.1 hxO.1.2.2
      rw [hℓx] at e
      exact e
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(hfull' s hs.1.1).1.1, hs.2, by rw [Set.mem_preimage, (hfull' s hs.1.1).2.1]; exact hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def weierstrassPolynomial {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (x : Option σ → ℂ) : ℂ :=
  x none ^ d + ∑ j : Fin d, c j (fun i => x (some i)) * x none ^ (j : ℕ)

theorem weierstrassPolynomial_pointWithLast_zero {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, c j 0 = 0) (t : ℂ) : weierstrassPolynomial c (pointWithLast 0 t) = t ^ d := by
  have h : (fun i => pointWithLast (0 : σ → ℂ) t (some i)) = 0 := rfl
  simp only [weierstrassPolynomial, h, hc, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

def WeierstrassPreparation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (e : (Option σ → ℂ) → ℂ) (c : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ e 0 ∧ e 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (c j) 0) ∧ (∀ j, c j 0 = 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = e x * weierstrassPolynomial c x

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def GeneralLinearCoordinates.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ¬ (∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0) →
    ∃ (A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ)) (d : ℕ),
      analyticOrderAt (fun t => f (A (pointWithLast 0 t))) 0 = d

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
