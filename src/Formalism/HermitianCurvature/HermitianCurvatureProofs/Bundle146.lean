module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section defs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Hyp (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ IsOpen Dm ∧ Dm ⊆ domJ k r j hj z z' ∧ RulesOn k r j hj z z' Dm Φ ∧
    Z.det ≠ 0 ∧ τ ≠ 0 ∧ γ ∈ B.GV k (r - (j + 1)) ∧ x0 k r j hj Z τ γ ∈ Dm

def Eq1 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) + levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) +
      τ • PBP.dz (fun τ' => D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      τ • D.vLet k r z z' j (by omega) (true, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq2 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 1 Φ (x0 k r j hj Z τ γ) =
    τ⁻¹ • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ)

def Eq3 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) - levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ) -
      conj τ • PBP.dzb (fun τ' => D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      conj τ • D.vLet k r z z' j (by omega) (false, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq4 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 1 Φ (x0 k r j hj Z τ γ) =
    (conj τ)⁻¹ • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ)

end defs

def Comp1 : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq2 k r j hj z z' Φ Z γ τ Y ∧ Eq4 k r j hj z z' Φ Z γ τ Y

def PlusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def PlusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def MinusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

def MinusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

theorem headLetter_of (h1 : Comp1) (hPP : PlusPos) (hPZ : PlusZero) (hMP : MinusPos) (hMZ : MinusZero) :
    LevelPointCoordinates.HeadLetter := by
  intro k r j hj z z' E _ _ Dm Φ hz hz' hD hDs hR Z γ τ hZ hτ hγ hx Y
  have hH : Hyp k r j hj z z' Dm Φ Z γ τ := ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩
  obtain ⟨c2, c4⟩ := h1 k r j hj z z' E Dm Φ Z γ τ hH Y
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · exact ⟨hPZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c2, hMZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c4⟩
  · exact ⟨hPP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c2, hMP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c4⟩

def NormalFormsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.xi0 (x0 k r j hj Z τ γ) a p = if p.val < j + 1 then C3.Zb j 1 Z τ a.val p.val else 0) ∧
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.y0 (x0 k r j hj Z τ γ) a p =
        if r + k < p.val ∧ 2 * r + k - p.val < j + 1 then star (C3.Zb j 1 Z τ a.val (2 * r + k - p.val)) else 0)

def LeadingMinorsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det ∧
      Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j + 1, by omega⟩ = Z.det * τ

def LeftActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (τ * Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩) • Ψ (x0 k r j hj Z τ γ)

def TorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      τ • PBP.dz (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ

def ConjugateActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (conj τ * conj (Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩)) • Ψ (x0 k r j hj Z τ γ)

def ConjugateTorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      -(conj τ • PBP.dzb (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ)

def FrozenX : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' u : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ' γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u ∧
      Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) * C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u * Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)

def FrozenV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' ℓ : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ' γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ ∧
      Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) * C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ * Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)

def Comp1OfParts : Prop := NormalFormsAtBasePoint → Comp1

def PlusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → LeftActionRuleAtBasePoint → TorusDirectionAtBasePoint → FrozenX → PlusPos

def PlusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → TorusDirectionAtBasePoint → PlusZero

def MinusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateActionRuleAtBasePoint → ConjugateTorusDirectionAtBasePoint → FrozenV → MinusPos

def MinusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateTorusDirectionAtBasePoint → MinusZero

theorem headLetter_of_leaves (hNf : NormalFormsAtBasePoint) (hDm : LeadingMinorsAtBasePoint) (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint)
    (hST : ConjugateTorusDirectionAtBasePoint) (hFX : FrozenX) (hFV : FrozenV) (h1 : Comp1OfParts) (hPP : PlusPosOfParts)
    (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of (h1 hNf) (hPP hNf hDm hL hT hFX) (hPZ hNf hDm hT) (hMP hNf hDm hSL hST hFV) (hMZ hNf hDm hST)

end Formalism.FourierDecayAlt.P.CutHL
end
end

section

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section pr

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def PG (x : Q.Pr (V1 E)) : Prop := OK μ ℓ x.1 ∧ OK μ ℓ x.2.unop

variable {μ ℓ}

theorem pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)) := ⟨ok_zero, ok_zero⟩

theorem pg_one : PG μ ℓ (1 : Q.Pr (V1 E)) := ⟨ok_one, ok_one⟩

theorem pg_add (hℓ : Continuous ℓ) {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x + y) :=
  ⟨ok_add hℓ hx.1 hy.1, ok_add hℓ hx.2 hy.2⟩

theorem pg_mul {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x * y) :=
  ⟨ok_mul hx.1 hy.1, ok_mul hy.2 hx.2⟩

theorem pg_neg {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (-x) := ⟨ok_neg hx.1, ok_neg hx.2⟩

theorem pg_star {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (star x) := ⟨hx.2, hx.1⟩

theorem pg_alg (c : ℂ) : PG μ ℓ (algebraMap ℂ (Q.Pr (V1 E)) c) := ⟨ok_alg c, ok_alg (conj c)⟩

theorem pg_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (f : ι → Q.Pr (V1 E)) (h : ∀ i ∈ s, PG μ ℓ (f i)) :
    PG μ ℓ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pg_add hℓ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {S : Type} [Fintype S] [DecidableEq S]


variable (μ ℓ) in
def EntrywiseClass (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) : Prop := ∀ a b, PG μ ℓ (M a b)

theorem entrywise_class_mul (hℓ : Continuous ℓ) {M N : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))} (hM : EntrywiseClass μ ℓ M) (hN : EntrywiseClass μ ℓ N) :
    EntrywiseClass μ ℓ (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact pg_sum hℓ _ _ fun c _ => pg_mul (hM a c) (hN c b)

theorem entrywise_class_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (M : ι → Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))
    (h : ∀ i ∈ s, EntrywiseClass μ ℓ (M i)) : EntrywiseClass μ ℓ (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact pg_sum hℓ _ _ fun i hi => h i hi a b

theorem entrywise_class_one : EntrywiseClass μ ℓ (1 : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_unit_matrix (a : S) (i j : Fin 2) : EntrywiseClass μ ℓ (Wd.eU a i j : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun x y => by
  unfold Wd.eU
  rw [Matrix.of_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_scalar {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : EntrywiseClass μ ℓ (Wd.io x : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  unfold Wd.io
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact pg_zero

theorem entrywise_class_insert (hℓ : Continuous ℓ) (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))} (hM : ∀ i j, EntrywiseClass μ ℓ (M i j)) :
    EntrywiseClass μ ℓ (Wd.ins a M) := by
  unfold Wd.ins
  exact entrywise_class_sum hℓ _ _ fun i _ => entrywise_class_sum hℓ _ _ fun j _ => entrywise_class_mul hℓ (entrywise_class_unit_matrix a i j) (hM i j)

theorem pg_Ts (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (Y : ℂ) : ∀ i j, PG μ ℓ (Wd.Ts σ Y i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact pg_add hℓ (pg_alg Y) hp
  · exact pg_neg hc
  · exact hci
  · exact pg_zero

theorem entrywise_class_letter (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (l : Wd.Letter ℂ S) : EntrywiseClass μ ℓ (Wd.vlet σ l) := by
  unfold Wd.vlet
  refine entrywise_class_insert hℓ _ fun i j => ?_
  unfold Wd.lift0
  rw [Matrix.map_apply]
  refine entrywise_class_scalar ?_
  split_ifs
  · exact pg_Ts hℓ σ hp hc hci _ i j
  · rw [Matrix.map_apply]
    exact pg_star (pg_Ts hℓ σ hp hc hci _ i j)

theorem entrywise_class_word_transfer (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) : ∀ w : List (Wd.Letter ℂ S), EntrywiseClass μ ℓ (Wd.bT σ w)
  | [] => by rw [Wd.bT]; exact entrywise_class_one
  | l :: w => by
      rw [Wd.bT]
      exact entrywise_class_mul hℓ (entrywise_class_letter hℓ σ hp hc hci l) (entrywise_class_word_transfer hℓ σ hp hc hci w)

theorem entrywise_class_site_one (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) :
    EntrywiseClass μ ℓ (Wd.bT (site1 (E := E) κ) w) :=
  entrywise_class_word_transfer hℓ _ ⟨ok_opP hℓ κ, ok_neg (ok_opPb hℓ κ)⟩ ⟨ok_opM _ cd_id, ok_opM _ cd_conj⟩
    ⟨ok_opM _ cd_inv, ok_opM _ cd_conjinv⟩ w

theorem oneBT_int (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) (Φ : X → Wd.Ix S → V1 E)
    (x : Wd.Ix S → V1 E) (hG : ∀ b, Good (fun v => Φ v b)) (hI : ∀ b, IsInt μ ℓ (fun v => Φ v b) (x b))
    (a : Wd.Ix S) :
    Good (fun v => oneBT κ w (Φ v) a) ∧ IsInt μ ℓ (fun v => oneBT κ w (Φ v) a) (oneBT κ w x a) := by
  have hB := entrywise_class_site_one (μ := μ) (ℓ := ℓ) hℓ κ w
  unfold oneBT act1
  exact ⟨good_sum _ _ fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1,
    int_sum hℓ _ _ _ (fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1) fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).2⟩

end pr

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

abbrev XH (h : C.LPt) : Type := U.LW (D.ptPerm h) → ℂ

def ellH (h : C.LPt) (v : XH h) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)

def zxH (h : C.LPt) (j : ℕ) (hh : D.ptSize h = j) (v : XH h) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.reindex (finCongr hh) (finCongr hh) (LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h))

def pbT (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    Q.Mx P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) F g

def domP (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) :=
  {g | (∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0) ∧ 0 < Gf k r z z' g}

theorem isOpen_domP (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (domP k r j z z') := by
  have h1 : IsOpen {g : Q.Mx k r | ∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} := by
    have : {g : Q.Mx k r | ∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} =
        ⋂ l : Fin (r + 2), {g | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} := by
      ext g; simp
    rw [this]
    refine isOpen_iInter_of_finite fun l => ?_
    by_cases hl : j ≤ l.val ∧ l.val ≤ r
    · have : {g : Q.Mx k r | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
        ext g; simp [hl.1, hl.2]
      rw [this]
      exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l).continuous continuous_const
    · have : {g : Q.Mx k r | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
        ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro a b; exact absurd ⟨a, b⟩ hl
      rw [this]; exact isOpen_univ
  exact h1.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').continuous)

theorem minorDomain_subset (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    domP k r j z z' ⊆ LevelPointCoordinates.domJ k r j hj z z' := fun g hg =>
  ⟨hg.1 ⟨j, by omega⟩ (show j ≤ j from le_rfl) (show j ≤ r by omega),
    hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ r by omega), hg.2⟩

end Formalism.FourierDecayAlt.P.PBQ
end
end
