module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def valP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithTop ℤ :=
  valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def lamP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithBot ℤ :=
  lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def geB (x : WithTop ℤ) (θ : WithBot ℤ) : Prop := ∀ t : ℤ, θ = (t : WithBot ℤ) → (t : WithTop ℤ) ≤ x

def leT (y : WithBot ℤ) (M : WithTop ℤ) : Prop := ∀ t : ℤ, M = (t : WithTop ℤ) → y ≤ (t : WithBot ℤ)

def GoodG {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k) : Prop :=
  geB (valP isVec i G) θ ∧ leT (lamP isVec i G) M

def psiFam (R : Type*) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) R :=
  psiPath R isVec x.1.1 N x.1.2

def FactSplit : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), i ≤ N → G ∈ polB k n N B →
    ∃ (T : Finset (ℕ × Fin n →₀ ℕ)) (Gc : (ℕ × Fin n →₀ ℕ) → MvPolynomial (ℕ × Fin n) k),
      (∀ β ∈ T, ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0) ∧
      (∀ β ∈ T, Gc β ∈ polB k n i B) ∧
      G = ∑ β ∈ T, Gc β * monomial β 1 ∧
      (GoodG isVec i θ M G → ∀ β ∈ T, GoodG isVec i θ M (Gc β))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def gtBox {n : ℕ} (μ : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (μ i.succ) (μ i.castSucc)

def dGT : (n : ℕ) → (Fin n → ℤ) → ℕ
  | 0, _ => 1
  | n + 1, μ => ∑ κ ∈ gtBox μ, dGT n κ


open Classical in
def stripsUp {n : ℕ} (μ : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) := by
  letI : DecidablePred (fun ν => HStrip ν μ b) := fun ν => by
    unfold HStrip
    infer_instance
  exact (Fintype.piFinset fun i => Finset.Icc (μ i) (μ i + b)).filter fun ν => HStrip ν μ b


open Classical in
def stripsDown {n : ℕ} (μ : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) := by
  letI : DecidablePred (fun ν => HStrip μ ν b) := fun ν => by
    unfold HStrip
    infer_instance
  exact (Fintype.piFinset fun i => Finset.Icc (μ i - b) (μ i)).filter fun ν => HStrip μ ν b

def StripsMem : Prop :=
  ∀ (n : ℕ) (μ ν : Fin n → ℤ) (b : ℕ),
    (ν ∈ stripsUp μ b ↔ HStrip ν μ b) ∧ (ν ∈ stripsDown μ b ↔ HStrip μ ν b)

def GTPieri : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ) (b : ℕ), Antitone μ →
    ∑ ν ∈ stripsUp μ b, dGT n ν = dGT n μ * (n + b - 1).choose b ∧
    ∑ ν ∈ stripsDown μ b, dGT n ν = dGT n μ * (n + b - 1).choose b

def StdCountGT : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ →
    Finite {I : ℤ → Finset (Fin n) // IsStd μ I} ∧ Nat.card {I : ℤ → Finset (Fin n) // IsStd μ I} = dGT n μ

def CountPAll : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), CountP n N isVec B

def ContIdx (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ) : Type :=
  {x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n)) //
    x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2}

def CountCont : Prop :=
  ∀ (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ), i ≤ N → Antitone μ₀ →
    Finite (ContIdx n i N isVec B μ₀) ∧
    Nat.card (ContIdx n i N isVec B μ₀) = dGT n μ₀ * ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end
