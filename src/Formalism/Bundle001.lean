module

public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Basic
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

open Finset

noncomputable section

namespace Formalism

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1



end Formalism
end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism


open ArithmeticFunction in
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x


open ArithmeticFunction in
def Schi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (χ n).re * (x / n - 1)

def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x

end Formalism
end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism


open ArithmeticFunction in
def LamF {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ :=
  Λ n * (1 + (χ n).re)

def S {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LamF χ n * (x / n - 1)

def gammaF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  Real.eulerMascheroniConstant +
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def G {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  S χ x - x * Real.log x + (1 + gammaF χ) * x

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def quadraticCharFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def quadraticCharThree : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

def quadraticCharacterMod7 : DirichletCharacter ℂ 7 := (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)

end Formalism
end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Sa (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n - 1)

def MellinSgen : Prop :=
  ∀ (a : ℕ → ℝ) (K : ℝ), (∀ n : ℕ, |a n| ≤ K * ArithmeticFunction.vonMangoldt n) →
    Measurable (Sa a) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (a n : ℂ)) s / (s * (s - 1))

end Formalism
end
end
