module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def CoeffCauchy : Prop :=
  ∀ (V : Type) [Fintype V] (G : MvPolynomial V ℂ) (ρ : V → ℝ) (S : ℝ) (μ : V →₀ ℕ), (∀ v, 0 < ρ v) →
    (∀ z : V → ℂ, (∀ v, ‖z v‖ ≤ ρ v) → ‖MvPolynomial.eval z G‖ ≤ S) →
    ‖AddMonoidAlgebra.coeff G μ‖ * ∏ v, ρ v ^ μ v ≤ S

def LamEnd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (NN : MLine K) (cf : K) (S : (K →+* ℂ) → ℝ) (B : ℝ),
    NN.Good → cf ≠ 0 → cf ∈ NN.I → (∀ σ, 0 < S σ) → 0 < B → (∀ σ, NN.len σ cf ≤ S σ * B) →
    - NN.deg - (Module.finrank ℚ K : ℝ) * Real.log B ≤ ∑ σ : K →+* ℂ, Real.log (S σ)

def pDeg (logOm : ℝ) : ℝ := (1 + |logOm|) / 2

def lineNN {K : Type} [Field K] [NumberField K] {g : ℕ} {V : Type} [Fintype V] (de : MLine K) (ℓ : Fin g → MLine K)
    (c : V → Fin g) (μ : V → ℕ) (n : ℕ) : MLine K :=
  (de.pow n).tensor (MLine.prodPow (fun v => ℓ (c v)) μ).dual

end Formalism.L2.LamCM
end
end

section

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

def IsBaseChangeLine {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K)
    (L1 : MLine K1) : Prop :=
  ((L1.I : Submodule (𝓞 K1) K1) = Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ L.I})) ∧
  ∀ σ : K1 →+* ℂ, L1.n σ = L.n (σ.comp (algebraMap K K1))

def NdegBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1),
    L.Good → IsBaseChangeLine L L1 → L1.Good ∧ L1.ndeg = L.ndeg

def LocGenBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1)
    (p : HeightOneSpectrum (𝓞 K)) (p1 : HeightOneSpectrum (𝓞 K1)) (c : K), L.I ≠ 0 → IsBaseChangeLine L L1 →
    (∀ a : 𝓞 K, a ∈ p.asIdeal ↔ (algebraMap (𝓞 K) (𝓞 K1) a) ∈ p1.asIdeal) → IsLocGen p c L.I →
    IsLocGen p1 (algebraMap K K1 c) L1.I

end Formalism.L2.LamCM
end
end

section

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def DegAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L M : MLine K), L.Good → M.Good →
    (L.tensor M).Good ∧ (L.tensor M).deg = L.deg + M.deg ∧ L.dual.Good ∧ L.dual.deg = - L.deg ∧
      ∀ k : ℕ, (L.pow k).Good ∧ (L.pow k).deg = k * L.deg

def MemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (x : K), I ≠ 0 →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K x ≤ p.valuation K c) → x ∈ I

def HadamardPD : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → A.det.re ≤ ∏ i, (A i i).re

end Formalism.L2.LamCM
end
end
