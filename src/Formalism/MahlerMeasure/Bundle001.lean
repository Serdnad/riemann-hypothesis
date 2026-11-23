module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.RingTheory.Polynomial.Pochhammer
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

namespace Formalism.GM

open MvPolynomial Finset

def qch (a j : ℕ) : ℚ := (a.choose j : ℚ)

def LevelSum : Prop :=
  ∀ (A z l : ℕ), z + l ≤ A →
    ∑ j ∈ range (l + 1), (-1 : ℚ) ^ j * qch l j * qch (A - z - l) j / qch A j = qch (z + l) l / qch A l

noncomputable def tieE {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (∑ c, X (w c) * X (e c))

noncomputable def tieF {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ c, (pderiv (w c)).toLinearMap ∘ₗ (pderiv (e c)).toLinearMap

noncomputable def tiePhi {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ j ∈ range (o + 1),
    (((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((o + n + r + z - 1).choose j : k))) •
      (((tieE w e) ^ j).comp ((tieF w e) ^ j))

def BiHom {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (a b : ℕ) (u : MvPolynomial σ k) : Prop :=
  ∀ m ∈ u.support, (∑ c, m (w c)) = a ∧ (∑ c, m (e c)) = b

def LevelAct : Prop :=
  ∀ (k σ : Type) [Field k] [CharZero k] (r : ℕ) (w e : Fin r → σ), Function.Injective w →
    Function.Injective e → (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n z l : ℕ) (u : MvPolynomial σ k), l ≤ o → l ≤ n → tieF w e u = 0 → BiHom w e (o - l) (n - l) u →
      tiePhi w e o n z ((tieE w e ^ l) u) =
        (((z + l).choose l : k) / ((o + n + r + z - 1).choose l : k)) • ((tieE w e ^ l) u)

end Formalism.GM
end

section

namespace Formalism.GM

open Finset Polynomial

def DetBlockLead : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (D : ℕ) (e : Fin n → ℕ),
    (∀ i, e i ≤ D) → (∀ i j, (A i j).natDegree + max (e i) (e j) ≤ D) →
      (A.det).natDegree ≤ ∑ i, (D - e i) ∧
      (A.det).coeff (∑ i, (D - e i)) =
        (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ∧
      ((Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ≠ 0 →
        (A.det).natDegree = ∑ i, (D - e i) ∧
        (A.det).leadingCoeff = (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det)

noncomputable def vmin (p : ℕ) {K : Type} [NormedField K] (h : ℕ) (x : K) : ℝ :=
  -Real.logb p (max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))))




end Formalism.GM
end

section

namespace Formalism.GM

open Finset Polynomial

def MahlerDisc : Prop :=
  ∀ (p k i : ℕ) (t₀ : ℤ), p.Prime → i ≤ p ^ k →
    ∀ n : ℕ, padicNorm p
      ((Polynomial.C ((i.factorial : ℚ)⁻¹) *
        (descPochhammer ℚ i).comp (Polynomial.C ((p : ℚ) ^ k) * X + Polynomial.C (t₀ : ℚ))).coeff n) ≤ 1

end Formalism.GM
end
