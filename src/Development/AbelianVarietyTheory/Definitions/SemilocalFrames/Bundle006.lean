module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions

variable (D : D7)

structure Glob0 (x eps CD Cg : ℝ) : Prop where
  nums : RankNums x eps CD D.R.m D.R.f D.R.k (Real.log D.host.rdE) (D.s.Del : ℝ)
  g_win : ∀ i, ((D.R.k : ℝ) * bx x eps) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ bx x eps ^ Cg
  gap : ∀ τ (j : ℕ) (h : j + 1 < D.R.m), x ^ (eps / 100) * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * x ^ eps ≤
    (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)
  cloud : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ)
  off : ∀ τ, ¬ Top D τ → 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) ≤ uFirst D τ - vFirst D τ ∧
    uFirst D τ - vFirst D τ ≤ 8 * (D.R.k : ℝ) * (D.s.Del : ℝ) ∧ uLast D τ = vLast D τ - 1 / 2
  rd_lo : 2 ≤ D.host.rdE

def DuWin (C0 : ℝ) : Prop :=
  ∀ u, (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 ≤ (D.duS u : ℝ) ∧
    (D.duS u : ℝ) ≤ (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0

variable {D}

end GlobalTheory.Diag.PG

end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Ell

open Formalism.MainNotions.S

section Rep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))

def SmV (w : H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ Lie) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w

def dR (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : H := deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) 0

end Rep

def lieOf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {X | Xᴴ * G + G * X = 0}

structure Mod (n k r : ℕ) where
  ε : Fin n → Bool
  lam : Fin n → ℝ
  H : Type
  [nH : NormedAddCommGroup H]
  [iH : InnerProductSpace ℂ H]
  σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)
  G : Matrix (Fin n) (Fin n) ℂ
  fr : Matrix (Fin n) (Fin n) ℂ
  Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ
  Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  Vp : Type
  [nV : NormedAddCommGroup Vp]
  [iV : InnerProductSpace ℂ Vp]
  π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Vp →L[ℂ] Vp)
  hlam : Formalism.QuantumDeterminants.IsHCParam lam
  ds : IsDS ε lam σ
  fr_unit : IsUnit fr
  fr_gram : frᴴ * Formalism.REAL.Jm ε * fr = G
  Q_Qi : Q * Qi = 1
  Qi_Q : Qi * Q = 1
  Q_gram : Qᴴ * G * Q = Formalism.QuantumDeterminants.Hpk k r
  hz : Formalism.QuantumDeterminants.inWb k r z
  hT : 0 < Formalism.QuantumDeterminants.Tz k r z
  hc : ∀ a, c a ≠ 0
  hπ : IsHCTypeW k r z u π

attribute [instance] Mod.nH Mod.iH Mod.nV Mod.iV

namespace Mod

variable {n k r : ℕ} (M : Mod n k r)

end Mod

end GlobalTheory.Ell
end
end

section

noncomputable section

open scoped Classical

namespace GlobalTheory.LoopV

open NumberField Matrix Formalism.MainNotions.S

variable {K : Type} [Field K] {N : ℕ}

def StrUp (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, j ≤ i → x i j = 0

def StrLo (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, i ≤ j → x i j = 0

def expT (x : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  ∑ i ∈ Finset.range N, ((i.factorial : K)⁻¹) • x ^ i

def stabU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {a | IsUpUni a ∧ IsLoUni (Z * a * Z⁻¹)}

def lieU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {x | StrUp x ∧ StrLo (Z * x * Z.adjugate)}

def roots (w : Matrix (Fin N) (Fin N) K) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ ∃ i j, j < i ∧ w i q.1 ≠ 0 ∧ w j q.2 ≠ 0

def ofRoots (R : Finset (Fin N × Fin N)) (c : R → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if h : (i, j) ∈ R then c ⟨(i, j), h⟩ else if i = j then 1 else 0

def EntIn [NumberField K] (I : Ideal (𝓞 K)) (x : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = x i j

end GlobalTheory.LoopV

end
end
