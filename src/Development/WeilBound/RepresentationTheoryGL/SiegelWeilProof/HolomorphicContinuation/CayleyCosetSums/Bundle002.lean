module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001

@[expose] public section

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem embOn_single_pf (s : Finset (Fin n)) (a b : s) :
    embOn s (Matrix.single a b (1 : ℂ)) = Matrix.single (a : Fin n) (b : Fin n) 1 := by
  ext i j
  by_cases hi : i = (a : Fin n) <;> by_cases hj : j = (b : Fin n)
  · subst hi hj
    simp [embOn, Matrix.single_apply]
  · simp only [embOn, Matrix.single_apply, hj, and_false, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]

theorem deriv_prod_range_sub_mul_prod_ne_zero (n m : ℕ) (hmn : m < n) :
    deriv (fun z : ℂ => (∏ i ∈ Finset.range (n - m), ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - (n - m)), ((i : ℂ) - m - z))) 0 ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
  have hm : n - (n - m) = m := by omega
  rw [hm, hk]
  set C : ℂ → ℂ := fun z => ∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℂ) - z) with hCdef
  set B : ℂ → ℂ := fun z => ∏ i ∈ Finset.range m, ((i : ℂ) - m - z) with hBdef
  have hfun : (fun z : ℂ => (∏ i ∈ Finset.range (k + 1), ((i : ℂ) - z)) *
      ∏ i ∈ Finset.range m, ((i : ℂ) - m - z)) = fun z => (C z * (0 - z)) * B z := by
    funext z
    rw [Finset.prod_range_succ']
    simp [C, B]
  have hC : DifferentiableAt ℂ C 0 := DifferentiableAt.fun_finsetProd (fun i _ => by fun_prop)
  have hB : DifferentiableAt ℂ B 0 := DifferentiableAt.fun_finsetProd (fun i _ => by fun_prop)
  have key : HasDerivAt (fun z => (C z * (0 - z)) * B z) ((C 0 * (-1)) * B 0) 0 := by
    have h := (hC.hasDerivAt.mul ((hasDerivAt_id (0 : ℂ)).const_sub 0)).mul hB.hasDerivAt
    convert h using 1 <;> first | rfl | simp
  rw [hfun, key.deriv]
  have hC0 : C 0 ≠ 0 := by
    simp only [C, sub_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.succ_ne_zero i)
  have hB0 : B 0 ≠ 0 := by
    simp only [B, sub_zero]
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.mp hi
    rw [sub_ne_zero]
    exact_mod_cast hi'.ne
  simp [hC0, hB0]

end PositivityTheory.Rg.Sw.HSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def fz (m : ℕ) (e : ℤ) (z : ℂ) (x : M2 n) : ℂ :=
  x.det ^ e * (u1 x).det ^ (-(m : ℤ)) * ((u1 x).det * (ub1 x).det) ^ (-z)

def sig (X : M2 n) : M2 n := -((JJ n)⁻¹ * Xᴴ * JJ n)

def rC (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) 0 +
    Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) 0

def lowQ (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 Q 0 1 - 1

def tOp {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (ρ : Kg → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F (x * ι k * a * nU (herm t) * b) * ψ t) ∂μ

def LocTau : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ Q : Matrix (Fin n) (Fin n) ℂ,
    ∃ (N : ℕ) (ρ : Fin N → Kg → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ) (a b : Fin N → M2 n) (D : ℂ → ℂ)
      (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) ∧ (∀ l, IsSingTest (ψ l)) ∧ (∀ l, InG (a l) ∧ InG (b l)) ∧
      Differentiable ℂ D ∧ D 0 ≠ 0 ∧ (∀ l, Differentiable ℂ (M l)) ∧
      ∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ ι (ρ l) (ψ l) (a l) (b l) (fz m e z) x

end PositivityTheory.Rg.Sw.HSt
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem det_gram_eq_zero (hmn : m < n) (x : Fin m → Fin n → ℂ) : (gramX (fun _ : Fin m => true) x).det = 0 := by
  have hg : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
    ext i j
    simp [gramX, evX, Qp, Qb, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_contra hne
  have hu : IsUnit ((Matrix.of x)ᴴ * Matrix.of x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_right (Matrix.of x)ᴴ (Matrix.of x)
  have h3 := Matrix.rank_le_height (Matrix.of x)
  simp only [Fintype.card_fin] at h1 h3
  omega

theorem trace_transpose_mul' (X Y : Matrix (Fin n) (Fin n) ℂ) : (Xᵀ * Y).trace = (Yᵀ * X).trace := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

end PositivityTheory.Rg.Sw.HSt.L3
end
end
