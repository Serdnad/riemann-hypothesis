module

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle005
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def nbar (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem inG_nbar (t : ℝ) : InG (nbar (n := n) t) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem nbar_block (y : M2 n) (t : ℝ) : (y * nbar t).toBlocks₂₁ = y.toBlocks₂₁ + (t : ℂ) • y.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [nbar, Matrix.fromBlocks_multiply]

private theorem JJ_mul_JJ_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem det_ne_of_inG (x : M2 n) (hx : InG x) : x.det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hx', JJ_mul_JJ_eq_neg_one, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem det_first_cayley_block_ne_group (x : M2 n) (hx : InG x) : (u1 x).det ≠ 0 := by
  apply PositivityTheory.Rg.Sw.HSt.LoweringDerivative.det_first_block_ne_zero_group <;> assumption

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem deriv_comp_mul_exp_smul_eq_fderiv (F : M2 n → ℂ) (x W : M2 n) (hF : DifferentiableAt ℂ F x) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) 0 = fderiv ℂ F x (x * W) := by
  have hL : HasDerivAt (fun t : ℝ => x * II.cE W t) (x * W) 0 := by
    let L : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 W)
  have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp [II.cE])
  have he : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) = fun t => F (x * II.cE W t) := by
    funext t
    simp only [II.cE, Complex.coe_smul]
  rw [he]
  exact h.deriv

theorem rC_eq (F : M2 n → ℂ) (x Z : M2 n) (hF : DifferentiableAt ℂ F x) : rC Z F x = fderiv ℂ F x (x * Z) := by
  unfold rC
  rw [deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _),
    ← Matrix.mul_smul, ← Matrix.mul_add, smul_smul]
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [hI, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem contDiffOn_inverse_first_block : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => ub1 x i j) {x | x.det ≠ 0} := by
  intro i j
  exact LVs.contDiffOn_inverse_first_block _ (fun x hx => isUnit_iff_ne_zero.2 hx) i j

theorem isOpen_det_ne : IsOpen {x : M2 n | x.det ≠ 0} :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem vanish_inv (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  obtain ⟨R, H0, κ, hR, hH0, hκ, hf⟩ := factor y b hy hb hc
  have key : ∀ s, fz m e 0 (y * nU (herm s) * b) * ψ s =
      ((y.det * b.det) ^ e * κ ^ (-(m : ℤ))) *
        (ψ s * (R * Rᴴ - Complex.I • (H0 + herm s)).det⁻¹ ^ m) := by
    intro s
    rw [fz_zero, hf, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one]
    simp only [mul_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, core2 hmn R hR H0 hH0 ψ hψ, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end
