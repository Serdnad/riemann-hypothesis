module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle002
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Matrix.Normed
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle008
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle001

@[expose] public section

section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

variable {N : ℕ}

def Hc (N : ℕ) (t : ℂ) (T : Matrix (Fin N) (Fin N) ℂ) : ℂ := (1 + T).det ^ t

theorem analyticAt_Hc (N : ℕ) (t : ℂ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ∈ Complex.slitPlane) :
    AnalyticAt ℂ (Hc N t) T0 := by
  unfold Hc
  have h1 : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (CK.analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const h

theorem one_det_slit : (1 + (0 : Matrix (Fin N) (Fin N) ℂ)).det ∈ Complex.slitPlane := by
  simpa using Complex.one_mem_slitPlane

theorem analyticAt_determinant_power_zero (N : ℕ) (t : ℂ) : AnalyticAt ℂ (Hc N t) 0 := analyticAt_Hc N t 0 one_det_slit

theorem det_phiF_slit (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    (1 + phiF X).det ∈ Complex.slitPlane := by rw [det_phiF]; exact hX

theorem fderiv_determinant_power_corner (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) = t * Hc N t (piF X) := by
  have hD := det_phiF_slit X hX
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) (analyticAt_Hc _ t _ hD).differentiableAt
  have hD0 : (1 + piF X).det ≠ 0 := Complex.slitPlane_ne_zero hX
  have hfun : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 0 1))
      = fun s : ℂ => ((1 + s) * (1 + piF X).det) ^ t := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_corner_perturbation]
  rw [hfun] at h1
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * (1 + piF X).det) (1 * (1 + piF X).det) 0 :=
    ((hasDerivAt_id' (0 : ℂ)).const_add 1).mul_const _
  have h2 := hf.cpow_const (c := t) (by simpa using hX)
  refine (h1.unique h2).trans ?_
  simp only [Hc, add_zero, one_mul]
  rw [Complex.cpow_sub _ _ hD0, Complex.cpow_one]
  field_simp

theorem fderiv_determinant_power_column_neg (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = -fderiv ℂ (Hc N t) (piF X) (colQ X c) := by
  have hA : AnalyticAt ℂ (Hc (N + 1) t) (phiF X) := analyticAt_Hc _ t _ (det_phiF_slit X hX)
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) hA.differentiableAt
  have e : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 c.succ 1)) =
      fun s : ℂ => Hc N t (piF X + s • (-colQ X c)) := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_column_perturbation, smul_neg, ← sub_eq_add_neg, add_sub_assoc]
  rw [e] at h1
  have hB : AnalyticAt ℂ (Hc N t) (piF X) := analyticAt_Hc _ t _ hX
  have h2 := fderiv_line (Hc N t) (piF X) (-colQ X c) hB.differentiableAt
  exact (h1.unique h2).trans (map_neg _ _)

theorem ev_piFc (N : ℕ) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ∈ Complex.slitPlane := by
  have hc : ContinuousAt (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det) 0 :=
    ((CK.analyticAt_det _).comp (analyticAt_const.add (analyticAt_piF 0))).continuousAt
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ∈ Complex.slitPlane := by
    rw [piF_zero, add_zero, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  exact hc.eventually_mem (Complex.isOpen_slitPlane.mem_nhds h0)

theorem iterated_derivative_corner_case (t : ℂ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
  set G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → ℂ :=
    fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1) with hG
  have hGa : AnalyticAt ℂ G 0 := analyticAt_fderiv_apply (Hc (N + 1) t) 0 _ (analyticAt_determinant_power_zero (N + 1) t)
  have e1 := icompL G phiF phiF_add phiF_smul 0 0 phiF_zero hGa N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k.succ (e k).succ 1)
    (fun i => phiF_single _ _)
  rw [← e1]
  have hev : (G ∘ phiF) =ᶠ[𝓝 0] (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => t * Hc N t (piF X)) := by
    filter_upwards [ev_piFc N] with X hX
    exact fderiv_determinant_power_corner t X hX
  rw [(hev.iteratedFDeriv ℂ N).eq_of_nhds]
  have hHa : AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => Hc N t (piF X)) 0 := by
    have h0 : AnalyticAt ℂ (Hc N t) (piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)) := by
      rw [piF_zero]
      exact analyticAt_determinant_power_zero N t
    exact h0.comp (analyticAt_piF 0)
  rw [iconst_mul _ 0 t hHa N]
  congr 1
  exact icompL (Hc N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero N t) N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k (e k) 1)
    (fun i => piF_single_succ _ _)

def fsumc (t : ℂ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1)

theorem fderiv_determinant_power_column (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) : fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsumc t c X := by

  rw [fderiv_determinant_power_column_neg t X hX c, colQ_expand, map_sum]
  simp only [map_smul, smul_eq_mul, fsumc]

theorem analyticAt_fsumc (t : ℂ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (h : (1 + piF X0).det ∈ Complex.slitPlane) : AnalyticAt ℂ (fsumc t c) X0 := by
  have hs := Finset.analyticAt_sum
    (f := fun k (X : Matrix (Fin N) (Fin (N + 1)) ℂ) => X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1))
    Finset.univ (fun k _ => (analyticAt_entry k 0 X0).mul
      ((analyticAt_fderiv_apply (Hc N t) (piF X0) _ (analyticAt_Hc N t _ h)).comp (analyticAt_piF X0)))
  rw [Finset.sum_fn] at hs
  exact hs.neg

theorem fsum_linec (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsumc t c (y + s • Matrix.single k0 0 1) =
      fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  simp only [fsumc]
  rw [piF_add, piF_smul, piF_single_zero, smul_zero, add_zero]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, and_true, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem fderiv_fsumc (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (hy : (1 + piF y).det ∈ Complex.slitPlane) :
    fderiv ℂ (fsumc t c) y (Matrix.single k0 0 1) = -fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  have h1 := fderiv_line (fsumc t c) y (Matrix.single k0 0 1) (analyticAt_fsumc t c y hy).differentiableAt
  have hfun : (fun s : ℂ => fsumc t c (y + s • Matrix.single k0 0 1))
      = fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
    funext s
    exact fsum_linec t c k0 y s
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1))
      (0 - 1 * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1)) 0 :=
    (hasDerivAt_const _ _).sub ((hasDerivAt_id' (0 : ℂ)).mul_const _)
  refine (h1.unique h2).trans ?_
  ring

end PositivityTheory.Rg.Sw.HSt.CKC
end
end

section

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DomZ (n : ℕ) : Set (M2 n) := {x | x ∈ Dom n ∧ (u1 x).det * (ub1 x).det ∈ Complex.slitPlane}

def KappaC : Prop :=
  ∀ (N : ℕ) (t : ℂ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) = ∏ i ∈ Finset.range N, (t + i)

def DjZ : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (j : ℕ) (z : ℂ) (x : M2 n), j ≤ n → x ∈ DomZ n →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z)) *
      fz m e z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹

def FzHol : Prop :=
  ∀ (n m : ℕ) (e : ℤ), IsOpen (DomZ n) ∧ GSet n ⊆ DomZ n ∧
    AnalyticOnNhd ℂ (fun p : ℂ × M2 n => fz m e p.1 p.2) (Set.univ ×ˢ DomZ n)

end PositivityTheory.Rg.Sw.HSt
end
end

section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.MI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem curve_zero (x Y : M2 n) : x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = x := by
  simp

theorem rC_eq (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) :
    rC Z F x = deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z1 Z))) 0 +
      Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z2 Z))) 0 := rfl

theorem deriv_curve_of_hasFDerivAt {F : M2 n → ℂ} {D : M2 n →L[ℝ] ℂ} {x : M2 n} (hF : HasFDerivAt F D x) (Y : M2 n) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 = D (x * Y) := by
  exact (hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_curve x Y) (curve_zero x Y).symm).deriv

theorem rC_of_diff {F : M2 n → ℂ} {x : M2 n} (hF : DifferentiableAt ℝ F x) (Z : M2 n) :
    rC Z F x = fderiv ℝ F x (x * Z1 Z) + Complex.I * fderiv ℝ F x (x * Z2 Z) := by
  rw [rC_eq, deriv_curve_of_hasFDerivAt hF.hasFDerivAt, deriv_curve_of_hasFDerivAt hF.hasFDerivAt]

theorem rC_congr {F F' : M2 n → ℂ} {O : Set (M2 n)} (hO : IsOpen O) {x : M2 n} (hx : x ∈ O) (h : EqOn F F' O)
    (Z : M2 n) : rC Z F x = rC Z F' x := by
  have key : ∀ Y : M2 n, deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • Y))) 0 := by
    intro Y
    apply Filter.EventuallyEq.deriv_eq
    have hc := (hasDerivAt_curve x Y).continuousAt
    have hO' : O ∈ 𝓝 (x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) := by
      rw [curve_zero]
      exact hO.mem_nhds hx
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    exact h ht
  rw [rC_eq, rC_eq, key, key]

end PositivityTheory.Rg.Sw.HSt.MI
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem inv_of_inG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) := by
  refine Matrix.inv_eq_left_inv ?_
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
    _ = 1 := by rw [h, JJ_sq]; simp

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have h : xᴴ * JJ n * x = JJ n := hx
    calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
      _ = 1 := by rw [h, JJ_sq]; simp
  exact (Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)

theorem isUnit_det_of_inG {x : M2 n} (hx : InG x) : IsUnit x.det :=
  (Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)

theorem inverse_first_block_eq_conjTranspose {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  rw [ub1, inv_of_inG hx, u1]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]
  abel

theorem det_first_block_ne_zero_group {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 := by
  have := PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)
  simpa [u1] using this

def Nq (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q 0 0 * Cmi n

theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.mp cm_mul_cmi

theorem Nq_sq (Q : Matrix (Fin n) (Fin n) ℂ) : Nq Q * Nq Q = 0 := by
  have : fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n) := by
    rw [fromBlocks_multiply]; simp [fromBlocks_zero]
  calc Nq Q * Nq Q = Cm n * fromBlocks 0 Q 0 0 * (Cmi n * Cm n) * fromBlocks 0 Q 0 0 * Cmi n := by
        simp only [Nq, Matrix.mul_assoc]
    _ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp

theorem mX_eq (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : mX (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 = 1 + s • Nq Q := by
  have e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Nq Q := by
  have := mX_eq Q 1
  rw [one_smul, one_smul] at this
  rw [lowQ, this]; abel

theorem Nq_blocks (Q : Matrix (Fin n) (Fin n) ℂ) :
    Nq Q = fromBlocks (-(1 / 2 : ℂ) • Q) ((Complex.I / 2) • Q) ((Complex.I / 2) • Q) ((1 / 2 : ℂ) • Q) := by
  rw [Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem inv_mul_lower {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    (x * (1 + s • Nq Q))⁻¹ = (1 - s • Nq Q) * x⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hN := Nq_sq Q
  have e : (1 + s • Nq Q) * (1 - s • Nq Q) = (1 : M2 n) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]
    simp
  have hx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x ((Matrix.isUnit_iff_isUnit_det x).mp hx)
  calc x * (1 + s • Nq Q) * ((1 - s • Nq Q) * x⁻¹) = x * ((1 + s • Nq Q) * (1 - s • Nq Q)) * x⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, Matrix.mul_one, hx']

theorem upper_left_block_sub (A B : M2 n) : (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_sub (A B : M2 n) : (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_mul_eq (A B : M2 n) : (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem inverse_first_block_lowering {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    ub1 (x * (1 + s • Nq Q)) = ub1 x - s • (Q * ub2 x) := by
  rw [ub1, inv_mul_lower hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, upper_left_block_sub, lower_left_block_sub, upper_left_block_smul,
    lower_left_block_smul, upper_left_block_mul_eq, toBlocks₂₁_mul, Nq_blocks, ub1, ub2]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_sub, smul_neg, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem first_block_lowering_invariant (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : u1 (x * (1 + s • Nq Q)) = u1 x := by
  have := (uAct n x 1 (s • Q) 0 1).1
  rw [mX_eq] at this
  rw [this]; simp

theorem det_lower (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : (x * (1 + s • Nq Q)).det = x.det := by
  rw [← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]
  have : (Cm n).det * (Cmi n).det = 1 := by rw [← det_mul, cm_mul_cmi, det_one]
  simp only [det_one, mul_one]
  linear_combination x.det * this

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end
