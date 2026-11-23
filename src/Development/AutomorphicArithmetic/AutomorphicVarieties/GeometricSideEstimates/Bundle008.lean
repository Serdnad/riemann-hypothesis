module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle002
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic

private theorem log_bound {T D C H q : ℝ} {N M : ℕ} (hT : 1 ≤ T) (hC : 1 ≤ C) (hH : 1 ≤ H) (hq : 1 ≤ q)
    (hHq : H ≤ 2 * q) (h : T ≤ D / ((C * H ^ N)⁻¹) ^ M) :
    Real.log T ≤ (|Real.log D| + M * Real.log C + M * N) * (1 + Real.log q) := by
  have hC0 : 0 < C := one_pos.trans_le hC
  have hH0 : 0 < H := one_pos.trans_le hH
  have hq0 : 0 < q := one_pos.trans_le hq
  rw [inv_pow, div_inv_eq_mul] at h
  have hp : 0 < (C * H ^ N) ^ M := by positivity
  have hD : 0 < D := (mul_pos_iff_of_pos_right hp).1 (one_pos.trans_le (hT.trans h))
  have h1 : Real.log T ≤ Real.log D + M * (Real.log C + N * Real.log H) := by
    have := Real.log_le_log (one_pos.trans_le hT) h
    rwa [Real.log_mul hD.ne' hp.ne', Real.log_pow, Real.log_mul hC0.ne' (by positivity), Real.log_pow] at this
  have h2 : Real.log H ≤ 1 + Real.log q := by
    have := Real.log_le_log hH0 hHq
    rw [Real.log_mul two_ne_zero hq0.ne'] at this
    have h3 := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
    linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have h4 : (M : ℝ) * N * Real.log H ≤ M * N * (1 + Real.log q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : 0 ≤ (|Real.log D| + M * Real.log C) * Real.log q := by positivity
  have h6 := le_abs_self (Real.log D)
  nlinarith

theorem UpperTheory.hermitian_space_log_estimate :
    FnLe := by
  intro E _ _ _ a ha L hL
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨M, hsc⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨D, -, hup⟩ := UpperTheory.geometric_side_upper_bound M
  obtain ⟨-, hrt, hγ, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨hTh, -⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  refine ⟨|Real.log D| + M * Real.log C + M * N, fun g => ?_⟩
  have hq : 1 ≤ qht g := (UpperTheory.V.Lit.Geo.qhtFacts E a).1 g
  obtain ⟨γ, hlt⟩ := exists_lt_of_ciInf_lt (show qht g < 2 * qht g by linarith)
  change AutomorphicForm.height (K := E) (ratGL E a γ * rt g) < _ at hlt
  have hH := AutomorphicForm.one_le_height (K := E) (ratGL E a γ * rt g)
  have hCH : 1 ≤ C * AutomorphicForm.height (K := E) (ratGL E a γ * rt g) ^ N :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hH)
  refine log_bound (hTh g).1 hC hH hq hlt.le ?_
  refine hup _ _ (0 : lat L g) _ (hsc g) (inv_pos.2 (one_pos.trans_le hCH)) (inv_le_one_of_one_le₀ hCH) fun v hv => ?_
  have e : (v.1 ᵥ* (γ⁻¹).val) ᵥ* γ.val = v.1 := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hw := hγ γ (rt g) (v.1 ᵥ* (γ⁻¹).val)
  rw [e, (hrt g).2.2] at hw
  have h1 := hmin (ratGL E a γ * rt g) (v.1 ᵥ* (γ⁻¹).val)
    (by
      change ptF _ _ ∈ L
      rw [hw.1]
      exact v.2)
    (fun h0 => hv (Subtype.ext (by
      rw [← e, h0, Matrix.zero_vecMul]
      rfl)))
  rw [hw.2] at h1
  rw [inv_le_iff_one_le_mul₀' (one_pos.trans_le hCH)]
  exact h1
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

noncomputable section

namespace UpperTheory.V.Geo.SmoothSumOrder

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem smooth_inv (l : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (fun y : Lie E a => l (Ring.inverse (Matrix.of y))) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  intro y hy
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hu : IsUnit (S y) := hy
  have h : ContDiffAt ℝ ∞ Ring.inverse (S y) := by
    simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  exact ((LinearMap.toContinuousLinearMap l).contDiff.contDiffAt.comp y
    (h.comp y S.contDiff.contDiffAt)).contDiffWithinAt

end

private def rmul (M : Matrix (Fin a) (Fin a) (Cinf E)) : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E) where
  toFun v := v ᵥ* M
  map_add' v w := Matrix.add_vecMul _ _ _
  map_smul' c v := Matrix.smul_vecMul _ _ _

private def lmul (v : Fin a → Cinf E) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] (Fin a → Cinf E) where
  toFun M := v ᵥ* M
  map_add' M M' := Matrix.vecMul_add _ _ _
  map_smul' c M := Matrix.vecMul_smul _ _ _

private theorem order (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ) (hx : Scale (fun i => qf (x i)) N) (n : ℕ) :
    ∀ P ∈ poly E a, ContDiffOn ℝ n (msum x P) (invSet E a) := by
  induction n with
  | zero =>
    intro P hP
    exact contDiffOn_zero.2 fun y hy =>
      (UpperTheory.sum_der E a ι x N hx P hP y hy).2.1.continuousAt.continuousWithinAt
  | succ n ih =>
    intro P hP
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (UpperTheory.sum_der E a ι x N hx P hP y hy).2.1.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_clm_apply]
    intro Z
    let b := Module.finBasis ℝ (Matrix (Fin a) (Fin a) (Cinf E))
    choose Q hQ hQ' using fun j => (UpperTheory.quadratic_form_gradient_formula E a P hP).2.2 (rmul (b j))
    let l := fun j => (b.coord j).comp (LinearMap.mulRight ℝ (Matrix.of Z))
    have hs : ContDiffOn ℝ n (fun y : Lie E a => ∑ j, l j (Ring.inverse (Matrix.of y)) • msum x (Q j) y)
        (invSet E a) :=
      ContDiffOn.sum fun j _ => ((smooth_inv (l j)).of_le (by exact_mod_cast le_top)).smul (ih _ (hQ j))
    refine hs.congr fun y hy => ?_
    have hu : IsUnit (Matrix.of y) := hy
    have hterm : ∀ i, fderiv ℝ (pg P) (x i ᵥ* Matrix.of y) (x i ᵥ* Matrix.of Z) =
        ∑ j, l j (Ring.inverse (Matrix.of y)) • pg (Q j) (x i ᵥ* Matrix.of y) := by
      intro i
      have e1 : x i ᵥ* Matrix.of Z = lmul (x i ᵥ* Matrix.of y) (Ring.inverse (Matrix.of y) * Matrix.of Z) := by
        change _ = (x i ᵥ* Matrix.of y) ᵥ* _
        rw [Matrix.vecMul_vecMul, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

      rw [e1, ← b.sum_repr (Ring.inverse (Matrix.of y) * Matrix.of Z), map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, ← hQ' j]
      rfl
    rw [(UpperTheory.sum_der E a ι x N hx P hP y hy).2.2 Z, tsum_congr hterm,
      Summable.tsum_finsetSum fun j _ => (UpperTheory.sum_der E a ι x N hx _ (hQ j) y hy).1.const_smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (UpperTheory.sum_der E a ι x N hx _ (hQ j) y hy).1.tsum_const_smul _

end UpperTheory.V.Geo.SmoothSumOrder

theorem UpperTheory.smooth_sum_left_right_mul_order :
    SumSm := fun _ _ _ _ ι x N hx P hP =>
  contDiffOn_infty.2 fun n => UpperTheory.V.Geo.SmoothSumOrder.order ι x N hx n P hP
end
end

section

open UpperTheory.V.Lit.Geo
open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

theorem UpperTheory.hermitian_space_moment_identity :
    MomQuad := by
  intro E _ _ _ a ha L hL g p
  obtain ⟨-, h2⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have hP : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E),
      (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
    intro i j w
    have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => star (x i w)
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }, rfl⟩
    have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => x j w
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }, rfl⟩
    exact (poly E a).mul_mem h1 h2
  have hS : ∀ (w : NumberField.InfinitePlace E) (i j : Fin a), HasSum
      (fun v : lat L g => (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) (pt (rt g) v.1) * p j i w).re)
      (gsum L (pg (fun x : Fin a → Cinf E => star (x i w) * x j w)) g * p j i w).re := by
    intro w i j
    exact Complex.hasSum_re ((((h2 _ (hP i j w)).1 g).hasSum).mul_right (p j i w))
  have hT := hasSum_sum (s := Finset.univ) fun w _ => hasSum_sum (s := Finset.univ) fun i _ =>
    hasSum_sum (s := Finset.univ) fun j _ => hS w i j
  have hq : ∀ x : Fin a → Cinf E, quad p x * gauss x = ∑ w : NumberField.InfinitePlace E, ∑ i, ∑ j,
      (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) x * p j i w).re := by
    intro x
    simp only [quad, Finset.sum_mul, pg, dotProduct, Matrix.vecMul, Finset.sum_apply, Complex.re_sum, Pi.mul_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.re_mul_ofReal]
    congr 1
    ring
  simp only [hq]
  rw [hT.tsum_eq]
  simp only [UpperTheory.V.Lit.Bor.trF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Complex.re_sum, Finset.sum_div, Pi.mul_apply]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.div_ofReal_re]
  congr 1
  change mean L _ g * _ = _
  rw [mean]
  ring
end
