module

public import Formalism.EllipticTorsion.Bundle002
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Polynomial
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.ELL

theorem legendre_invariant : LegendreInv := by
  intro K _ l
  refine ⟨?_, ?_⟩ <;>
  simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

theorem deuring_invariant : DeuringInv := by
  intro K _ a
  refine ⟨?_, ?_⟩ <;>
  simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

end Formalism.ELL
end

section

noncomputable section

namespace Formalism.ELL.IntegerValuedContinuity

theorem continuous_eval {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (P : Polynomial K) :
    Continuous fun b : ℤ_[p] => P.eval (algebraMap ℚ_[p] K (b : ℚ_[p])) := by
  have h1 : Continuous (algebraMap ℚ_[p] K) := by
    have : (⇑(algebraMap ℚ_[p] K)) = fun c => c • (1 : K) := by
      funext c; exact Algebra.algebraMap_eq_smul_one c
    rw [this]; exact continuous_id.smul continuous_const
  have h2 : Continuous (fun b : ℤ_[p] => (b : ℚ_[p])) := continuous_subtype_val
  exact (P.continuous).comp (h1.comp h2)

end Formalism.ELL.IntegerValuedContinuity

namespace Formalism.ELL

theorem integer_valued_padic_integers : IntValuedZp := by
  intro p _ K _ _ P hP b
  have hc := Formalism.ELL.IntegerValuedContinuity.continuous_eval (p := p) (K := K) P
  have hclosed : IsClosed {b : ℤ_[p] | ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1} :=
    isClosed_le (continuous_norm.comp hc) continuous_const
  refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
  intro n
  show ‖P.eval (algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]))‖ ≤ 1
  have : algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]) = (n : K) := by
    simp
  rw [this]; exact hP n

end Formalism.ELL
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.ELL.PadicLogarithmSubstitution

open Formalism.G Formalism.ELL

section Integral

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem integralMv_one {σ : Type*} : IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integralMv_mul {σ : Type*} {f g : MvPowerSeries σ K} (hf : IntegralMv f)
    (hg : IntegralMv g) : IntegralMv (f * g) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem integralMv_pow {σ : Type*} {f : MvPowerSeries σ K} (hf : IntegralMv f) (n : ℕ) :
    IntegralMv (f ^ n) := by
  induction n with
  | zero => simpa using (integralMv_one (K := K) (σ := σ))
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hf

theorem norm_finsum_le_one {f : ℕ → K} (h : ∀ n, ‖f n‖ ≤ 1) : ‖∑ᶠ n, f n‖ ≤ 1 := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => h i)
  · rw [finsum_of_infinite_support hs]; simp

theorem integralMv_subst {σ : Type*} {a : PowerSeries K} (ha : IntegralPS a)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0) (hf : IntegralMv f) :
    IntegralMv (a.subst f) := by
  intro d
  rw [PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hf0)]
  refine norm_finsum_le_one (fun n => ?_)
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (ha n) (norm_nonneg _) (integralMv_pow hf n d)

end Integral

section LogId

variable {K : Type*} [Field K] [CharZero K]

def geometricSignedSeries (K : Type*) [Field K] [CharZero K] : PowerSeries K :=
  mk fun n => algebraMap ℚ K ((-1 : ℚ) ^ n)

theorem geomAlt_mul : geometricSignedSeries K * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add (f := _), mul_comm]
  rcases n with _ | m
  · simp [geometricSignedSeries]
  · rw [coeff_succ_X_mul]
    simp only [geometricSignedSeries, coeff_mk, coeff_one]
    rw [← map_add (f := _)]
    have : ((-1 : ℚ) ^ (m + 1) + (-1) ^ m) = 0 := by ring
    simp [this]

theorem log_subst_eq_smul (c : K) (B : PowerSeries K) (hB0 : constantCoeff B = 1)
    (hBd : (1 + X) * derivative B = c • B) :
    (log K).subst (B - 1) = c • log K := by
  have h0 : constantCoeff (B - 1) = 0 := by simp [hB0]
  have hS : HasSubst (B - 1) := HasSubst.of_constantCoeff_zero' h0
  have hone : (1 + X : PowerSeries K).subst (B - 1) = B := by
    rw [subst_add hS, subst_X hS, ← coe_substAlgHom hS, map_one]; ring
  have hGB : (geometricSignedSeries K).subst (B - 1) * B = 1 := by
    have hm := subst_mul hS (geometricSignedSeries K) (1 + X)
    rw [geomAlt_mul, hone, ← coe_substAlgHom hS, map_one] at hm
    rw [← coe_substAlgHom hS, ← hm]
  have hlog : derivative (log K) = geometricSignedSeries K := by
    rw [derivative_log]
    ext n
    simp [geometricSignedSeries]
  have hD : derivative ((log K).subst (B - 1)) = derivative (c • log K) := by
    have hX : (1 + X : PowerSeries K) ≠ 0 := by
      intro h
      have := congrArg constantCoeff h
      simp at this
    refine mul_right_cancel₀ hX ?_
    rw [derivative_subst hS, Derivation.map_smul, hlog]
    rw [map_sub, derivative_one, sub_zero, mul_assoc, mul_comm (derivative B), hBd,
      mul_smul_comm, hGB, smul_mul_assoc, geomAlt_mul]
  refine derivative.ext hD ?_
  rw [show constantCoeff (c • log K) = 0 by simp]
  exact constantCoeff_subst_eq_zero h0 _ constantCoeff_log

end LogId

section Binom

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]

def phi : ℤ_[p] →+* K := (algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom

def bser (b : ℤ_[p]) : PowerSeries K := mk fun n => phi p K (Ring.choose b n)

theorem choose_rec (b : ℤ_[p]) (n : ℕ) :
    ((n + 1 : ℕ) : ℤ_[p]) * Ring.choose b (n + 1) = (b - n) * Ring.choose b n := by
  have h := Ring.choose_smul_choose b (Nat.le_succ n)
  rw [Nat.choose_succ_self_right, show n.succ - n = 1 by omega, Ring.choose_one_right,
    nsmul_eq_mul] at h
  rw [mul_comm (b - (n : ℤ_[p]))]
  exact h

theorem bser_constantCoeff (b : ℤ_[p]) : constantCoeff (bser p K b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, bser, coeff_mk, Ring.choose_zero_right, map_one]

theorem bser_deriv (b : ℤ_[p]) :
    (1 + X) * derivative (bser p K b) = phi p K b • bser p K b := by
  ext n
  have hr := congrArg (phi p K) (choose_rec p b n)
  simp only [map_mul, map_sub, map_natCast] at hr
  rw [add_mul, one_mul, map_add (f := _), coeff_derivative, coeff_smul]
  rcases n with _ | m
  · simp only [bser, coeff_mk, coeff_zero_X_mul, smul_eq_mul] at hr ⊢
    push_cast at hr ⊢
    linear_combination hr
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp only [bser, coeff_mk, smul_eq_mul] at hr ⊢
    push_cast at hr ⊢
    linear_combination hr

theorem norm_phi_le (z : ℤ_[p]) : ‖phi p K z‖ ≤ 1 := by
  rw [phi, RingHom.comp_apply, norm_algebraMap']
  exact PadicInt.norm_le_one z

theorem integralPS_bser_sub_one [IsUltrametricDist K] (b : ℤ_[p]) :
    IntegralPS (bser p K b - 1) := by
  intro n
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [bser, coeff_mk]; exact norm_phi_le p K _
  · rw [norm_neg, coeff_one]; split_ifs <;> simp

end Binom

end PadicLogarithmSubstitution

open PadicLogarithmSubstitution in
theorem N_padic_integer_smul : Formalism.ELL.NZpSmul := by
  intro p _ K _ _ _ _ σ G hG b
  obtain ⟨f, hf0, hfi, rfl⟩ := hG
  have hB0 := bser_constantCoeff p K b
  have h0 : constantCoeff (bser p K b - 1) = 0 := by simp [hB0]
  have hS : HasSubst (bser p K b - 1) := HasSubst.of_constantCoeff_zero' h0
  have hf : HasSubst f := HasSubst.of_constantCoeff_zero hf0
  have hc : algebraMap ℚ_[p] K (b : ℚ_[p]) = phi p K b := rfl
  refine ⟨(bser p K b - 1).subst f, constantCoeff_subst_eq_zero hf0 _ h0,
    integralMv_subst (integralPS_bser_sub_one p K b) hf0 hfi, ?_⟩
  unfold logOnePlus
  rw [← subst_comp_subst_apply hS hf, log_subst_eq_smul _ _ hB0 (bser_deriv p K b),
    subst_smul hf, hc]

end Formalism.ELL
end
end

section

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := K) i H)

theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ j, MvPowerSeries.constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd

  rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy), Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR

end Formalism.ELL
end
end
