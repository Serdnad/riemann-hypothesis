module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.CommOfBounded
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RelIdxNeZeroOfLeLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SelfDualStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Arith

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem rep_sqrt_sq : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d), Complex.ofReal_natCast]

theorem rep_conj_theta : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [cmTheta, map_div₀, map_add (f := _), map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat]
  ring

theorem rep_theta_add_conj : cmTheta b d + conj (cmTheta b d) = b := by
  rw [rep_conj_theta b d, cmTheta]
  ring

theorem rep_theta_mul_conj (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * conj (cmTheta b d) = (a : ℂ) * c := by
  have h4 : ((4 * (a : ℤ) * c : ℤ) : ℂ) = ((b ^ 2 + d : ℤ) : ℂ) := by rw [hOK]
  push_cast at h4
  have hs := rep_sqrt_sq d
  rw [rep_conj_theta b d, cmTheta]
  linear_combination (-1 / 4 : ℂ) * h4 - (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq +
    (1 / 4 : ℂ) * hs

theorem rep_elt_norm (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (p q : ℤ) :
    (lam * ((p : ℂ) * a + q * cmTheta b d)) * conj (lam * ((p : ℂ) * a + q * cmTheta b d)) =
      (Complex.normSq lam : ℂ) * a * ((a * p ^ 2 + b * p * q + c * q ^ 2 : ℤ) : ℂ) := by
  have h1 := rep_theta_add_conj b d
  have h2 := rep_theta_mul_conj a b c d hOK
  have hN := Complex.mul_conj lam
  simp only [map_mul, map_add (f := _), map_intCast, map_natCast]
  push_cast
  linear_combination ((p : ℂ) * a + q * cmTheta b d) * ((p : ℂ) * a + q * conj (cmTheta b d)) * hN +
    (Complex.normSq lam : ℂ) * p * q * a * h1 + (Complex.normSq lam : ℂ) * q ^ 2 * h2

theorem rep_omega1 : (cmL a b d ha hd lam hlam).ω₁ = lam * a := rfl
theorem rep_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl

theorem rep_area_ne : area (cmL a b d ha hd lam hlam) ≠ 0 := by
  rw [area, rep_omega1, rep_omega2, abs_ne_zero]
  have him : (conj (lam * a) * (lam * cmTheta b d)).im =
      Complex.normSq lam * a * (Real.sqrt d / 2) := by
    rw [show conj (lam * a) * (lam * cmTheta b d) = (lam * conj lam) * a * cmTheta b d by
      simp only [map_mul, map_natCast]; ring, Complex.mul_conj,
      show ((Complex.normSq lam : ℝ) : ℂ) * a * cmTheta b d =
        ((Complex.normSq lam * a : ℝ) : ℂ) * cmTheta b d by push_cast; ring, Complex.im_ofReal_mul]
    simp [cmTheta]
  rw [him]
  exact ne_of_gt (mul_pos (mul_pos (Complex.normSq_pos.2 hlam) (Nat.cast_pos.2 ha))
    (div_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hd)) two_pos))

def repKappa : ℂ := ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * (Complex.normSq lam : ℂ) * a

theorem rep_kappa_ne : repKappa a b d ha hd lam hlam ≠ 0 := by
  unfold repKappa
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.2 (rep_area_ne a b d ha hd lam hlam)))
    (Complex.ofReal_ne_zero.2 (Complex.normSq_pos.2 hlam).ne')) (Nat.cast_ne_zero.2 ha.ne')

variable (m : Type) [Fintype m] [DecidableEq m]

theorem rep_norm_f (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (x y : ℤ) (i₀ : m) :
    stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
      repKappa a b d ha hd lam hlam * ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) := by
  rw [rep_H_apply, Fintype.sum_eq_single i₀ (fun i hi => by simp [fvec, hi])]
  simp only [fvec, Pi.single_eq_same]
  rw [rep_elt_norm a b c d lam hOK x y]
  unfold repKappa
  ring

theorem rep_fvec_mem (x y : ℤ) (i₀ : m) : fvec a b d lam x y i₀ ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup]
  intro i
  by_cases h : i = i₀
  · subst h
    simp only [fvec, Pi.single_eq_same]
    exact PeriodPair.mem_lattice.2 ⟨x, y, by rw [rep_omega1, rep_omega2]; ring⟩
  · simp only [fvec, Pi.single_eq_of_ne h]
    exact zero_mem _

end Arith

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma stdH_symm (L : PeriodPair) (x y : m → ℂ) : stdH L m y x = conj (stdH L m x y) := by

  rw [stdH_apply, stdH_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma stdH_single_zero (L : PeriodPair) (j : m) (w : ℂ) {z : m → ℂ} (hz : z j = 0) :
    stdH L m (Pi.single j w) z = 0 := by
  rw [stdH_apply]
  have hsum : ∑ i, (Pi.single j w : m → ℂ) i * conj (z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = j
    · subst h
      rw [hz, map_zero, mul_zero]
    · simp [h]
  rw [hsum, zero_mul]

private theorem stdH_sub_eq_and_add_conj_eq_of_stdH_eq (L : PeriodPair) (v f' : m → ℂ)
    (hvv : PI.ULS.stdH L m v v = PI.ULS.stdH L m f' f') :
    PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' ∧
      PI.ULS.stdH L m v (v - f') + conj (PI.ULS.stdH L m v (v - f')) =
        PI.ULS.stdH L m (v - f') (v - f') := by
  have h1 : PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' :=
    map_sub (PI.ULS.stdH L m v) v f'
  refine ⟨h1, ?_⟩
  have h2 : PI.ULS.stdH L m (v - f') (v - f') =
      PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' - (PI.ULS.stdH L m f' v - PI.ULS.stdH L m f' f') := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [h1, h2, map_sub, ← stdH_symm L v f', ← stdH_symm L v v, hvv]
  ring

private theorem isKv_sub_stdH_smul {L : PeriodPair} {e : ℤ}
    (hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = (e : ℂ)) (hl0 : lam ≠ 0) {z w : m → ℂ} {t : ℂ}
    (ht : IsK b d t) (hz : IsKv b d lam z) (hw : IsKv b d lam w) :
    IsKv b d lam (w - ((kappa L lam * t)⁻¹ * PI.ULS.stdH L m w z) • z) := by
  obtain ⟨s, hs, hH⟩ := isK_H hn L hl0 hw hz
  rw [hH, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ (kappa_ne L hl0)]
  exact isKv_sub hw (isKv_smul hn (isK_mul hn (isK_inv hn ht) hs) hz)

lemma qrefl_to (hok : CmOK a b c d) (v f' : m → ℂ)
    (hvv : stdH (cmL a b d ha hd lam hlam) m v v = stdH (cmL a b d ha hd lam hlam) m f' f')
    (hne : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v f' ≠ 0)
    (hvK : IsKv b d lam v) (hfK : IsKv b d lam f') :
    ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      σ v = f' ∧ ∀ w, stdH (cmL a b d ha hd lam hlam) m w (v - f') = 0 → σ w = w := by
  obtain ⟨hvz, hκ⟩ := stdH_sub_eq_and_add_conj_eq_of_stdH_eq (PI.ULS.cmL a b d ha hd lam hlam) v f' hvv
  have hκ0 : PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f') ≠ 0 := by
    rw [hvz]; exact hne
  have hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = ((a * c : ℤ) : ℂ) := by
    rw [theta_norm hok.1]; push_cast; ring
  have hzK : IsKv b d lam (v - f') := isKv_sub hvK hfK
  obtain ⟨t, ht, htF⟩ := isK_H hn (PI.ULS.cmL a b d ha hd lam hlam) hlam hvK hzK
  have htF' : conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')) =
      kappa (PI.ULS.cmL a b d ha hd lam hlam) lam * conj t := by
    rw [htF, map_mul, kappa_conj]
  obtain ⟨σ, hσ⟩ : ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      σ = qequiv (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m) (v - f') hκ0 hκ := ⟨_, rfl⟩
  have hσapp : ∀ x, σ x = x - ((PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f'))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, qequiv_apply]
  have hσsymm : ∀ x, σ.symm x = x - ((conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, ← qmap_apply]; rfl
  have hs1 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega1, mul_div_cancel_left₀ _ hlam]
      exact_mod_cast isK_int (b := b) (d := d) (a : ℤ)) i
  have hs2 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega2, mul_div_cancel_left₀ _ hlam]
      exact isK_theta) i
  have hφ : ∀ x, IsKv b d lam x → IsKv b d lam ((σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσapp, htF]
    exact isKv_sub_stdH_smul hn hlam ht hzK hx
  have hψ : ∀ x, IsKv b d lam x →
      IsKv b d lam ((σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσsymm, htF']
    exact isKv_sub_stdH_smul hn hlam (isK_conj ht) hzK hx
  obtain ⟨N, hN, hN1⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hφ _ (hs1 i)) (fun i => hφ _ (hs2 i))
  obtain ⟨N', hN', hN2⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hψ _ (hs1 i)) (fun i => hψ _ (hs2 i))
  have hidx := comm_of_bounded σ hN hN' (fun s hs => hN1 s hs) (fun s hs => hN2 s hs)
  refine ⟨σ, ?_, hidx.1, hidx.2, ?_, ?_⟩
  · rw [hσ]
    exact qequiv_isom _ (fun x y => stdH_symm _ x y) _ hκ0 hκ
  · rw [hσapp, inv_mul_cancel₀ hκ0, one_smul, sub_sub_cancel]
  · intro w hw
    rw [hσapp, hw, mul_zero, zero_smul, sub_zero]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
