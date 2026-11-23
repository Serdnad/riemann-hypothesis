module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle003
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem key_id (α β u ub : ℂ) (hα : α ≠ 0) (hu : 1 - u ≠ 0) (h1 : β - α * u ≠ 0) (h2 : α - β * ub ≠ 0)
    (hA : α - β * u * ub ≠ 0) :
    (Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub)) /
      (Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub)) * ((β - α * u) / (1 - u)) =
      β * (1 - u * ub) / (1 - β / α * (u * ub)) := by
  have hI := Complex.I_ne_zero
  have e1 : Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * (α - β * u * ub) / ((1 - u) * (α - β * ub)) := by
    field_simp; ring
  have e2 : Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * α * β * (1 - u * ub) / ((β - α * u) * (α - β * ub)) := by
    field_simp; ring
  have e3 : 1 - β / α * (u * ub) = (α - β * u * ub) / α := by field_simp
  rw [e1, e2, e3]
  field_simp

theorem pow_combine (c X Y S T : ℂ) (k : ℕ) (h : X * Y / S = T) :
    c * X ^ k * (Y ^ k * (S ^ k)⁻¹) = c * T ^ k := by
  rw [← h, div_pow, mul_pow]; ring

theorem cayley_val (k : ℕ) (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ext1 (U k m) (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) =
      ((k : ℂ) - 1) / (4 * Real.pi) * (eta a b * (1 - (r : ℂ) ^ 2) / (1 - eta a b ^ 2 * (r : ℂ) ^ 2)) ^ k := by
  set u := circleMap 0 r θ with hu_def
  have hnu : ‖u‖ = r := by simp [u, abs_of_pos hr0]
  have hu1 : (1 : ℂ) - u ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hnu; linarith
  have huu : u * conj u = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnu]; push_cast; ring
  have hn : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
    rw [← hnu, Complex.sq_norm, Complex.normSq_apply]; ring
  set z := Complex.I * (1 + u) / (1 - u) with hz_def
  have hz_im : z.im = (1 - r ^ 2) / Complex.normSq (1 - u) := by
    rw [hz_def, Complex.div_im, ← sub_div]
    congr 1
    simp
    nlinarith [hn]
  have hzpos : 0 < z.im := by
    rw [hz_im]
    apply div_pos
    · nlinarith
    · exact Complex.normSq_pos.2 hu1
  have hz : z.im ≠ 0 := hzpos.ne'
  set zP : P := ⟨z, hz⟩ with hzP
  have hzP1 : zP.1 = z := rfl
  have hzpos' : 0 < zP.1.im := hzpos
  have hext : ext1 (U k m) z = F k m zP := by
    unfold ext1; rw [dite_eq_left hz]; exact if_pos hzpos'
  have hab : 0 < a ^ 2 + b ^ 2 := by
    have := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb)); nlinarith [sq_nonneg a]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a ^ 2 + b ^ 2) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hab
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by rw [hs_def]; exact Real.sq_sqrt hab.le
  have hS0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hα0 : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hβ0 : (a : ℂ) - b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hden : den m z = (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold den; rw [h10, h11, hz_def]; push_cast; field_simp; ring
  have hnum : num m z = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold num; rw [h00, h01, hz_def]; field_simp
    linear_combination (b * (1 - u)) * Complex.I_sq
  have h1 : ((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u ≠ 0 := by
    have := den_ne m hz; rw [hden] at this; exact (div_ne_zero_iff.1 this).1
  have h2 : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u ≠ 0 := by
    have h := (map_ne_zero (starRingEnd ℂ)).2 h1
    convert h using 1
    simp only [map_sub, map_mul, map_add (f := _), Complex.conj_ofReal, Complex.conj_I]; ring
  have hA : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * u * conj u ≠ 0 := by
    intro h
    rw [mul_assoc, huu, ← Complex.ofReal_pow] at h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.zero_im] at this
    have h3 : b * (1 + r ^ 2) = 0 := by
      linear_combination this
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hb h4
    · nlinarith [sq_nonneg r]
  have hw : (m • zP).1 = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) := by
    rw [coe_smul, hzP1, hnum, hden, div_div_div_cancel_right₀ hu1]
  have hwb : conj (Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u)) =
      -Complex.I * (((a : ℂ) + b * Complex.I) + ((a : ℂ) - b * Complex.I) * conj u) /
      (((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u) := by
    simp only [map_div₀, map_sub, map_mul, map_add (f := _), Complex.conj_ofReal, Complex.conj_I]; ring
  have hwim : 0 < (m • zP).1.im := by
    rw [coe_smul, im_div, det_eq, h00, h01, h10, h11]
    apply div_pos (mul_pos (by nlinarith) hzpos') (Complex.normSq_pos.2 (den_ne m hz))
  have hdet : |m.val.det| = s ^ 2 := by
    rw [det_eq, h00, h01, h10, h11, hs2, abs_of_pos (by nlinarith)]; ring
  have hrp : (|m.val.det| ^ (-(k : ℝ) / 2) : ℝ) = (s ^ k)⁻¹ := by
    rw [hdet, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by push_cast; ring, Real.rpow_neg hs.le, Real.rpow_natCast]
  have hηsq : (((a : ℂ) - b * Complex.I) / (s : ℂ)) ^ 2 = ((a : ℂ) - b * Complex.I) / ((a : ℂ) + b * Complex.I) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hS0) hα0, ← Complex.ofReal_pow, hs2]
    push_cast
    linear_combination (-((a : ℂ) - b * Complex.I) * (b : ℂ) ^ 2) * Complex.I_sq
  rw [hext]
  unfold F q1 j1
  rw [if_pos (mul_pos hzpos' hwim), hrp]
  push_cast
  refine pow_combine _ _ _ _ _ k ?_
  rw [hw, hwb, hzP1, hden, key_id _ _ _ _ hα0 hu1 h1 h2 hA, ← huu, eta, ← hs_def, hηsq]
  field_simp

end UpperTheory.Esk.RadialIntegralLemmas
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem den_mul (g h : GL (Fin 2) ℝ) (z : P) : den (g * h) z.1 = den g (h • z).1 * den h z.1 := by
  have h0 := den_ne h z.2
  rw [coe_smul]
  conv_rhs => rw [den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
  simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem p1 (k : ℕ) (g h : GL (Fin 2) ℝ) (z : P) : j1 k (g * h) z = j1 k g (h • z) * j1 k h z := by
  simp only [j1, den_mul, mul_pow, Units.val_mul, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), Complex.ofReal_mul]
  ring

theorem p2 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : j1 k g z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (den_ne g z.2))
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')

theorem im_smul (g : GL (Fin 2) ℝ) (z : P) :
    (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
  rw [coe_smul, im_div]

theorem sub_conj (g : GL (Fin 2) ℝ) (z w : P) :
    (g • z).1 - conj (g • w).1 = (g.val.det : ℂ) * (z.1 - conj w.1) / (den g z.1 * conj (den g w.1)) := by
  rw [coe_smul, coe_smul, map_div₀, div_sub_div _ _ (den_ne g z.2) ((map_ne_zero _).2 (den_ne g w.2))]
  congr 1
  simp only [num, den, map_add (f := _), map_mul, Complex.conj_ofReal, det_eq]
  push_cast
  ring

theorem sign (g : GL (Fin 2) ℝ) (z w : P) : 0 < (g • z).1.im * (g • w).1.im ↔ 0 < z.1.im * w.1.im := by
  rw [im_smul, im_smul]
  have hd : g.val.det ≠ 0 := g.det_ne_zero
  have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
  have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
  have hc : 0 < g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd))) (mul_pos nz nw)
  rw [show g.val.det * z.1.im / Complex.normSq (den g z.1) * (g.val.det * w.1.im / Complex.normSq (den g w.1))
      = g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) * (z.1.im * w.1.im) by
    field_simp]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

theorem ratio (g : GL (Fin 2) ℝ) (z w : P) (h : 0 < z.1.im * w.1.im) :
    ((g • w).1 - conj (g • w).1) / ((g • z).1 - conj (g • w).1)
      = (w.1 - conj w.1) / (z.1 - conj w.1) * (den g z.1 / den g w.1) := by
  have hd : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 g.det_ne_zero
  have h1 := den_ne g z.2
  have h2 := den_ne g w.2
  have h3 : conj (den g w.1) ≠ 0 := (map_ne_zero _).2 h2
  have h4 : z.1 - conj w.1 ≠ 0 := b_ne _ _ h
  have h5 : w.1 - conj w.1 ≠ 0 := b_ne _ _ (mul_self_pos.2 w.2)
  rw [sub_conj, sub_conj]
  field_simp

theorem p3 (k : ℕ) (g : GL (Fin 2) ℝ) (z w : P) :
    q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w := by
  unfold q1
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · rw [ratio g z w h, mul_pow, div_pow (den g z.1)]
    have h2 := pow_ne_zero k (den_ne g w.2)
    simp only [j1]
    field_simp
  · simp

theorem p4 (g : GL (Fin 2) ℝ) (z w : P) : kap (g • z) (g • w) = kap z w := by
  unfold kap
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · have hd : g.val.det ≠ 0 := g.det_ne_zero
    have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
    have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
    have h4 : ‖z.1 - conj w.1‖ ≠ 0 := norm_ne_zero_iff.2 (b_ne _ _ h)
    rw [im_smul, im_smul, sub_conj, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, div_pow, mul_pow, mul_pow, sq_abs]
    simp only [Complex.sq_norm]
    field_simp
  · rfl

end UpperTheory.Esk.AutomorphyFactorLemmas

namespace UpperTheory.Esk

open AutomorphyFactorLemmas in
theorem automorphy_factor_kernel_algebra_proof : B1b :=
  ⟨p1, p2, p3, p4, p5, fun k z w hk => p6 k z w hk, p7, p8, p9⟩

end UpperTheory.Esk
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.MultivariableReproducingLemmas

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem nrm_pos {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem norm_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => hb.2.2.2.2.2.1 (k v) (z v) (w v) (hk v)

theorem cont_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (z : X I) : Continuous (qq k z) := by
  unfold qq
  exact continuous_finsetProd _ fun v _ =>
    (hb.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))

theorem integrable {I : Type} [Fintype I] (hb : B1b) (hK : KapInt) (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C)
    (z : X I) : Integrable (fun w => qq k z w * f w) := by
  obtain ⟨C1, A, h⟩ := hK I k hk
  obtain ⟨hm, hl, -⟩ := h z
  have hKi : Integrable (Kap k z) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ w, ‖Kap k z w‖ₑ = ∫⁻ w, ENNReal.ofReal (Kap k z w) := by
          congr 1; funext w; exact Real.enorm_eq_ofReal (Kap_nonneg k z w)
      _ ≤ C1 := hl
      _ < ⊤ := ENNReal.coe_lt_top
  have hc : 0 ≤ ∏ v, (((k v : ℝ) - 1) / (4 * Real.pi)) := Finset.prod_nonneg fun v _ => by
    have h4 : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    exact div_nonneg (by linarith) (by positivity)
  refine (hKi.const_mul ((∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C / nrm k z)).mono'
    ((cont_qq hb k z).mul hf).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have h1 := norm_qq hb k (fun v => le_trans (by norm_num) (hk v)) z w
  have hn := nrm_pos k z
  rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ hn]
  calc ‖qq k z w‖ * ‖f w‖ * nrm k z = (‖qq k z w‖ * nrm k z) * ‖f w‖ := by ring
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * (‖f w‖ * nrm k w) := by rw [h1]; ring
    _ ≤ (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * C :=
        mul_le_mul_of_nonneg_left (hC w) (mul_nonneg hc (Kap_nonneg k z w))
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C * Kap k z w := by ring

theorem symm_eq (n : ℕ) (p : P × (Fin n → P)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 := by
  funext j
  induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem qq_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (z : X (Fin (n + 1))) (t : P) (w : Fin n → P) :
    qq k z (Fin.cons t w) = q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w := by
  simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem nrm_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (t : P) (w : Fin n → P) :
    nrm k (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k 0 : ℝ) / 2) * nrm (fun j => k j.succ) w := by
  simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem fin_case (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) : ∀ (n : ℕ) (k : Fin n → ℕ), (∀ v, 4 ≤ k v) →
    ∀ f : X (Fin n) → ℂ, SepHol f → ∀ C, (∀ z, ‖f z‖ * nrm k z ≤ C) → ∀ z, ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  intro n
  induction n with
  | zero =>
    intro k hk f hf C hC z
    have hF : (fun w => qq k z w * f w) = fun _ => f z := funext fun w => by
      rw [Subsingleton.elim w z]; simp [qq]
    rw [hF, show (volume : Measure (X (Fin 0))) = Measure.dirac z from Measure.pi_of_empty _ z,
      integral_const]
    simp
  | succ n ih =>
    intro k hk f hf C hC z
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
    have hI := integrable hb hK k hk f hf.1 C hC z
    have hG : Integrable (fun p : P × (Fin n → P) =>
        q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 * f (Fin.cons p.1 p.2))
        ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
      have := (hmp.symm.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2 hI
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply, symm_eq, qq_cons]
    have hin : ∀ w : Fin n → P, ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
        f (Fin.cons t w) = qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
      intro w
      have hol : Hol1 fun t => f (Fin.cons t w) := by
        have h := hf.2 (Fin.cons (z 0) w) 0
        convert h using 3 with t
        funext j
        induction j using Fin.cases <;> simp
      have hbd : ∃ C', ∀ t : P, ‖f (Fin.cons t w)‖ * |t.1.im| ^ ((k 0 : ℝ) / 2) ≤ C' := by
        refine ⟨C / nrm (fun j => k j.succ) w, fun t => ?_⟩
        rw [le_div_iff₀ (nrm_pos _ _), mul_assoc, ← nrm_cons]
        exact hC _
      have h := (h3 (k 0) (hk 0) (fun t => f (Fin.cons t w)) hol hbd (z 0)).2
      calc ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons t w)
          = ∫ t, qq (fun j => k j.succ) (fun j => z j.succ) w * (q1 (k 0) (z 0) t * f (Fin.cons t w)) := by
            congr 1; funext t; ring
        _ = _ := by rw [integral_const_mul, h]
    have hsep : SepHol fun w : X (Fin n) => f (Fin.cons (z 0) w) := by
      refine ⟨hf.1.comp (continuous_pi fun j => ?_), fun w v => ?_⟩
      · induction j using Fin.cases
        · simpa using continuous_const
        · simpa using continuous_apply _
      · have h := hf.2 (Fin.cons (z 0) w) v.succ
        convert h using 3 with t
        funext j
        induction j using Fin.cases with
        | zero => simp [(Fin.succ_ne_zero v).symm]
        | succ j =>
          simp only [Fin.cons_succ, Function.update_apply, Fin.succ_inj]
          split_ifs <;> simp_all
    have hbd : ∀ w : X (Fin n), ‖f (Fin.cons (z 0) w)‖ * nrm (fun j => k j.succ) w ≤
        C / |(z 0).1.im| ^ ((k 0 : ℝ) / 2) := by
      intro w
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (z 0).2) _), mul_assoc, mul_comm (nrm _ _), ← nrm_cons]
      exact hC _
    calc ∫ w, qq k z w * f w
        = ∫ p, (fun w => qq k z w * f w)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p)
            ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
          (hmp.symm.integral_comp' _).symm
      _ = ∫ p : P × (Fin n → P), q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 *
            f (Fin.cons p.1 p.2) ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
          congr 1; funext p; simp only [symm_eq, qq_cons]
      _ = ∫ w : Fin n → P, (∫ t : P, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
            f (Fin.cons t w)) ∂(Measure.pi fun _ : Fin n => (volume : Measure P)) := integral_prod_symm _ hG
      _ = ∫ w : X (Fin n), qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
          congr 1; funext w; exact hin w
      _ = f (Fin.cons (z 0) (fun j => z j.succ)) := ih _ (fun v => hk _) _ hsep _ hbd _
      _ = f z := congrArg f (Fin.cons_self_tail z)

theorem main (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) (I : Type) [Fintype I] (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : SepHol f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C) (z : X I) :
    ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ : ∀ (w : X I) j, φ w j = w (σ.symm j) := by
    intro w j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [MeasurableEquiv.coe_piCongrLeft]
    exact this
  have hmp : MeasurePreserving φ (volume : Measure (X I)) (volume : Measure (X (Fin (Fintype.card I)))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) := by
    refine ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => ?_⟩
    have h := hf.2 (fun i => w' (σ i)) (σ.symm j)
    convert h using 3 with t
    funext i
    have heq : σ i = j ↔ i = σ.symm j := by
      constructor
      · intro h; exact σ.injective (by simpa using h)
      · intro h; simpa [h]
    simp only [Function.update_apply]
    rw [heq]
  have hnrm : ∀ w' : X (Fin (Fintype.card I)), nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) := by
    intro w'
    exact Fintype.prod_equiv σ.symm _ _ fun j => by simp
  have hbd : ∀ w' : X (Fin (Fintype.card I)), ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    intro w'; rw [hnrm]; exact hC _
  have hqq : ∀ w : X I, qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w := by
    intro w
    simp only [qq, hφ]
    exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' *
          f fun i => w' (σ i)) (φ w) := by
        congr 1; funext w; simp only [hqq, hφ, Equiv.symm_apply_apply]
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : X (Fin (Fintype.card I)) =>
          qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f fun i => z (σ.symm (σ i)) := fin_case ha hb h3 hK _ _ (fun v => hk _) _ hsep C hbd _
    _ = f z := by simp only [Equiv.symm_apply_apply]

end UpperTheory.Esk.MultivariableReproducingLemmas

open UpperTheory.Esk.MultivariableReproducingLemmas in
theorem UpperTheory.Esk.multivariable_reproducing_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B3 → UpperTheory.Esk.KapInt → UpperTheory.Esk.MultivariableReproducingFormula := by
  intro ha hb h3 hK I _ k hk f hf hC z
  obtain ⟨C, hC⟩ := hC
  exact ⟨integrable hb hK k hk f hf.1 C hC z, main ha hb h3 hK I k hk f hf C hC z⟩
end
end

section

open scoped ENNReal NNReal

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_trace_bound_proof : UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases hγ : y ∈ D.LamF T γ
        · have hnf : γ ∈ {γ : PG F | ¬ Fix s γ} := fun hf => absurd (hγ s hs hf) (not_le.2 hsT)
          rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hnf]
        · rw [Set.indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (le_of_lt (hT.trans hsT))
end
