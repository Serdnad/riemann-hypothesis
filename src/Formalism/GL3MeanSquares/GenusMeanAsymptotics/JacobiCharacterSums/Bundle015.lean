module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle002
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle006
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LFunctionBounds.ExpSumLowerBound
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle002

@[expose] public section

section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exr_abs_le {a p q : ℝ} (h1 : p ≤ a) (h2 : a ≤ q) : |a| ≤ |p| + |q| :=
  abs_le.2 ⟨by linarith [neg_abs_le p, abs_nonneg q], by linarith [le_abs_self q, abs_nonneg p]⟩

theorem ex_rect_logDeriv (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) (y : ℝ) (hy : 0 < y)
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁)
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (f ρ = 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁))
    (hedge : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → f w = 0 →
      x₀ < w.re ∧ w.re < x₁ ∧ y₀ < w.im ∧ w.im < y₁) :
    Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (-(deriv f 1 / f 1) * y - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ) := by
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = |x₀ - 1| + |x₁ - 1| + |y₀| + |y₁| + 1 := ⟨_, rfl⟩
  have hR₁ : 0 < R₁ := by rw [hR₁def]; positivity
  obtain ⟨Zb, m, h, hZb, hm, hh, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f 1 (R₁ + 1) R₁ hR₁ (by linarith) hf.differentiableOn hf1
  have hrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w a1 a2 a3 a4
    rw [Metric.mem_ball, dist_eq_norm]
    have e1 := Complex.norm_le_abs_re_add_abs_im (w - 1)
    have e2 : |(w - 1).re| ≤ |x₀ - 1| + |x₁ - 1| := by
      rw [sub_re, one_re]; exact exr_abs_le (by linarith) (by linarith)
    have e3 : |(w - 1).im| ≤ |y₀| + |y₁| := by
      rw [sub_im, one_im, sub_zero]; exact exr_abs_le a3 a4
    linarith
  have hball : Metric.ball (1 : ℂ) R₁ ⊆ Metric.closedBall 1 R₁ := Metric.ball_subset_closedBall
  have hSsub : Metric.ball (1 : ℂ) (R₁ + 1) ⊆ Metric.closedBall 1 (R₁ + 1) := Metric.ball_subset_closedBall
  have hR1S : Metric.ball (1 : ℂ) R₁ ⊆ Metric.ball 1 (R₁ + 1) := Metric.ball_subset_ball (by linarith)
  have hhS : DifferentiableOn ℂ h (Metric.ball 1 (R₁ + 1)) := hh.mono hSsub
  have hfacS : ∀ z ∈ Metric.ball (1 : ℂ) (R₁ + 1), f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    fun z hz => hfac z (hSsub hz)
  have hZin : ∀ ρ ∈ Z, ρ ∈ Metric.ball (1 : ℂ) R₁ := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hrect ρ a1.le a2.le a3.le a4.le
  have hZsub : Z ⊆ Zb := by
    intro ρ hρ
    exact (hZb ρ).2 ⟨hball (hZin ρ hρ), ((hZ ρ).1 hρ).1⟩
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := fun ρ hρ =>
    exr_ord f h Zb m _ Metric.isOpen_ball hhS hfacS ρ (hZsub hρ) (hR1S (hZin ρ hρ))
      (hh0 ρ (hball (hZin ρ hρ)))
  have h1Z : (1 : ℂ) ∉ Z := fun h => hf1 ((hZ 1).1 h).1
  have hZne0 : ∀ ρ ∈ Z, ρ ≠ 0 := by
    intro ρ hρ h0; have := ((hZ ρ).1 hρ).2.1; rw [h0, zero_re] at this; linarith
  have hZne1 : ∀ ρ ∈ Z, ρ ≠ 1 := fun ρ hρ h1 => h1Z (h1 ▸ hρ)

  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = Metric.ball (1 : ℂ) R₁ \ (((Zb \ Z : Finset ℂ) : Set ℂ) ∪ {0}) :=
    ⟨_, rfl⟩
  have hU : IsOpen U := by
    rw [hUdef]
    exact Metric.isOpen_ball.sdiff ((Finset.finite_toSet _).union (Set.finite_singleton 0)).isClosed
  have hUrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ U := by
    intro w a1 a2 a3 a4
    rw [hUdef]
    refine ⟨hrect w a1 a2 a3 a4, ?_⟩
    rintro (hw | hw)
    · rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.mem_coe] at hw
      have hfw : f w = 0 := ((hZb w).1 hw.1).2
      obtain ⟨b1, b2, b3, b4⟩ := hedge w a1 a2 a3 a4 hfw
      exact hw.2 ((hZ w).2 ⟨hfw, b1, b2, b3, b4⟩)
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, zero_re] at a1; linarith
  have hUball : ∀ w ∈ U, w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w hw; rw [hUdef] at hw; exact hw.1
  have hUne0 : ∀ w ∈ U, w ≠ 0 := by
    intro w hw h0; rw [hUdef] at hw; exact hw.2 (Or.inr h0)
  have hUZb : ∀ w ∈ U, w ∉ Z → w ∉ Zb := by
    intro w hw hwZ hwZb; rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff]; exact ⟨hwZb, hwZ⟩))
  have h1U : (1 : ℂ) ∈ U := hUrect 1 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hZU : ∀ ρ ∈ Z, ρ ∈ U := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hUrect ρ a1.le a2.le a3.le a4.le

  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ, φ = fun w => (y : ℂ) ^ w / w := ⟨_, rfl⟩
  obtain ⟨Lf, hLdef⟩ : ∃ Lf : ℂ → ℂ,
      Lf = fun w => deriv h w / h w + ∑ ρ ∈ Zb \ Z, (m ρ : ℂ) / (w - ρ) := ⟨_, rfl⟩
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hφU : DifferentiableOn ℂ φ U := by
    intro w hw
    rw [hφdef]
    exact ((differentiableAt_id.const_cpow (Or.inl hy0)).div differentiableAt_id
      (hUne0 w hw)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ Lf U := by
    intro w hw
    have hwb := hR1S (hUball w hw)
    have hN : Metric.ball (1 : ℂ) (R₁ + 1) ∈ nhds w := Metric.isOpen_ball.mem_nhds hwb
    have hd1 : DifferentiableAt ℂ (deriv h) w :=
      ((hhS.deriv Metric.isOpen_ball) w hwb).differentiableAt hN
    have hd2 : DifferentiableAt ℂ h w := (hhS w hwb).differentiableAt hN
    have hhw : h w ≠ 0 := hh0 w (hball (hUball w hw))
    rw [hLdef]
    refine (DifferentiableAt.add (hd1.div hd2 hhw) ?_).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun ρ hρ => ?_
    refine (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) ?_
    rw [Finset.mem_sdiff] at hρ
    intro h0; rw [sub_eq_zero] at h0
    rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff, h0]; exact ⟨hρ.1, hρ.2⟩))
  have hLD : ∀ w ∈ U, w ∉ Z → deriv f w / f w = (∑ ρ ∈ Z, (m ρ : ℂ) / (w - ρ)) + Lf w := by
    intro w hw hwZ
    rw [exr_logDeriv f h Zb m _ Metric.isOpen_ball hhS hfacS w (hR1S (hUball w hw)) (hUZb w hw hwZ)
      (hh0 w (hball (hUball w hw))), hLdef, ← Finset.sum_sdiff hZsub]
    ring
  have hk : ∀ w, exKer y w = φ w / (w - 1) := fun w => by rw [hφdef, exKer, div_div]
  have hb1 : ∃ b : ℂ → ℂ, b 1 = -(deriv f 1 / f 1) * y ∧ ∀ ρ ∈ Z, b ρ = -(m ρ : ℂ) * exKer y ρ :=
    ⟨fun p => if p = 1 then -(deriv f 1 / f 1) * y else -(m p : ℂ) * exKer y p, by simp,
      fun ρ hρ => by simp [hZne1 ρ hρ]⟩
  obtain ⟨b, hb1, hbρ⟩ := hb1
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀ : ℂ → ℂ, G₀ = fun w => -dslope (fun z => Lf z * φ z) 1 w -
      ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := ⟨_, rfl⟩
  have hG₀U : DifferentiableOn ℂ G₀ U := by
    rw [hG₀def]
    refine DifferentiableOn.sub ((differentiableOn_dslope (hU.mem_nhds h1U)).2 (hLU.mul hφU)).neg ?_
    refine DifferentiableOn.fun_sum fun ρ hρ => ?_
    exact (differentiableOn_const _).mul (((differentiableOn_dslope (hU.mem_nhds (hZU ρ hρ))).2 hφU).sub
      ((differentiableOn_dslope (hU.mem_nhds h1U)).2 hφU))
  have hφw : ∀ z, φ z = (y : ℂ) ^ z / z := fun z => by rw [hφdef]
  have hφ1 : φ 1 = y := by rw [hφw]; simp
  have hkey : ∀ w ∈ U, w ∉ insert 1 Z →
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) = G₀ w := by
    intro w hw hwP
    rw [Finset.mem_insert, not_or] at hwP
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hwP.1
    have hw0 := hUne0 w hw
    have hwρ : ∀ ρ ∈ Z, w - ρ ≠ 0 := fun ρ hρ h0 => hwP.2 (sub_eq_zero.1 h0 ▸ hρ)
    have hC : ∑ ρ ∈ Z, b ρ / (w - ρ) = ∑ ρ ∈ Z, -(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1))) / (w - ρ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, exKer]
    have hD : ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) =
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1)) :=
      Finset.sum_congr rfl fun ρ hρ => by
        rw [dslope_of_ne _ (sub_ne_zero.1 (hwρ ρ hρ)), dslope_of_ne _ hwP.1, slope_def_field,
          slope_def_field, hφ1, hφw, hφw]
    have hrel : ∑ ρ ∈ Z, (-((m ρ : ℂ) / (w - ρ)) * ((y : ℂ) ^ w / w / (w - 1)) +
        (m ρ : ℂ) / (1 - ρ) * y / (w - 1) - (-(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1)))) / (w - ρ) +
        (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1))) = 0 :=
      Finset.sum_eq_zero fun ρ hρ => exr_term _ _ _ _ _ _ hw0 hw1 (hwρ ρ hρ) (hZne0 ρ hρ)
        (sub_ne_zero.2 (hZne1 ρ hρ))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hrel
    have hG₀w : G₀ w = -dslope (fun z => Lf z * φ z) 1 w -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := by rw [hG₀def]
    rw [hG₀w, hD, Finset.sum_insert h1Z, hC, hb1, dslope_of_ne _ hwP.1, slope_def_field, hLD w hw hwP.2,
      hLD 1 h1U h1Z, hk w, hφ1, hφw w]
    linear_combination hrel
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun w => if w ∈ insert 1 Z then G₀ w else
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) := ⟨_, rfl⟩
  have hGU : DifferentiableOn ℂ G U := by
    refine hG₀U.congr fun w hw => ?_
    rw [hGdef]
    by_cases hwP : w ∈ insert 1 Z
    · simp only [if_pos hwP]
    · simp only [if_neg hwP]; exact hkey w hw hwP
  have hPin : ∀ p ∈ insert 1 Z, x₀ < p.re ∧ p.re < x₁ ∧ y₀ < p.im ∧ p.im < y₁ := by
    intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with hp | hp
    · subst hp; simp; exact ⟨hx₀1, hx₁, hy₀, hy₁⟩
    · exact ((hZ p).1 hp).2
  have hsub : (Set.uIcc x₀ x₁ ×ℂ Set.uIcc y₀ y₁) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    exact hUrect w hw.1.1 hw.1.2 hw.2.1 hw.2.2
  have hres := Formalism.FX.rectangle_residue (fun w => -(deriv f w / f w) * exKer y w) G (insert 1 Z) b
    x₀ x₁ y₀ y₁ (by linarith) (by linarith) hPin ⟨U, hU, hsub, hGU⟩ (fun w hw => by
      rw [hGdef]; simp only [if_neg hw]; ring)
  have hsum : ∑ ρ ∈ Z, b ρ = -∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, hord ρ hρ, neg_mul]
  rw [show Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
    Formalism.FX.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ from rfl, hres,
    Finset.sum_insert h1Z, hb1, hsum]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma sharp_split (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have hd : Disjoint (Icc 1 a) (Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
    omega
  have hu : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  rw [hu, Finset.sum_union hd]

lemma sharp_schi_div {N : ℕ} (χ : DirichletCharacter ℂ N) {v : ℝ} (hv : 0 < v) :
    Formalism.ZeroFreeDirichlet.Schi χ v / (v : ℂ) =
      ∑ n ∈ Icc 1 ⌊v⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / v : ℝ) : ℂ) := by
  rw [Formalism.ZeroFreeDirichlet.Schi.eq_1, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hv0 : v ≠ 0 := hv.ne'
  rw [mul_div_assoc]
  congr 1
  rw [← Complex.ofReal_div]
  congr 1
  field_simp

lemma sharp_identity {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y =
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have huy : u - y ≠ 0 := (sub_pos.mpr hu).ne'
  have hfl : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
  rw [sharp_schi_div χ hu0, sharp_schi_div χ hy0, sharp_split _ hfl, Formalism.ZeroFreeDirichlet.psiChi.eq_1]
  have hc1 : y * u / (u - y) * (1 / y - 1 / u) = 1 := by
    field_simp
  have hAC : (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ)) -
      ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / y : ℝ) : ℂ) =
      ((1 / y - 1 / u : ℝ) : ℂ) * ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hE : ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) =
      ((y * u / (u - y) : ℝ) : ℂ) *
        ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hc1' : ((y * u / (u - y) : ℝ) : ℂ) * ((1 / y - 1 / u : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc1, Complex.ofReal_one]
  rw [hE]
  linear_combination ((y * u / (u - y) : ℝ) : ℂ) * hAC +
    (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) * hc1'

lemma sharp_term {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u)
    {n : ℕ} (hn : n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ ≤
      Real.log u := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hyn : y < n := (Nat.floor_lt hy0.le).mp hn1
  have hnu : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).mp hn2
  have hnpos : (0:ℝ) < n := by linarith
  have huy : 0 < u - y := by linarith
  have hf0 : 0 ≤ y * u / (u - y) * (1 / n - 1 / u) := by
    apply mul_nonneg (div_nonneg (by positivity) huy.le)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hnpos hnu
  have hf1 : y * u / (u - y) * (1 / n - 1 / u) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one huy]
    have h1 : y * u * (1 / n - 1 / u) = y * u / n - y := by
      rw [mul_sub, mul_one_div, mul_one_div, mul_div_cancel_right₀ y hu0.ne']
    rw [h1]
    have h2 : y * u / n ≤ u := by
      rw [div_le_iff₀ hnpos]
      nlinarith
    linarith
  have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : Λ n ≤ Real.log u :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hnu)
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hΛ0, ← abs_mul, abs_of_nonneg hf0]
  calc Λ n * ‖χ (n : ZMod N)‖ * (y * u / (u - y) * (1 / n - 1 / u)) ≤ Λ n * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hχ hΛ0) hf1 hf0 (mul_nonneg hΛ0 zero_le_one)
    _ = Λ n := by ring
    _ ≤ Real.log u := hΛ

theorem sharp_arith {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ‖((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y‖ ≤
      (u - y + 1) * Real.log u := by
  rw [sharp_identity χ hy hu]
  have hu1 : 1 ≤ u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
          ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, Real.log u := Finset.sum_le_sum (fun n hn => sharp_term χ hy hu hn)
    _ = ((⌊u⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) * Real.log u := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (u - y + 1) * Real.log u := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have h2 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
        have h3 : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
        rw [Nat.cast_sub h3]
        linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
