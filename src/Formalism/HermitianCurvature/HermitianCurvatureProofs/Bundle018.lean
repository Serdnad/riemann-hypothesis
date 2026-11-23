module

public import Formalism.HermitianCurvature.Bundle003
public import Lemmata.HermitianSesquilinear.ConjEqOfNonnegReal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle009
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle014
public import Formalism.HermitianCurvature.StatementFr
public import Mathlib.Analysis.Complex.Exponential
public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle012
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.GramProductIdentities

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

end Rep

section CS

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem cs_of_pos (Ξ : F7.Sesq M) (h : ∀ m, 0 ≤ (Ξ m m).re ∧ (Ξ m m).im = 0) (x y : M) :
    ‖Ξ x y‖ ^ 2 ≤ (Ξ x x).re * (Ξ y y).re := by
  first | exact Bl.HermitianSesquilinear.goal1 .. | (apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> first | assumption | infer_instance) | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x y | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› | exact @Bl.HermitianSesquilinear.goal1 M ‹_› | exact @Bl.HermitianSesquilinear.goal1 M

end CS

theorem exp_le_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.exp (-2 * |x|) ≤ 1 + x := by
  rcases le_or_gt 0 x with h0 | h0
  · have : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
    linarith
  · have hu : |x| = -x := abs_of_neg h0
    set u := -x with hu'
    have hu0 : 0 ≤ u := by linarith
    have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    have h2 : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (-2 * u) * (1 + 2 * u) ≤ 1 := by
      calc Real.exp (-2 * u) * (1 + 2 * u) ≤ Real.exp (-2 * u) * Real.exp (2 * u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    rw [hu]
    nlinarith [mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 1 - 2 * u)]

theorem prod_bounds {ι : Type} (g : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2) :
    ∀ w : List ι, (∀ l ∈ w, |g l - 1| ≤ ε) →
      Real.exp (-2 * ε * w.length) ≤ (w.map g).prod ∧ (w.map g).prod ≤ Real.exp (ε * w.length) := by
  intro w
  induction w with
  | nil => intro _; simp
  | cons l w ih =>
    intro hw
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hw l' (by simp [hl'])
    have hl := hw l (by simp)
    have hx : |g l - 1| ≤ 1 / 2 := le_trans hl hε
    have hlo : Real.exp (-2 * ε) ≤ g l := by
      have := exp_le_one_add hx
      have : Real.exp (-2 * ε) ≤ Real.exp (-2 * |g l - 1|) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hhi : g l ≤ Real.exp ε := by
      have := Real.add_one_le_exp (g l - 1)
      have : Real.exp (g l - 1) ≤ Real.exp ε := Real.exp_le_exp.mpr (le_trans (le_abs_self _) hl)
      linarith
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have e1 : Real.exp (-2 * ε * (w.length + 1)) = Real.exp (-2 * ε) * Real.exp (-2 * ε * w.length) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (ε * (w.length + 1)) = Real.exp ε * Real.exp (ε * w.length) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    constructor
    · exact mul_le_mul hlo ih1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hlo)
    · exact mul_le_mul hhi ih2 (le_trans (Real.exp_pos _).le ih1) (Real.exp_pos _).le

theorem qProduct : QProduct := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil => simp [qw, hq]
  | cons l w ih =>
    have hl := hw l (by simp)
    have ih' := ih fun l' hl' => hw l' (by simp [hl'])
    simp only [qw, List.map_cons, List.prod_cons]
    rw [← ih']
    cases hp : l.plus
    · simp only [hp] at hl ⊢
      simp only [Bool.false_eq_true, if_false]
      have h2 : l.pt - Y - 1 ≠ 0 := hl
      field_simp
      try ring
    · simp only [hp] at hl ⊢
      simp only [if_true]
      have h2 : Y - l.pt ≠ 0 := hl
      field_simp
      try ring

theorem lemmaQ : LemmaQ := by
  intro S _ _ q w N dl Y hN hw hdl hpts hq
  have hN' : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hdlpos : 0 < dl := by nlinarith
  set g : Letter ℝ S → ℝ := fun l => if l.plus then 1 + 1 / (Y - l.pt) else 1 + 1 / (l.pt - Y - 1)
    with hg
  have hfac : ∀ l ∈ w, |g l - 1| ≤ 1 / dl := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h
      simp only [hg, hp, Bool.false_eq_true, if_false, add_sub_cancel_left, abs_div, abs_one]
      have : |l.pt - Y - 1| = |Y - (l.pt - 1)| := by rw [← abs_neg]; ring_nf
      rw [this]
      exact one_div_le_one_div_of_le hdlpos h.2
    · simp only [hp, if_true] at h
      simp only [hg, hp, if_true, add_sub_cancel_left, abs_div, abs_one]
      exact one_div_le_one_div_of_le hdlpos h
  have hreg : ∀ l ∈ w, if l.plus then Y - l.pt ≠ 0 else l.pt - Y - 1 ≠ 0 := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
      intro h0
      have : |Y - (l.pt - 1)| = 0 := by rw [abs_eq_zero]; linarith
      linarith [h.2]
    · simp only [hp, if_true] at h ⊢
      intro h0
      rw [h0, abs_zero] at h
      linarith
  have hprod := qProduct S q w Y hq hreg
  have hε : 1 / dl ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  obtain ⟨hlo, hhi⟩ := prod_bounds g (1 / dl) hε w hfac
  have hlen : (w.length : ℝ) ≤ N := by exact_mod_cast hw
  have hkey : 1 / dl * w.length ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdlpos]
    nlinarith
  rw [hprod]
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) hlo
    nlinarith
  · refine le_trans hhi (Real.exp_le_exp.mpr ?_)
    linarith

theorem dkStep4 : DKStep4 := by
  intro S q w L hL
  induction L with
  | nil => simp [kapF]
  | cons l L ih =>
    have hl : l.plus = true := hL l (by simp)
    have hL' : ∀ l' ∈ L, l'.plus = true := fun l' h => hL l' (by simp [h])
    have h1 : (L.map fun l' => if l.plus = l'.plus then (1:ℂ)
        else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨l', hl', rfl⟩ := hx
      simp [hl, hL' l' hl']
    simp only [kapF, List.map_cons, List.prod_cons]
    rw [h1, ih hL']
    simp only [ypt, hl, if_true]
    ring

end Formalism.FourierDecayAlt.P.GramProductIdentities

theorem Formalism.FourierDecayAlt.P.lemma_Q_estimate : Formalism.FourierDecayAlt.FormPairingAction.LemmaQ := Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQ
end

section

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem continuousOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by
  exact (contDiffOn_bet hα).continuousOn

theorem cont_vert (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    Continuous fun θ : ℝ => bet α (x0 TT + (θ : ℂ) * I) := by
  exact (continuousOn_bet hα).comp_continuous (by fun_prop) (vert_mem hTT)

theorem im_circleIntegral (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    (circleIntegral α 0 (TT + 1)).im = ∫ θ in (0 : ℝ)..2 * Real.pi, (bet α (x0 TT + (θ : ℂ) * I)).re := by
  have hint : IntervalIntegrable (fun θ : ℝ => I * bet α (x0 TT + (θ : ℂ) * I)) MeasureTheory.volume
      0 (2 * Real.pi) :=
    (continuous_const.mul (cont_vert hTT hα)).intervalIntegrable _ _
  rw [circleIntegral_eq hTT, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext θ
  simp [Complex.mul_im]

theorem th_top (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    th TT α (x0 TT + 2 * Real.pi * I) = 2 * (circleIntegral α 0 (TT + 1)).im := by
  rw [im_circleIntegral hTT hα]
  have hw : x0 TT + 2 * Real.pi * I - x0 TT = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
  have harg : ∀ t : ℝ, x0 TT + (t : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * I) =
      x0 TT + ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    intro t; push_cast; ring
  have him : ∀ z : ℂ, (z * (((2 * Real.pi : ℝ) : ℂ) * I)).im = 2 * Real.pi * z.re := by
    intro z
    simp [Complex.mul_im, Complex.mul_re]
    ring
  simp only [th, prim, hw, om_apply, harg, him]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (f := fun θ : ℝ => (bet α (x0 TT + (θ : ℂ) * I)).re)
      (by positivity : (2 * Real.pi) ≠ 0)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have hpi : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc (2 * Real.pi), hpi, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

section real

theorem pratio (s : Finset ℕ) (lam : ℕ → ℝ) (α β y : ℝ) (hI : 3 ≤ β - α)
    (hroot : ∀ t ∈ s, -lam t < α ∨ β < -lam t) (hy1 : α + (β - α) / 3 ≤ y) (hy2 : y + 1 ≤ β - (β - α) / 3) :
    |∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) fun t ht => ?_
  have hI0 : 0 < β - α := by linarith
  have h3 : 0 ≤ 3 / (β - α) := by positivity
  rcases hroot t ht with h | h
  · have a1 : 0 < y + lam t := by linarith
    rw [abs_of_pos a1, abs_of_pos (by linarith : 0 < y + 1 + lam t)]
    nlinarith
  · have a2 : y + 1 + lam t < 0 := by linarith
    rw [abs_of_neg (by linarith : y + lam t < 0), abs_of_neg a2]
    have : 1 ≤ 3 / (β - α) * -(y + 1 + lam t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI0]; linarith
    nlinarith

theorem long_bound (k r N Cc I : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hN : 20 ≤ N) (hCc : 1 ≤ Cc)
    (h : Cc * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ I) : 6 * (k + 2 * r + 1) ≤ I := by
  have hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 := by positivity
  have h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I := by nlinarith
  have h2 : 6 * k ≤ k * N * (r + 1) ^ 2 := by
    have : 20 ≤ N * (r + 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2 := by
    have : 400 ≤ N ^ 2 := by nlinarith
    nlinarith
  have h4 : 0 ≤ N ^ 3 := by positivity
  linarith

theorem three_le_len (N I : ℝ) (hN : 20 ≤ N) (h : 6 * N ^ 3 + 6 * N ≤ I) : 3 ≤ I := by
  have : 0 ≤ 6 * N ^ 3 := by positivity
  linarith

theorem two_N_bound (N : ℝ) (hN : 20 ≤ N) : 0 < N ^ 2 - 1 ∧ ((2 : ℕ) : ℝ) * (N / (N ^ 2 - 1)) ≤ 1 / 2 := by
  have hpos : 0 < N ^ 2 - 1 := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem final_cmp (Pa x0 F q TT sA E1 qw : ℝ) (hPa : 0 ≤ Pa) (hx0 : 0 < x0) (hF0 : 0 < F) (hq : 0 < q) (hTT : 0 < TT)
    (hsA : 0 ≤ sA) (hE1 : 0 < E1) (hE1sq : E1 ^ 2 = Real.exp 1) (hP2 : Pa ^ 2 ≤ E1 * (sA ^ 2 * q))
    (hx : x0 ^ 2 ≤ q / TT) (hF : F ^ 2 ≤ E1) (hqw : E1⁻¹ * q ≤ qw) :
    Pa ≤ Real.exp 1 * sA * (√TT)⁻¹ * (qw / (x0 * F)) := by
  have hsq : (√TT)⁻¹ ^ 2 = TT⁻¹ := by rw [inv_pow, Real.sq_sqrt hTT.le]
  have hsq0 : 0 < (√TT)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hTT)
  have hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q := by
    have hl0 : 0 ≤ Pa * (x0 * F) := mul_nonneg hPa (mul_pos hx0 hF0).le
    have hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q := mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le
    rw [← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]
    have eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2 := by ring
    have eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp
    rw [eL, eR]
    calc Pa ^ 2 * x0 ^ 2 * F ^ 2 ≤ E1 * (sA ^ 2 * q) * x0 ^ 2 * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * E1 := by gcongr
  have hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q := by
    rw [← hE1sq]; field_simp
  have hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw := by
    rw [← hC] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)
    positivity
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]
  exact hfin

theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

end real

section xs

theorem xs_eq_prod {S : Type} [Fintype S] [DecidableEq S] (x0 : ℂ → ℂ) :
    ∀ (L : List (Wd.Letter ℂ S)) (e : Wd.Ix S) (Y : ℂ),
      Fr.xs x0 L e Y = x0 Y * (L.map fun l => if e l.intersection_update_fsHerm_neg_one = 0 then Fr.phiL l Y else 1).prod
  | [], _, _ => by simp [Fr.xs]
  | l :: L, e, Y => by
    simp only [Fr.xs, List.map_cons, List.prod_cons]
    rw [xs_eq_prod x0 L e Y]
    ring

theorem phiL_bound (b : Bool) (pt y D : ℝ) (hD : 2 ≤ D) (hd : D + 2 ≤ |y - pt|) :
    0 < (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ∧
      (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ≤ 1 + 1 / D := by
  have hD0 : 0 < D := by linarith
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : pt - y - 2 < 0 := by linarith
      have h2 : pt - y - 1 < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h1
      · rw [div_le_iff_of_neg h1]
        have : 0 < 1 / D := by positivity
        nlinarith
    · rw [abs_of_neg h] at hd
      have h1 : 0 < pt - y - 2 := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D := by ring
        rw [e1]
        have : 1 ≤ (pt - y - 2) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
  · simp only [if_true]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : 0 < y - pt := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D := by ring
        rw [e1]
        have : 1 ≤ (y - pt) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
    · rw [abs_of_neg h] at hd
      have h2 : y + 1 - pt < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h
      · rw [div_le_iff_of_neg h]
        have : 0 < 1 / D := by positivity
        nlinarith

end xs

end

end Formalism.FourierDecayAlt.P.PBL
end

section

namespace Formalism.FourierDecayAlt.P

theorem le_thetaRange_proof : Formalism.FourierDecayAlt.LE.ThetaRange := by
  intro ε σ x hε hσ hx
  simp only [LE.th]
  have hb : 0 < x / (x + ε) := by positivity
  exact ⟨Real.rpow_pos_of_pos hb σ, Real.rpow_le_one hb.le ((div_le_one (by linarith)).mpr (by linarith)) hσ⟩

theorem le_thetaSmooth_proof : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.LEx1.thetaSmooth

theorem cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.LEx1.cutBound

theorem cutoff_theta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.LEx1.cutTheta

end Formalism.FourierDecayAlt.P
end
