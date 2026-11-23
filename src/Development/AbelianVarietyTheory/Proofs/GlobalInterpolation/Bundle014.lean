module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HaarDisintegrationAveragedFibreMeasures
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  first | exact @GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | exact GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | (intros; apply GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon <;> assumption)
end

section

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.WeberProduct

def eulerProd (x : ℂ) : ℂ := ∏' n : ℕ, (1 - x ^ (n + 1))

def oddProd (x : ℂ) : ℂ := ∏' k : ℕ, (1 - x ^ (2 * k + 1))

theorem multipliable_odd {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun k : ℕ ↦ 1 - x ^ (2 * k + 1) := by
  have h2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hs : Summable fun k : ℕ ↦ ‖x‖ * (‖x‖ ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) h2).mul_left _
  have := multipliable_one_add_of_summable (f := fun k : ℕ ↦ -x ^ (2 * k + 1))
    (hs.congr fun k ↦ by simp [norm_pow, pow_succ, pow_mul]; ring)
  simpa [sub_eq_add_neg] using this

theorem multipliable_euler {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - x ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow hx

theorem eulerProd_split {y : ℂ} (hy : ‖y‖ < 1) : eulerProd y = oddProd y * eulerProd (y ^ 2) := by
  have hy2 : ‖y ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg y]
  have e1 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k)) = fun k ↦ 1 - y ^ (2 * k + 1) := rfl
  have e2 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k + 1)) =
      fun k ↦ 1 - (y ^ 2) ^ (k + 1) := by
    funext k; rw [← pow_mul]; ring_nf
  have h := tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - y ^ (n + 1))
    (by rw [e1]; exact multipliable_odd hy) (by rw [e2]; exact multipliable_euler hy2)
  rw [e1, e2] at h
  rw [eulerProd, eulerProd, oddProd, h]

theorem oddProd_neg_mul {t : ℂ} (ht : ‖t‖ < 1) : oddProd (-t) * oddProd t = oddProd (t ^ 2) := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  rw [oddProd, oddProd, oddProd, ← (multipliable_odd hn).tprod_mul (multipliable_odd ht)]
  congr 1
  funext k
  rw [Odd.neg_pow ⟨k, rfl⟩, ← pow_mul]
  ring_nf

theorem eulerProd_identity {t : ℂ} (ht : ‖t‖ < 1) :
    eulerProd (-t) * eulerProd t * eulerProd (t ^ 4) = eulerProd (t ^ 2) ^ 3 := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  have h2 : ‖t ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have a := eulerProd_split hn
  have b := eulerProd_split ht
  have c := eulerProd_split h2
  rw [neg_sq] at a
  rw [← pow_mul] at c
  norm_num at c
  have d := oddProd_neg_mul ht
  norm_num at c
  linear_combination (eulerProd t * eulerProd (t ^ 4)) * a + (oddProd (-t) * eulerProd (t ^ 2) * eulerProd (t ^ 4)) * b +
    (eulerProd (t ^ 2) ^ 2 * eulerProd (t ^ 4)) * d - eulerProd (t ^ 2) ^ 2 * c

theorem eta_eq (z : ℂ) : ModularForm.eta z = Function.Periodic.qParam 24 z * eulerProd (Function.Periodic.qParam 1 z) :=
  rfl

theorem eta_relation (τ : ℍ) :
    cexp (-(π * I / 24)) * ModularForm.eta (((τ : ℂ) + 1) / 2) * ModularForm.eta ((τ : ℂ) / 2) *
      ModularForm.eta (2 * (τ : ℂ)) = ModularForm.eta τ ^ 3 := by
  set t := cexp (π * I * (τ : ℂ)) with ht_def
  have ht : ‖t‖ < 1 := by
    rw [ht_def, Complex.norm_exp, Real.exp_lt_one_iff]
    have := τ.im_pos
    simp only [mul_re, ofReal_re, Complex.I_re, ofReal_im, Complex.I_im, mul_im, coe_re, coe_im]
    nlinarith [Real.pi_pos]
  have q1 : Function.Periodic.qParam 1 (((τ : ℂ) + 1) / 2) = -t := by
    rw [Function.Periodic.qParam, ht_def, ← mul_neg_one, ← Complex.exp_pi_mul_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  have q2 : Function.Periodic.qParam 1 ((τ : ℂ) / 2) = t := by
    rw [Function.Periodic.qParam, ht_def]; congr 1; push_cast; ring
  have q3 : Function.Periodic.qParam 1 (2 * (τ : ℂ)) = t ^ 4 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have q4 : Function.Periodic.qParam 1 (τ : ℂ) = t ^ 2 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hq : cexp (-(π * I / 24)) * Function.Periodic.qParam 24 (((τ : ℂ) + 1) / 2) *
      Function.Periodic.qParam 24 ((τ : ℂ) / 2) * Function.Periodic.qParam 24 (2 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 3 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [eta_eq, eta_eq, eta_eq, eta_eq, q1, q2, q3, q4]
  have key := eulerProd_identity ht
  linear_combination (eulerProd (-t) * eulerProd t * eulerProd (t ^ 4)) * hq +
    Function.Periodic.qParam 24 (τ : ℂ) ^ 3 * key

theorem weber_prod (τ : ℍ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ =
      ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h0 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  have key := eta_relation τ
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂]
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_iff (by simp [h0])]
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * key

end GlobalTheory.WeberProduct
end
end

section

open Complex

open Polynomial
open UpperHalfPlane hiding I

noncomputable section

namespace GlobalTheory.WeberCubicAlgebra

lemma half_root (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
  have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, h2⟩
  rw [L.derivWeierstrassP_neg] at e1
  have e2 : -t + 2 * t = t := by ring
  simp only [e2] at e1
  have e3 : L.derivWeierstrassP t = 0 := by linear_combination e1 / 2
  rw [← L.derivWeierstrassP_sq t ht, e3]
  simp

lemma roots_alg {e1 e2 e3 g h P A B D : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0)
    (d1 : e1 - e2 = P * A) (d2 : e1 - e3 = P * B) (d3 : e3 - e2 = P * D) :
    g = 2 / 3 * P ^ 2 * (A ^ 2 + B ^ 2 + D ^ 2) ∧
      g ^ 3 - 27 * h ^ 2 = 16 * P ^ 6 * (A * B * D) ^ 2 := by
  have a12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination r1 - r2)
  have a13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination r1 - r3)
  have s : e1 + e2 + e3 = 0 := by
    have : (e2 - e3) * (e1 + e2 + e3) = (e2 - e3) * 0 := by linear_combination (a12 - a13) / 4
    exact mul_left_cancel₀ (sub_ne_zero.2 h23) this
  have hh : h = 4 * e1 ^ 3 - g * e1 := by linear_combination -r1
  have k1 : (P * A) ^ 2 = (e1 - e2) ^ 2 := by rw [d1]
  have k2 : (P * B) ^ 2 = (e1 - e3) ^ 2 := by rw [d2]
  have k3 : (P * D) ^ 2 = (e3 - e2) ^ 2 := by rw [d3]
  obtain rfl : e3 = -e1 - e2 := by linear_combination s
  subst hh
  subst a12
  constructor
  · linear_combination (-2 / 3 : ℂ) * (k1 + k2 + k3)
  · have : 16 * P ^ 6 * (A * B * D) ^ 2 = 16 * ((P * A) ^ 2 * (P * B) ^ 2 * (P * D) ^ 2) := by ring
    rw [this, k1, k2, k3]
    ring

lemma coeffs (A B D j F0 F1 F2 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hs : A = B + D)
    (h0 : F0 * (B * D) = 16 * A ^ 2) (h1 : F1 * (A * D) = 16 * B ^ 2)
    (h2 : F2 * (A * B) = 16 * D ^ 2) (hj : j * (A * B * D) ^ 2 = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3) :
    F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096 := by
  have e0 : F0 = 16 * A ^ 2 / (B * D) := by rw [eq_div_iff (mul_ne_zero hB hD)]; exact h0
  have e1 : F1 = 16 * B ^ 2 / (A * D) := by rw [eq_div_iff (mul_ne_zero hA hD)]; exact h1
  have e2 : F2 = 16 * D ^ 2 / (A * B) := by rw [eq_div_iff (mul_ne_zero hA hB)]; exact h2
  have ej : j = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3 / (A * B * D) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hA hB) hD))]; exact hj
  subst e0 e1 e2 ej hs
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

lemma cubic_eq (j F0 F1 F2 : ℂ)
    (h : F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096) :
    ((X - C 16) ^ 3 - C j * X : ℂ[X]) = (X - C F0) * (X - C (-F1)) * (X - C (-F2)) := by
  obtain ⟨s1, s2, s3⟩ := h
  have e : ((X - C F0) * (X - C (-F1)) * (X - C (-F2)) : ℂ[X]) =
      X ^ 3 - C (F0 - F1 - F2) * X ^ 2 + C (-(F0 * F1) - F0 * F2 + F1 * F2) * X - C (F0 * F1 * F2) := by
    simp only [map_sub, map_neg, map_mul, map_add (f := _)]
    ring
  rw [e, s1, s2, s3]
  simp only [map_sub, map_ofNat]
  ring

end GlobalTheory.WeberCubicAlgebra

namespace GlobalTheory.WeberCubicAlgebra


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber in
theorem weberCubic_of_halfPeriodDiff : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  intro τ hd hj hw
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨w0, w1, w2⟩ := hw
  unfold JacobiProduct at hj
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : thetaConst 0 0 τ * thetaConst 0 1 τ * thetaConst 1 0 τ ≠ 0 := by
    rw [hj]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have t0 : thetaConst 0 0 τ ≠ 0 := fun h => hprod (by simp [h])
  have t1 : thetaConst 0 1 τ ≠ 0 := fun h => hprod (by simp [h])
  have t2 : thetaConst 1 0 τ ≠ 0 := fun h => hprod (by simp [h])
  obtain ⟨n1, n2, n3⟩ := halfPeriods_notMem τ
  have mem : ∀ p q : ℤ, ((p : ℂ) * (τ : ℂ) + q) ∈ (GlobalTheory.periodPairOfTau τ).lattice := fun p q => by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨p, q, by ring⟩
  have r1 := half_root (GlobalTheory.periodPairOfTau τ) (t := 1 / 2) (by simpa using mem 0 1) n1
  have r2 := half_root (GlobalTheory.periodPairOfTau τ) (t := (τ : ℂ) / 2) (by
    have := mem 1 0
    convert this using 1
    push_cast
    ring) n2
  have r3 := half_root (GlobalTheory.periodPairOfTau τ) (t := (1 + (τ : ℂ)) / 2) (by
    have := mem 1 1
    convert this using 1
    push_cast
    ring) n3
  have hP : ((Real.pi : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ hp
  have h12 : wp τ (1 / 2) ≠ wp τ ((τ : ℂ) / 2) := by
    rw [← sub_ne_zero, d1]
    exact mul_ne_zero hP (pow_ne_zero _ t0)
  have h13 : wp τ (1 / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    rw [← sub_ne_zero, d2]
    exact mul_ne_zero hP (pow_ne_zero _ t1)
  have h23 : wp τ ((τ : ℂ) / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    intro h
    have h' : wp τ ((1 + (τ : ℂ)) / 2) - wp τ ((τ : ℂ) / 2) = 0 := by rw [h]; ring
    rw [d3] at h'
    exact mul_ne_zero hP (pow_ne_zero _ t2) h'
  have hw1 : wp τ (1 / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP (1 / 2) := rfl
  have hw2 : wp τ ((τ : ℂ) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((τ : ℂ) / 2) := rfl
  have hw3 : wp τ ((1 + (τ : ℂ)) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((1 + (τ : ℂ)) / 2) := rfl
  rw [← hw1] at r1
  rw [← hw2] at r2
  rw [← hw3] at r3
  obtain ⟨hg, hdisc⟩ := roots_alg h12 h13 h23 r1 r2 r3 d1 d2 d3
  have hjl : jLat τ * ((GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ).g₃ ^ 2) =
      1728 * (GlobalTheory.periodPairOfTau τ).g₂ ^ 3 := by
    rw [jLat_eq, div_mul_cancel₀ _ (disc_ne_zero τ)]
  rw [hdisc, hg] at hjl
  have hs : thetaConst 0 0 τ ^ 4 = thetaConst 0 1 τ ^ 4 + thetaConst 1 0 τ ^ 4 := by
    apply mul_left_cancel₀ hP
    linear_combination -d1 + d2 + d3
  have hJ4 : thetaConst 0 0 τ ^ 4 * thetaConst 0 1 τ ^ 4 * thetaConst 1 0 τ ^ 4 =
      16 * ModularForm.eta (τ : ℂ) ^ 12 := by
    have := congrArg (· ^ 4) hj
    linear_combination this
  have a0 : (thetaConst 0 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF τ ^ 24 := by
    rw [w0]; ring
  have a1 : (thetaConst 0 1 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₁ τ ^ 24 := by
    rw [w1]; ring
  have a2 : (thetaConst 1 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₂ τ ^ 24 := by
    rw [w2]; ring
  have A0 := pow_ne_zero 4 t0
  have B0 := pow_ne_zero 4 t1
  have D0 := pow_ne_zero 4 t2
  apply cubic_eq
  apply coeffs _ _ _ _ _ _ _ A0 B0 D0 hs
  · apply mul_left_cancel₀ A0
    linear_combination weberF τ ^ 24 * hJ4 - 16 * a0
  · apply mul_left_cancel₀ B0
    linear_combination weberF₁ τ ^ 24 * hJ4 - 16 * a1
  · apply mul_left_cancel₀ D0
    linear_combination weberF₂ τ ^ 24 * hJ4 - 16 * a2
  · have h16 : (16 : ℂ) * ((Real.pi : ℂ) ^ 2) ^ 6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hP)
    apply mul_left_cancel₀ h16
    linear_combination hjl

end GlobalTheory.WeberCubicAlgebra
end
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayConv

variable {K : Type} [Field K] [NumberField K]

theorem lamIdeal_pow {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    lamIdeal (P ^ (k + 1)) = Real.log (Ideal.absNorm P) := by
  have h1 : P.IsPrime := Ideal.isPrime_of_prime hP
  unfold lamIdeal
  rw [if_pos ⟨P, k + 1, h1, hP.ne_zero, by omega, rfl⟩, Ideal.radical_pow _ (by omega), h1.radical]

theorem finite_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0) : {J : Ideal (𝓞 K) | J ∣ I}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)

theorem sum_lamIdeal (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h rfl).elim
  | h₂ I hu =>
    intro _ T hT
    have h1 : I = 1 := isUnit_iff_eq_one.1 hu
    subst h1
    rw [map_one, Nat.cast_one, Real.log_one]
    refine Finset.sum_eq_zero fun J hJ => ?_
    unfold lamIdeal
    rw [if_neg]
    rintro ⟨P, k, hP, hP0, hk, rfl⟩
    have := isUnit_of_dvd_one ((hT _).1 hJ)
    rw [isUnit_pow_iff (by omega), Ideal.isUnit_iff] at this
    exact hP.ne_top this
  | h₃ I P hI hP ih =>
    intro _ T hT
    set S := (finite_dvd hI).toFinset with hS
    have hSm : ∀ J, J ∈ S ↔ J ∣ I := fun J => by simp [hS]
    have hsub : S ⊆ T := fun J hJ => (hT J).2 (((hSm J).1 hJ).mul_left P)
    have hfin : FiniteMultiplicity P I := FiniteMultiplicity.of_prime_left hP hI
    have hN : ∀ J : Ideal (𝓞 K), J ≠ 0 → ((Ideal.absNorm J : ℕ) : ℝ) ≠ 0 := fun J hJ =>
      Nat.cast_ne_zero.2 fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
    rw [← Finset.sum_sdiff hsub, ih hI S hSm, map_mul, Nat.cast_mul, Real.log_mul (hN _ hP.ne_zero) (hN _ hI)]
    congr 1
    rw [Finset.sum_eq_single_of_mem (P ^ (multiplicity P I + 1)), lamIdeal_pow hP]
    · rw [Finset.mem_sdiff, hT, hSm]
      refine ⟨?_, hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩
      rw [pow_succ']
      exact mul_dvd_mul_left _ (pow_multiplicity_dvd _ _)
    · intro J hJ hne
      rw [Finset.mem_sdiff, hT, hSm] at hJ
      unfold lamIdeal
      rw [if_neg]
      rintro ⟨Q, k, hQ, hQ0, hk, rfl⟩
      have hQp : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
      by_cases hQP : Q = P
      · subst hQP
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h1 : Q ^ j ∣ I := by
          have := hJ.1
          rw [pow_succ'] at this
          exact (mul_dvd_mul_iff_left hP.ne_zero).1 this
        have h2 : j ≤ multiplicity Q I := hfin.le_multiplicity_of_pow_dvd h1
        have h3 : ¬ j + 1 ≤ multiplicity Q I := fun h => hJ.2 (pow_dvd_of_le_multiplicity h)
        exact hne (by rw [show j = multiplicity Q I by omega])
      · refine hJ.2 (hQp.pow_dvd_of_dvd_mul_left k ?_ hJ.1)
        intro hd
        exact hQP (associated_iff_eq.1 ((hQp.dvd_prime_iff_associated hP).1 hd))

variable {M : ℕ} (D : RayData K M)

theorem finite_idealsIn (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

end GlobalTheory.Hk.RayConv

namespace GlobalTheory.Hk


open RayConv in
theorem aRay_mul_log : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (g : D.G) (n : ℕ), aRay D g n * Real.log n = ∑ h : D.G, ∑ p ∈ n.divisorsAntidiagonal, lamRay D h p.1 * aRay D (g / h) p.2 := by
  intro K _ _ M _ D g n
  let F : D.G → ℕ → Finset (Ideal (𝓞 K)) := fun g n => (finite_idealsIn D g n).toFinset
  have hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g :=
    fun g n I => by simp [F, idealsIn]
  have ha : ∀ g n, aRay D g n = (F g n).card := fun g n => by
    unfold aRay; rw [Set.ncard_eq_toFinset_card _ (finite_idealsIn D g n)]
  have hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I := fun g n => by
    unfold lamRay; rw [finsum_mem_eq_finite_toFinset_sum _ (finite_idealsIn D g n)]
  let T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset
  have hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I := fun I hI J => by
    simp only [T]; rw [dite_eq_right hI]; simp
  have L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J := by
    rw [ha, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun I hI => ?_
    have := (hF _ _ _).1 hI
    rw [sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]
  have R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 =
      ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1 := fun h p => by
    rw [hl, ha, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [mul_comm]
  simp only [R]
  rw [L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨h, p⟩, I, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    refine ⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩,
      (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩
    rw [D.cls_mul I J a2 b2 a1 b1, a4, b4, mul_div_cancel]
  · rintro ⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    obtain ⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, rfl⟩ := hxy
    obtain rfl : J = J' := mul_left_cancel₀ a1 e1
    subst a3 b3 a4 c3 d3 c4
    rfl
  · rintro ⟨I, J⟩ hx
    simp only [Finset.mem_sigma, hF] at hx
    obtain ⟨⟨a1, a2, a3, a4⟩, hJ⟩ := hx
    obtain ⟨J', rfl⟩ := (hT _ a1 _).1 hJ
    have j1 : J ≠ ⊥ := left_ne_zero_of_mul a1
    have j2 : J' ≠ ⊥ := right_ne_zero_of_mul a1
    refine ⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]
    refine ⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩
    · rw [← a3]; exact fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)
    · rw [← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2, mul_div_cancel_left]
  · intro x _; rfl

end GlobalTheory.Hk
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → (∀ t : K, t ≠ 0 → Integrable φ (GlobalTheory.QuadFibre.fibOf μ ν q U s t)) ∧ ContinuousOn (fun t => ∫ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  first | exact @GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | exact GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | (intros; apply GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf <;> assumption)
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.averagedFibreMeasure_compl_fibre_eq_zero : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  first | exact @GlobalTheory.QuadFibre.fibOf_compl_fibre | exact GlobalTheory.QuadFibre.fibOf_compl_fibre | (intros; apply GlobalTheory.QuadFibre.fibOf_compl_fibre <;> assumption)
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.haar_disintegration_averagedFibreMeasures : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → (∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ) → μ {x | q x = 0} = 0 → ∀ φ : V → ENNReal, Measurable φ → ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t) ∂ν := by
  first | exact @GlobalTheory.QuadFibre.disintegration | exact GlobalTheory.QuadFibre.disintegration | (intros; apply GlobalTheory.QuadFibre.disintegration <;> assumption)
end
