module

public import Formalism.JumpKernelCokernel.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

def P (s : ℝ) : ℝ := 25 + 57 * s + 40 * s ^ 2 + 8 * s ^ 3

lemma hCoef_eq (x : ℝ) (hx : 1 < x) : Formalism.KernelCokernelLengths.hCoef x = P (1 / (x - 1)) := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  unfold Formalism.KernelCokernelLengths.hCoef P
  field_simp
  ring

lemma P_mono {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) : P t ≤ P s := by
  unfold P
  have hs : 0 ≤ s := le_trans ht hts
  nlinarith [mul_le_mul hts hts ht hs, pow_le_pow_left₀ ht hts 3, pow_le_pow_left₀ ht hts 2]

lemma P_ge {s : ℝ} (hs : 0 ≤ s) : 25 ≤ P s := by
  unfold P
  nlinarith [pow_nonneg hs 2, pow_nonneg hs 3]

end Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

open Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas in
theorem Formalism.KernelCokernelLengths.coefficient_height_limit : Formalism.KernelCokernelLengths.HCoefLim := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    rw [hCoef_eq x (by linarith), hCoef_eq y (by linarith)]
    apply P_mono
    · have : 0 < y - 1 := by linarith
      positivity
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro x hx
    rw [hCoef_eq x (by linarith)]
    apply P_ge
    have : 0 < x - 1 := by linarith
    positivity
  · have hs : Filter.Tendsto (fun x : ℝ => 1 / (x - 1)) Filter.atTop (nhds 0) := by
      have h := tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id)
      refine h.congr ?_
      intro x
      simp [sub_eq_add_neg]
    have hP : Continuous P := by unfold P; fun_prop
    have h25 : P 0 = 25 := by unfold P; norm_num
    have hlim : Filter.Tendsto (fun x : ℝ => P (1 / (x - 1))) Filter.atTop (nhds 25) := by
      rw [← h25]; exact (hP.tendsto 0).comp hs
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hCoef_eq x hx).symm
end
end

section

namespace Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Filter

lemma coef_le (x : ℝ) (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < (x - 1) ^ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x - 11 / 21)]

lemma coef_nonneg (x : ℝ) (hx : 11 ≤ x) : 0 ≤ (2 * x - 1) / (x - 1) ^ 2 := by
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma one_le_log (x : ℝ) (hx : 11 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

lemma logb_le (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : Real.logb x y ≤ Real.log y := by
  rw [Real.logb]
  exact div_le_self (Real.log_nonneg hy) (one_le_log x hx)

lemma logb_nonneg' (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : 0 ≤ Real.logb x y := by
  rw [Real.logb]
  exact div_nonneg (Real.log_nonneg hy) (by linarith [one_le_log x hx])

lemma eventually_log (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 13 + 2 * Real.log (4 * (n : ℝ)) ≤ c * n := by
  refine ⟨⌈256 / c ^ 2 + 26 / c⌉₊ + 1, fun n hn => ?_⟩
  have hA : 0 ≤ 256 / c ^ 2 := by positivity
  have hB : 0 ≤ 26 / c := by positivity
  have hnR : 256 / c ^ 2 + 26 / c + 1 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (256 / c ^ 2 + 26 / c)
    have h2 : ((⌈256 / c ^ 2 + 26 / c⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log (4 * n) ≤ 2 * Real.sqrt (4 * n) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 4 * n))
    rw [Real.log_sqrt (by positivity)] at h
    linarith [Real.sqrt_nonneg (4 * (n : ℝ))]
  have hsq : Real.sqrt (4 * n) = 2 * Real.sqrt n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hs16 : 16 / c ≤ Real.sqrt n := by
    have h1 : (16 / c) ^ 2 ≤ (n : ℝ) := by
      have : (16 / c) ^ 2 = 256 / c ^ 2 := by ring
      linarith
    calc 16 / c = Real.sqrt ((16 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1
  have h16 : 16 ≤ c * Real.sqrt n := by
    rw [div_le_iff₀ hc] at hs16
    linarith
  have h26 : 26 ≤ c * n := by
    have : 26 / c ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hcn : c * n = (c * Real.sqrt n) * Real.sqrt n := by rw [mul_assoc, hss]
  nlinarith [mul_le_mul_of_nonneg_right h16 hs0]

end Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas in
theorem Formalism.KernelCokernelLengths.thickness_first_bound : Formalism.KernelCokernelLengths.ThickA := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_log (ε / 2) (by linarith)
  refine ⟨min (1 / 10) (ε / 10), by positivity, max N 4, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hδ1 : min (1 / 10) (ε / 10) ≤ 1 / 10 := min_le_left _ _
  have hδε : min (1 / 10) (ε / 10) ≤ ε / 10 := min_le_right _ _
  have hbN : N ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : 4 ≤ b := le_trans (le_max_right _ _) hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hb4R : (4 : ℝ) ≤ b := by exact_mod_cast hb4
  have hℓ' : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hH1 : (1 : ℝ) ≤ 2 * ((h + (η + t + 1) : ℕ) : ℝ) := by
    have : 1 ≤ h + (η + t + 1) := by omega
    have : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hHle : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by
    have : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
    exact_mod_cast this
  have hδb : min (1 / 10) (ε / 10) * (b : ℝ) ≤ ε / 10 * b := mul_le_mul_of_nonneg_right hδε hb0
  have hδb1 : min (1 / 10) (ε / 10) * (b : ℝ) ≤ 1 / 10 * b := mul_le_mul_of_nonneg_right hδ1 hb0
  have hcoef := coef_le ℓ hℓ'
  have hcoef0 := coef_nonneg ℓ hℓ'
  have hlogb := logb_le ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have hlogb0 := logb_nonneg' ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have h2H : 2 * ((h + (η + t + 1) : ℕ) : ℝ) ≤ 4 * b := by
    have hη' : (η : ℝ) ≤ 1 / 10 * b := le_trans hη hδb1
    have hS' : (S : ℝ) ≤ 1 / 10 * b := le_trans hS hδb1
    have ht' : (t : ℝ) ≤ 1 / 10 * b := le_trans ht hδb1
    linarith
  have hlog2H : Real.log (2 * ((h + (η + t + 1) : ℕ) : ℝ)) ≤ Real.log (4 * b) :=
    Real.log_le_log (by linarith) h2H
  have hlogN := hN b hbN
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) =
      ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) + 3 +
        (Real.logb (ℓ : ℝ) (2 * ((h + (η + t + 1) : ℕ) : ℝ)) + 1) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    rw [mul_div_assoc]
  have hHc : ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) ≤
      ((h + (η + t + 1) : ℕ) : ℝ) * (21 / 100) :=
    mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) := by
    rw [haR]
    have := mul_nonneg (Nat.cast_nonneg (h + (η + t + 1))) hcoef0
    linarith
  have hceil : (⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ : ℝ) ≤
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) + 1 := (Nat.ceil_lt_add_one haR0).le
  have hεb : 0 ≤ ε * (b : ℝ) := mul_nonneg hε.le hb0
  push_cast
  push_cast at hHle hHc hceil haR hlogb hlog2H
  linarith
end

section

namespace Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

lemma coef_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) :
    (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpos : 0 < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 21 * ℓ - 11)]

lemma log_two_le (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 100 + 98 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 100 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)
  have h3 : Real.log x = Real.log (x / 100) + Real.log 100 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    field_simp
  linarith

lemma one_le_log (ℓ : ℕ) (hℓ : 11 ≤ ℓ) : 1 ≤ Real.log (ℓ : ℝ) := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma logb_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    Real.logb (ℓ : ℝ) x ≤ Real.log x := by
  exact div_le_self (Real.log_nonneg hx) (one_le_log ℓ hℓ)

lemma logb_nonneg' (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.logb (ℓ : ℝ) x := by
  have h : (1 : ℝ) < ℓ := by
    have : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  exact Real.logb_nonneg h hx

end Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas in
theorem Formalism.KernelCokernelLengths.thickness_second_bound : Formalism.KernelCokernelLengths.ThickB := by
  refine ⟨1 / 100, by norm_num, 10000, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hbR : (10000 : ℝ) ≤ b := by exact_mod_cast hb
  have hη' : 100 * η ≤ b := by
    have : ((100 * η : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have hS' : 100 * S ≤ b := by
    have : ((100 * S : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have ht' : 100 * t ≤ b := by
    have : ((100 * t : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  refine ⟨by omega, by omega, ?_⟩
  have hHn : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
  have hH1 : 1 ≤ h + (η + t + 1) := by omega
  have hHR : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by exact_mod_cast hHn
  have hH1R : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast hH1
  have hbi : b ≤ bi + t + 1 := h1
  have hbiR : (b : ℝ) ≤ bi + t + 1 := by exact_mod_cast hbi
  set H : ℕ := h + (η + t + 1) with hHdef
  have hx1 : (1 : ℝ) ≤ 2 * (H : ℝ) := by linarith
  have hlb := logb_le ℓ hℓ (2 * (H : ℝ)) hx1
  have hlb0 := logb_nonneg' ℓ hℓ (2 * (H : ℝ)) hx1
  have hlog := log_two_le (2 * (H : ℝ)) (by linarith)
  have hc := coef_le ℓ hℓ
  have hcoef0 : 0 ≤ (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    apply div_nonneg <;> nlinarith
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hA : (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hc hH0
  have hA0 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc]; positivity
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H ≤ (H : ℝ) * (21 / 100) + 4 + ((2 * (H : ℝ)) / 100 + 98) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have hceil := Nat.ceil_lt_add_one haR0
  have hηR : (100 : ℝ) * η ≤ b := by exact_mod_cast hη'
  have hSR : (100 : ℝ) * S ≤ b := by exact_mod_cast hS'
  have htR : (100 : ℝ) * t ≤ b := by exact_mod_cast ht'
  have key : ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (bi : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast key
end

section

namespace Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem main (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) (N : Submodule O M) (hN : N.map f ≤ N) :
    Module.length O (↥N ⧸ (N.map f).comap N.subtype) ≤ Module.length O (LinearMap.ker f) := by
  have hNf : ∀ x ∈ N, f x ∈ N := fun x hx => hN (Submodule.mem_map_of_mem hx)
  let g : N →ₗ[O] ↥((N.map f).comap N.subtype) :=
    LinearMap.codRestrict ((N.map f).comap N.subtype) (f.restrict hNf)
      (fun x => Submodule.mem_comap.2 (Submodule.mem_map_of_mem x.2))
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_comap.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have hNfin : Module.length O N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective N.subtype N.injective_subtype)
  have hQfin : Module.length O ((N.map f).comap N.subtype) ≠ ⊤ :=
    ne_top_of_le_ne_top hNfin (Module.length_le_of_injective _ (Submodule.injective_subtype _))
  have e1 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype ((N.map f).comap N.subtype))
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ ((N.map f).comap N.subtype))
  have e2 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype (LinearMap.ker g)) hgs
    (LinearMap.exact_subtype_ker_map g)
  have e3 : Module.length O (↥N ⧸ (N.map f).comap N.subtype) = Module.length O (LinearMap.ker g) := by
    rw [e1, add_comm] at e2
    exact WithTop.add_right_cancel hQfin e2
  rw [e3]
  refine Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker f) (N.subtype.comp (LinearMap.ker g).subtype) ?_) ?_
  · intro x
    exact LinearMap.mem_ker.2
      (congrArg (fun z : ↥((N.map f).comap N.subtype) => ((z : N) : M)) (LinearMap.mem_ker.1 x.2))
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h

end Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem Formalism.KernelCokernelLengths.kernel_cokernel_lengths : Formalism.KernelCokernelLengths.KerCoker := by
  intro O _ M _ _ hM f N hN
  exact Formalism.KernelCokernelLengths.KernelCokernelLemmas.main O M hM f N hN
end

section

namespace Formalism.KernelCokernelLengths

theorem fil_eq_of_noJump {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (Fil : ℤ → Submodule K D) (b η : ℕ)
    (hj : ∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) :
    ∀ k : ℕ, ∀ j : ℤ, -(b : ℤ) < j → j + k = -(η : ℤ) → Fil j = Fil (-(η : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro j _ hjk
    simp only [Nat.cast_zero, add_zero] at hjk
    rw [hjk]
  | succ k ih =>
    intro j hjb hjk
    have hlt : j < -(η : ℤ) := by push_cast at hjk; omega
    rw [hj j hjb hlt]
    exact ih (j + 1) (by omega) (by push_cast at hjk ⊢; omega)

theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro K _ D _ _ Fil hA χ hχ b η w hj hw
  have h1 : ∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i) := by
    intro i hi
    have hne : χ ^ i - 1 ≠ 0 := sub_ne_zero.mpr (hχ i hi)
    have h2 := (Fil (-i)).smul_mem (χ ^ i - 1)⁻¹ (hw i)
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  refine ⟨h1, fun i hi hib => ?_⟩
  by_cases hη : (η : ℤ) ≤ i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, -i + k = -(η : ℤ) := ⟨(i - η).toNat, by omega⟩
    rw [← fil_eq_of_noJump Fil b η hj k (-i) (by omega) hk]
    exact h1 i hi
  · exact hA (by omega : -(η : ℤ) ≤ -i) (h1 i hi)

end Formalism.KernelCokernelLengths
end

section

namespace Formalism.KernelCokernelLengths

theorem power_binomial_bound : PowBinom := by
  intro A _ ℓ u ε q b Y hℓ hY
  set k := (Y - 1) / ℓ with hk
  set I : Ideal A := Ideal.span {(ℓ : A), q ^ ℓ} with hI
  have hYle : Y ≤ ℓ * (k + 1) := by
    have h := Nat.lt_mul_div_succ (Y - 1) (show 0 < ℓ by omega)
    rw [← hk] at h
    omega
  have hmem : (u * q ^ ℓ + (ℓ : A) * ε) ^ b ∈
      Ideal.span {(ℓ : A) ^ (b - k)} ⊔ Ideal.span {q ^ Y} * I ^ (b - k - 1) := by
    rw [add_pow]
    refine Ideal.sum_mem _ (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    by_cases hmk : m ≤ k
    · apply Ideal.mem_sup_left
      rw [Ideal.mem_span_singleton]
      have h1 : (ℓ : A) ^ (b - k) ∣ ((ℓ : A) * ε) ^ (b - m) := by
        rw [mul_pow]; exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
    · apply Ideal.mem_sup_right
      obtain ⟨e, rfl⟩ : ∃ e, m = k + 1 + e := ⟨m - (k + 1), by omega⟩
      have hℓI : (ℓ : A) ∈ I := Ideal.subset_span (by simp)
      have hqI : q ^ ℓ ∈ I := Ideal.subset_span (by simp)
      have hin : (q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) ∈ I ^ (b - k - 1) := by
        have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hqI e)
          (Ideal.pow_mem_pow hℓI (b - (k + 1 + e)))
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      have hp : q ^ (ℓ * (k + 1)) = q ^ Y * q ^ (ℓ * (k + 1) - Y) := by
        rw [← pow_add]; congr 1; omega
      have heq : (u * q ^ ℓ) ^ (k + 1 + e) * ((ℓ : A) * ε) ^ (b - (k + 1 + e)) *
            (b.choose (k + 1 + e) : A) =
          q ^ Y * ((q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) *
            (u ^ (k + 1 + e) * q ^ (ℓ * (k + 1) - Y) * ε ^ (b - (k + 1 + e)) *
              (b.choose (k + 1 + e) : A))) := by
        have hq : (q ^ ℓ) ^ (k + 1 + e) = q ^ Y * q ^ (ℓ * (k + 1) - Y) * (q ^ ℓ) ^ e := by
          rw [pow_add, ← pow_mul, hp]
        rw [mul_pow, mul_pow, hq]
        ring
      rw [heq]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hin)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hc
  exact ⟨α, β, by rw [← hac]; ring, hβ⟩

end Formalism.KernelCokernelLengths
end

section

namespace Formalism.KernelCokernelLengths

theorem column_degree_bound : CDge := by
  intro ℓ hℓ bi S η h hh
  have h2 : bi + S + η ≤ h + η := by omega
  gcongr
  all_goals first
    | exact_mod_cast h2
    | (rw [sub_nonneg]; exact_mod_cast (by omega : 1 ≤ ℓ))
    | (rw [sub_pos]; exact_mod_cast (by omega : 1 < ℓ))

end Formalism.KernelCokernelLengths
end

section

theorem Formalism.KernelCokernelLengths.filtration_exponent_holds : Formalism.KernelCokernelLengths.FExp := by
  intro R _ u π₀ q ℓ hℓ Mi h hMi
  set m := h / (ℓ - 1) with hm
  have hpos : 0 < ℓ - 1 := by omega
  have hk : Mi + 1 ≤ (ℓ - 1) * (m + 1) := by
    have := Nat.lt_mul_div_succ h hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hMi this)
  obtain ⟨d, hd⟩ : ∃ d, (ℓ - 1) * (m + 1) = Mi + 1 + d := ⟨_, (Nat.add_sub_cancel' hk).symm⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨u ^ (m + 1) * q ^ d, ?_⟩
  rw [mul_pow, mul_pow, ← pow_mul, hd, pow_add]
  ring
end

section

namespace Formalism.KernelCokernelLengths

theorem jump_shift_holds : JumpShift := by
  intro s S η t a ht
  refine ⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

end Formalism.KernelCokernelLengths
end
