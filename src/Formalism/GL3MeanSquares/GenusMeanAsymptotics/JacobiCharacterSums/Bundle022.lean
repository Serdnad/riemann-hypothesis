module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplBox
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplNeg
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
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

@[expose] public section

section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_pick (S : Finset ℝ) (a b : ℝ) (hab : a < b) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ ∀ s ∈ S, (b - a) / (2 * ((S.card : ℝ) + 1)) ≤ |x - s| := by
  set h : ℝ := (b - a) / (2 * ((S.card : ℝ) + 1)) with hh
  have hn : (0 : ℝ) < 2 * ((S.card : ℝ) + 1) := by positivity
  have hpos : 0 < h := div_pos (by linarith) hn
  have hmul : h * (2 * ((S.card : ℝ) + 1)) = b - a := by
    rw [hh]; field_simp
  by_contra hcon
  push Not at hcon
  have key : ∀ i ∈ Finset.range (S.card + 1), ∃ s ∈ S, |a + (2 * (i : ℝ) + 1) * h - s| < h := by
    intro i hi
    have hi' : (i : ℝ) ≤ S.card := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    apply hcon
    · nlinarith
    · nlinarith
  choose! f hfS hf using key
  have hcard : S.card < (Finset.range (S.card + 1)).card := by simp
  obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun i hi => hfS i hi)
  have h1 := hf i hi
  have h2 := hf j hj
  rw [hfij] at h1
  rw [abs_lt] at h1 h2
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    nlinarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
    nlinarith

theorem ex_choose : ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ σ₁ T' δ : ℝ, 1 - κ ≤ σ₁ ∧ σ₁ ≤ 1 - 3 * κ / 4 ∧ T ≤ T' ∧ T' ≤ T + 1 ∧ 0 < δ ∧ δ ≤ 1 / 20 ∧
      κ / (C * (T + 1) * Real.log ((M : ℝ) * (T + 2))) ≤ δ ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) := by
  obtain ⟨C0, hC0, hbox⟩ := ex_box
  refine ⟨8 * (4 * C0 + 1), by positivity, ?_⟩
  intro κ hκ hκ' M _ χ T hM hT
  obtain ⟨Z, hZ, -, hcard⟩ := hbox M χ (T + 3) hM (by linarith)
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  set N : ℝ := (Z.card : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set lg : ℝ := Real.log ((M : ℝ) * (T + 2)) with hlg
  have hx12 : (12 : ℝ) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlg2 : Real.log ((M : ℝ) * (T + 3 + 2)) ≤ 2 * lg := by
    have h1 : (M : ℝ) * (T + 3 + 2) ≤ ((M : ℝ) * (T + 2)) ^ 2 := by nlinarith
    have h2 : Real.log (((M : ℝ) * (T + 2)) ^ 2) = 2 * lg := by
      rw [Real.log_pow]; push_cast; ring
    rw [← h2]
    exact Real.log_le_log (by nlinarith) h1
  have hNb : 8 * (N + 1) ≤ 8 * (4 * C0 + 1) * (T + 1) * lg := by
    have h1 : C0 * (T + 3 + 1) * Real.log ((M : ℝ) * (T + 3 + 2)) ≤ C0 * (2 * (T + 1)) * (2 * lg) := by
      apply mul_le_mul _ hlg2 _ (by positivity)
      · apply mul_le_mul_of_nonneg_left (by linarith) hC0.le
      · apply Real.log_nonneg; nlinarith
    have h2 : 1 ≤ (T + 1) * lg := by nlinarith
    nlinarith

  obtain ⟨σ₁, hσa, hσb, hσ⟩ := ex_pick (Z.image Complex.re) (1 - κ) (1 - 3 * κ / 4) (by linarith)
  obtain ⟨T', hTa, hTb, hT'⟩ := ex_pick (Z.image (fun ρ => |ρ.im|)) T (T + 1) (by linarith)
  have hc1 : (((Z.image Complex.re).card : ℕ) : ℝ) ≤ N := by
    rw [hN]; exact Nat.cast_le.mpr Finset.card_image_le
  have hc2 : (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℕ) : ℝ) ≤ N := by
    rw [hN]; exact Nat.cast_le.mpr Finset.card_image_le
  have hδpos : 0 < κ / (8 * (N + 1)) := by positivity
  have hg1 : κ / (8 * (N + 1)) ≤
      (1 - 3 * κ / 4 - (1 - κ)) / (2 * (((Z.image Complex.re).card : ℝ) + 1)) := by
    have e : (1 - 3 * κ / 4 - (1 - κ)) = κ / 4 := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hg2 : κ / (8 * (N + 1)) ≤
      (T + 1 - T) / (2 * (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) + 1)) := by
    have e : (T + 1 - T) = 1 := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδle : κ / (8 * (N + 1)) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨σ₁, T', κ / (8 * (N + 1)), hσa, hσb, hTa, hTb, hδpos, hδle, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left hκ.le (by positivity) hNb
  · intro ρ h0 hre him
    have hmem : ρ ∈ Z := (hZ ρ).2 ⟨h0, hre, him⟩
    exact hg1.trans (hσ _ (Finset.mem_image_of_mem _ hmem))
  · intro ρ h0 hre
    by_cases him : |ρ.im| ≤ T + 3
    · have hmem : ρ ∈ Z := (hZ ρ).2 ⟨h0, hre, him⟩
      have := hT' _ (Finset.mem_image_of_mem (fun ρ : ℂ => |ρ.im|) hmem)
      rw [abs_sub_comm] at this
      exact hg2.trans this
    · push Not at him
      have : (2 : ℝ) ≤ |ρ.im| - T' := by linarith
      have h3 := le_abs_self (|ρ.im| - T')
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exm_neg {C₂ : ℝ} (hC₂ : 0 < C₂) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (T δ E : ℝ) (s : ℂ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hδ0 : 0 < δ) (him : |s.im| ≤ T + 1) (hE : 1 / ‖s - 1‖ ≤ E) (hE0 : 0 ≤ E)
    (h : ‖negLD χ s‖ ≤ C₂ * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0)) :
    ‖negLD χ s‖ ≤ C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + E := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 := exm_log_le (M : ℝ) T |s.im| hM' hT (abs_nonneg _) him
  have h2 : (if χ = 1 then 1 / ‖s - 1‖ else 0) ≤ E := by split_ifs <;> assumption
  refine h.trans (add_le_add ?_ h2)
  gcongr

theorem exm_rpow_sigma (y : ℝ) (hy : 2 ≤ y) : y ^ (1 + 1 / Real.log y) = Real.exp 1 * y := by
  have hy0 : 0 < y := by linarith
  have hl := exm_log_y y hy
  have hl0 : Real.log y ≠ 0 := by linarith
  rw [Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0, mul_one_div_cancel hl0, mul_comm]

theorem exm_core : ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 ≤ C₃ ∧ ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T σ₁ T' δ : ℝ), 3 ≤ M → 2 ≤ T →
    1 - κ ≤ σ₁ → σ₁ ≤ 1 - 3 * κ / 4 → T ≤ T' → T' ≤ T + 1 → 0 < δ → δ ≤ 1 / 20 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) →
    ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T')) →
    ∀ y : ℝ, 2 ≤ y →
      ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - explicitFormulaConstant χ - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
        1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T' +
          2 * T' * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)) +
          (3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2 +
           3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2)) := by
  obtain ⟨C₂, hC₂, hneg⟩ := ex_negLD_bound
  obtain ⟨C₃, hC₃, htail⟩ := ex_tail_bound
  refine ⟨C₂, C₃, hC₂, hC₃, ?_⟩
  intro κ hκ hκ' M _ χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim Z hZ y hy
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hly := exm_log_y y hy
  have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
  set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  set σ₀ := 1 + 1 / Real.log y with hσ₀
  have hσ₀1 : 1 < σ₀ := by
    have : 0 < 1 / Real.log y := by positivity
    linarith
  have hσ₀3 : σ₀ ≤ 3 := by
    have : 1 / Real.log y ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hly
    rw [hσ₀]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := exm_rpow_sigma y hy
  have hσ19 : 19 / 20 ≤ σ₁ := by linarith
  have hσ1 : σ₁ < 1 := by linarith
  have hT'0 : 0 < T' := by linarith

  have hBL : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ N + 4 / (3 * κ) := by
    intro t ht
    have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
    have him : ((σ₁ : ℂ) + t * I).im = t := by simp
    have hnorm : 3 * κ / 4 ≤ ‖(σ₁ : ℂ) + t * I - 1‖ := by
      have h1 := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I - 1)
      have h2 : ((σ₁ : ℂ) + t * I - 1).re = σ₁ - 1 := by simp
      rw [h2, abs_of_neg (by linarith)] at h1
      linarith
    have hne : (σ₁ : ℂ) + t * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him]; linarith) _ (by positivity)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; exact hσ19) (by rw [hre]; linarith) hne
      intro ρ hρ hρre hρs
      have h1 := Complex.abs_re_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      have h2 := Complex.abs_im_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      rw [Complex.sub_re, hre] at h1
      rw [Complex.sub_im, him] at h2
      have h3 : |ρ.im| ≤ T + 3 := by
        have : |ρ.im| ≤ |ρ.im - t| + |t| := by
          have := abs_add_le (ρ.im - t) t
          simpa using this
        linarith
      have h4 := hgapre ρ hρ hρre h3
      rw [abs_sub_comm] at h4
      linarith
    · have := one_div_le_one_div_of_le (by positivity : 0 < 3 * κ / 4) hnorm
      rwa [one_div_div] at this

  have hBH : ∀ v : ℝ, |v| = T' → ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ N + 1 := by
    intro v hv x hx hx'
    have hre : ((x : ℂ) + v * I).re = x := by simp
    have him : ((x : ℂ) + v * I).im = v := by simp
    have hnorm : 1 ≤ ‖(x : ℂ) + v * I - 1‖ := by
      have h1 := Complex.abs_im_le_norm ((x : ℂ) + v * I - 1)
      have h2 : ((x : ℂ) + v * I - 1).im = v := by simp
      rw [h2, hv] at h1
      linarith
    have hne : (x : ℂ) + v * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him, hv]; linarith) _ (by norm_num)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; linarith) (by rw [hre]; linarith) hne
      intro ρ hρ hρre _
      have h2 := Complex.abs_im_le_norm (ρ - ((x : ℂ) + v * I))
      rw [Complex.sub_im, him] at h2
      have h4 := hgapim ρ hρ hρre
      rw [← hv] at h4
      have h5 := abs_abs_sub_abs_le ρ.im v
      linarith
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnorm
      simpa using this
  have hH : ∀ v : ℝ, |v| = T' → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤
      3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2 := by
    intro v hv
    have h := ex_horiz_bound χ y σ₁ σ₀ v (N + 1) (by linarith) (by linarith) (by rw [hv]; linarith)
      (by linarith) (hBH v hv)
    have hv2 : v ^ 2 = T' ^ 2 := by rw [← hv, sq_abs]
    rw [hv2, hyσ₀] at h
    refine h.trans ?_
    have : σ₀ - σ₁ ≤ 3 := by linarith
    gcongr
  have hLf := ex_left_bound χ y σ₁ T' (N + 4 / (3 * κ)) (by linarith) (by linarith) hσ1 hT'0.le hBL
  have hTl := htail M χ y σ₀ T' (by linarith) hσ₀1 (by linarith)
  have hinv : 1 / (σ₀ - 1) = Real.log y := by rw [hσ₀]; simp
  rw [hinv, hyσ₀] at hTl
  have hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T' := by
    intro w hw1 _ hw3 hw0
    have h1 := hgapre w hw0 (by linarith) (by linarith)
    have h2 := hgapim w hw0 (by linarith)
    constructor
    · rcases hw1.lt_or_eq with h | h
      · exact h
      · rw [h] at h1; simp at h1; linarith
    · rcases hw3.lt_or_eq with h | h
      · exact h
      · rw [h] at h2; simp at h2; linarith
  have hrect := ex_rect_Fchi χ y hy0 σ₁ σ₀ T' (by linarith) hσ1 hσ₀1 hT'0 Z hZ hedge
  have hper := (perron_formula_character M χ y (by linarith) σ₀ hσ₀1).2
  unfold Formalism.ZF.rectInt at hrect
  have halg := exm_alg _ _ _ _ _ _ _ _ _ y hy0 hper hrect
  have hD : (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) / (y : ℂ) =
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) := by
    split_ifs
    · push_cast; field_simp
    · simp
  have hS : (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) / (y : ℂ) =
      ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [exKer, Complex.cpow_sub _ _ hyC, Complex.cpow_one]
    ring
  rw [hD, hS] at halg
  rw [halg]
  exact exm_norm _ _ _ _ _ y _ _ _ _ hy0 hTl hLf (hH (-T') (by rw [abs_neg, abs_of_pos hT'0]))
    (hH T' (abs_of_pos hT'0))

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
