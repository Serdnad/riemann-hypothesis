module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle024
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.polyDegreeSlashAction_right_action_properties : ∀ (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) → slP w g p ∈ degreeLT ℂ (w + 1) ∧ slP w (g * h) p = slP w h (slP w g p) ∧ slP w 1 p = p ∧ (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act | exact GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act | (intros; apply GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerDbar

def P (s : ℂ) (G : ℂ → ℂ) (d : ℂ) : Prop :=
  ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = d

lemma wirtinger_eq_zero_of_hasDerivAt {s : ℂ} {g : ℂ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' s) : P s g 0 := by
  refine ⟨_, hg.hasFDerivAt.restrictScalars ℝ, ?_⟩
  simp

lemma wirtinger_sub {s : ℂ} {G H : ℂ → ℂ} {d e : ℂ} (hG : P s G d) (hH : P s H e) :
    P s (fun z => G z - H z) (d - e) := by
  obtain ⟨L, hL, hd⟩ := hG
  obtain ⟨M, hM, he⟩ := hH
  refine ⟨L - M, hL.sub hM, ?_⟩
  simp only [ContinuousLinearMap.sub_apply]
  rw [← hd, ← he]; ring

lemma wirtinger_sum {s : ℂ} {ι : Type} (S : Finset ι) (G : ι → ℂ → ℂ) (d : ι → ℂ)
    (h : ∀ i ∈ S, P s (G i) (d i)) : P s (fun z => ∑ i ∈ S, G i z) (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hasFDerivAt_const (0 : ℂ) s, by simp⟩
  | insert a S ha ih =>
    obtain ⟨L, hL, hd⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨M, hM, he⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨L + M, ?_, ?_⟩
    · refine (hL.add hM).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha, ← hd, ← he]; simp only [ContinuousLinearMap.add_apply]; ring

lemma wirtinger_conj_mul_pow {s : ℂ} {b : ℂ → ℂ} {b' : ℂ} (hb : HasDerivAt b b' s) (j : ℕ) :
    P s (fun z => starRingEnd ℂ (b z) * z ^ j) (-2 * Complex.I * s ^ j * starRingEnd ℂ b') := by
  have h1 : HasFDerivAt (fun z => starRingEnd ℂ (b z))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) b').restrictScalars ℝ)) s :=
    Complex.conjCLE.hasFDerivAt.comp s (hb.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun z : ℂ => z ^ j)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((j : ℂ) * s ^ (j - 1))).restrictScalars ℝ) s :=
    ((hasDerivAt_pow j s).hasFDerivAt.restrictScalars ℝ)
  refine ⟨_, h1.mul h2, ?_⟩
  simp
  ring

theorem wirtinger_eichler : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧
      L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  intro w f h p hf hh s hs
  have he : ∀ (g : ℍ → ℂ) (z : ℂ), 0 < z.im → eichler w g (ofComplex z) =
      ∑ j ∈ Finset.range (w + 1), C ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w g j z) * X ^ j := by
    intro g z hz
    rw [ofComplex_apply_of_im_pos hz]
    rfl
  have hF : P s (fun z => ∑ j ∈ Finset.range (w + 1), (w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w f j z * z ^ j)
      (∑ j ∈ Finset.range (w + 1), (0 : ℂ)) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_eq_zero_of_hasDerivAt
      (((GlobalTheory.EichlerChange.hasDerivAt_ecoef w f hf j s hs).const_mul _).mul (hasDerivAt_pow j s))
  have hH : P s (fun z => ∑ j ∈ Finset.range (w + 1), starRingEnd ℂ ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w h j z) * z ^ j)
      (∑ j ∈ Finset.range (w + 1), -2 * Complex.I * s ^ j *
        starRingEnd ℂ ((w.choose j : ℂ) * ((h ∘ ofComplex) s * (-s) ^ (w - j)))) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_conj_mul_pow ((GlobalTheory.EichlerChange.hasDerivAt_ecoef w h hh j s hs).const_mul _) j
  obtain ⟨L, hL, hd⟩ := wirtinger_sub (wirtinger_sub hF hH) (wirtinger_eq_zero_of_hasDerivAt (Polynomial.hasDerivAt p s))
  refine ⟨L, hL.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hs] with z hz
    rw [he f z hz, he h z hz]

    simp [Polynomial.map_sum, eval_finsetSum]
  · rw [hd]
    have hb : (s - (starRingEnd ℂ) s) ^ w = ∑ j ∈ Finset.range (w + 1),
        s ^ j * (-(starRingEnd ℂ) s) ^ (w - j) * (w.choose j : ℂ) := by
      rw [sub_eq_add_neg, add_pow]
    rw [hb, Finset.mul_sum, Finset.sum_mul, Finset.sum_const_zero]
    simp only [zero_sub, sub_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_mul, map_natCast, map_pow, map_neg]
    ring

end GlobalTheory.EichlerDbar
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChangeGL
open GlobalTheory.EichlerChange

lemma toGL_entry (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) (i j : Fin 2) :
    (toGL g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  unfold toGL; rw [dite_eq_right h]; rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    (toGL g).det.val = ((g.det : ℤ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two,
    toGL_entry g h, toGL_entry g h, toGL_entry g h, toGL_entry g h]
  push_cast
  ring

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g h.ne']
  exact_mod_cast h

lemma denom_toGL (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) (z : ℂ) :
    denom (toGL g) z = ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) := by
  rw [denom, toGL_entry g h, toGL_entry g h]
  simp

lemma coe_toGL_smul (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) (τ : ℍ) :
    ((toGL g • τ : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * τ + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)) := by
  rw [coe_smul_of_det_pos (toGL_det_pos g h), denom_toGL g h.ne', num, toGL_entry g h.ne',
    toGL_entry g h.ne']
  simp

lemma slash_toGL (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL g) τ = f (toGL g • τ) * ((g.det : ℤ) : ℂ) ^ (k - 1) *
      (((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have hpos := toGL_det_pos g h
  rw [ModularForm.slash_apply, σ, if_pos hpos, abs_of_pos hpos, toGL_det g h.ne', denom_toGL g h.ne']
  simp

lemma eichler_I (w : ℕ) (h : ℍ → ℂ) : eichler w h UpperHalfPlane.I = 0 := by
  simp [eichler]

theorem polySlash_eichler_toGL_smul : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    ∀ (β : Matrix (Fin 2) (Fin 2) ℤ), 0 < β.det → ∀ τ : ℍ,
      slP (k - 2) β (eichler (k - 2) f (toGL β • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] toGL β) τ +
        slP (k - 2) β (eichler (k - 2) f (toGL β • UpperHalfPlane.I)) := by
  intro k hk f hf β hβ τ
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] toGL β with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := hf.slash _ _
  set a : ℂ := ((β 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((β 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((β 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((β 1 1 : ℤ) : ℂ) with hd
  set D : ℂ := ((β.det : ℤ) : ℂ) with hD
  have hdet : a * d - b * c = D := by
    rw [ha, hb, hc, hd, hD, Matrix.det_fin_two]
    push_cast
    ring
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w β p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finsetSum_coeff]
    simp only [Polynomial.coeff_smul, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ =
      (slP w β (eichler w f (toGL β • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_toGL_smul β hβ]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← denom_toGL β hβ.ne']
      exact denom_ne_zero _ _
    have hs : ((toGL β • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_toGL_smul β hβ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) (D * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (toGL β • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w β ((toGL β • τ : ℍ) : ℂ) τ (D * (c * τ + d)⁻¹)
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (toGL β • τ) * D ^ (w + 1) * (c * τ + d)⁻¹ ^ (w + 2) := by
      have e : ((w + 2 : ℕ) : ℤ) - 1 = ((w + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hdef, slash_toGL _ β hβ, e, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) * q i =
        f (toGL β • τ) * (D * (c * τ + d)⁻¹ ^ 2) * ∑ i ∈ Finset.range (w + 1),
          (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1, eichler_I, coeff_zero] at hconst
  rw [coeff_add]
  linear_combination hconst

end GlobalTheory.EichlerChangeGL
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerIntegralFromI_finset_sum : ∀ (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ), (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) → ∀ τ : ℍ, eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  first | exact @GlobalTheory.EichlerSum.eichler_finset_sum | exact GlobalTheory.EichlerSum.eichler_finset_sum | (intros; apply GlobalTheory.EichlerSum.eichler_finset_sum <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ σ : SL(2, ℤ), ∃ C : ℂ[X], ∀ τ : ℍ, slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  first | exact @GlobalTheory.EichlerChange.polySlash_eichler_smul | exact GlobalTheory.EichlerChange.polySlash_eichler_smul | (intros; apply GlobalTheory.EichlerChange.polySlash_eichler_smul <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open MeasureTheory Filter Topology Set

namespace GlobalTheory.HeckeFamilyMatrices

theorem eichler_tail_cauchy (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (hc : 0 < c)
    (hb : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) (hτ : 1 ≤ τ.im) :
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) := by
  have hI : (1:ℝ) ≤ Complex.I.im := by simp
  have i1 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le g K c m Complex.I hg.continuousOn hc hb hI).1
  have i2 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le g K c m τ hg.continuousOn hc hb hτ).1
  have t1 := intervalIntegral_tendsto_integral_Ioi 0 i1 tendsto_id
  have t2 := intervalIntegral_tendsto_integral_Ioi 0 i2 tendsto_id
  have t3 := GlobalTheory.T.tendsto_integral_shifted_segment_zero_of_exp_decay g K c m τ hg.continuousOn hc hb hτ
  have hlim : Tendsto (fun S : ℝ => Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop
      (𝓝 (Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) + (τ - Complex.I) * 0)) :=
    ((t1.const_mul _).sub (t2.const_mul _)).add (t3.const_mul _)
  rw [mul_zero, add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 0] with S hS
  exact GlobalTheory.T.integral_segment_eq_parallelogram_sides g τ S hg (by linarith) hS

theorem eichler_tail : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c →
    (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) →
    ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w,
      ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  intro w F C c hF hc hbd
  set G : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex with hGdef
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := UpperHalfPlane.mdifferentiable_iff.mp hF
  let g : ℕ → ℂ → ℂ := fun j z => G z * (-z) ^ (w - j)
  have hg : ∀ j, DifferentiableOn ℂ (g j) {z : ℂ | 0 < z.im} := fun j =>
    hG.mul ((differentiable_id.neg.pow _).differentiableOn)
  have hgb : ∀ j, ∀ z : ℂ, 1 ≤ z.im → ‖g j z‖ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w := by
    intro j z hz
    have hz0 : 0 < z.im := by linarith
    have h1 : ‖G z‖ ≤ C * Real.exp (-c * z.im) := by
      have := hbd ⟨z, hz0⟩ hz
      simpa [hGdef, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz0] using this
    have h2 : ‖(-z) ^ (w - j)‖ ≤ (1 + ‖z‖) ^ w := by
      rw [norm_pow, norm_neg]
      calc ‖z‖ ^ (w - j) ≤ (1 + ‖z‖) ^ (w - j) := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + ‖z‖) ^ w := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.sub_le _ _)
    calc ‖g j z‖ = ‖G z‖ * ‖(-z) ^ (w - j)‖ := norm_mul _ _
      _ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  set M : ℝ := ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ w
  set Lp : ℂ[X] := ∑ j ∈ Finset.range (w + 1),
      Polynomial.C ((w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I))) * X ^ j
    with hLp
  refine ⟨Lp, 2 ^ w * C * M, ?_⟩
  intro τ hτ j hj
  have hj' : j ∈ Finset.range (w + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hc1 : (eichler w F τ).coeff j = (w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) := by
    rw [eichler, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hc2 : Lp.coeff j = (w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I)) := by
    rw [hLp, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hint : (∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
      ((τ : ℂ) - Complex.I) * ∫ t in (0:ℝ)..1, g j (Complex.I + t * ((τ : ℂ) - Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; simp only [g, hGdef]; ring
  have hL5 := eichler_tail_cauchy (g j) C c w (τ : ℂ) (hg j) hc (hgb j) hτ
  have hkey : (eichler w F τ - Lp).coeff j = -((w.choose j : ℂ) * Complex.I * ∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)) := by
    rw [Polynomial.coeff_sub, hc1, hc2, hint, hL5]; ring
  rw [hkey, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have hb3 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le (g j) C c w (τ : ℂ) (hg j).continuousOn hc (hgb j) hτ).2
  have hch : ‖(w.choose j : ℂ)‖ ≤ 2 ^ w := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.choose_le_two_pow w j
  have hnn : 0 ≤ C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M := (norm_nonneg _).trans hb3
  calc ‖(w.choose j : ℂ)‖ * ‖∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)‖
      ≤ 2 ^ w * (C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M) :=
        mul_le_mul hch hb3 (norm_nonneg _) (by positivity)
    _ = 2 ^ w * C * M * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
        ring

end GlobalTheory.HeckeFamilyMatrices
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  first | exact @GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | exact GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | (intros; apply GlobalTheory.is_c1_of_finite_of_tsen_lang_systems <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_pth_power_scale_thin_shell : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 → ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  first | exact @GlobalTheory.AlmostEt.klc_scale | exact GlobalTheory.AlmostEt.klc_scale | (intros; apply GlobalTheory.AlmostEt.klc_scale <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (S : Finset L), (∀ s ∈ S, (MulAction.orbit G s).Finite) → ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧ ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | exact GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | (intros; apply GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_reps_of_cosetRepresentativeTrace : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (U : Subgroup G) [Fintype (G ⧸ U)] (S : Finset L), (∀ s ∈ S, s ∈ Fix L U) → ∀ y₀ ∈ Fix L U, ∃ (y : L) (D E : Finset G), y = ∑ d ∈ D, d • y₀ ∧ (∀ h : G, ∃! g, g ∈ E ∧ h • y = g • y ∧ ∀ s ∈ S, h • s = g • s) ∧ ∑ g ∈ E, g • y = cosetTrace U y₀ := by
  first | exact @GlobalTheory.AlmostEt.exists_reps_of_cosetTrace | exact GlobalTheory.AlmostEt.exists_reps_of_cosetTrace | (intros; apply GlobalTheory.AlmostEt.exists_reps_of_cosetTrace <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω),
  0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N → B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  first | exact @GlobalTheory.inert_fixes_root_of_unit_ratio | exact GlobalTheory.inert_fixes_root_of_unit_ratio | (intros; apply GlobalTheory.inert_fixes_root_of_unit_ratio <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  first | exact @GlobalTheory.NeedB.KumLemma.kummer_character_main | exact GlobalTheory.NeedB.KumLemma.kummer_character_main | (intros; apply GlobalTheory.NeedB.KumLemma.kummer_character_main <;> assumption)
end
