module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle001
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem neg_inv_SL (a : SL(2, ℤ)) : (-a)⁻¹ = -a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [neg_mul_neg, mul_inv_cancel]

def pmSub (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa only [mul_neg] using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa only [neg_mul] using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa only [neg_mul_neg] using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have := Γ.inv_mem ha
      rwa [neg_inv_SL] at this

theorem mem_pmSub {Γ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} : g ∈ pmSub Γ ↔ g ∈ Γ ∨ -g ∈ Γ := by
  rfl

theorem le_pmSub (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmSub Γ := by
  intro g hg
  exact Or.inl hg

theorem relIndex_pmSub {Γ : Subgroup SL(2, ℤ)} (hm : (-1 : SL(2, ℤ)) ∉ Γ) : Γ.relIndex (pmSub Γ) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨-1, mem_pmSub.2 (Or.inr (by rw [neg_neg]; exact Γ.one_mem)), fun b hb => ?_⟩
  rw [mul_neg_one]
  rcases mem_pmSub.1 hb with h | h
  · refine Or.inr ⟨h, fun h' => hm ?_⟩
    have := Γ.mul_mem (Γ.inv_mem h) h'
    rwa [mul_neg, inv_mul_cancel] at this
  · refine Or.inl ⟨h, fun h' => hm ?_⟩
    have := Γ.mul_mem (Γ.inv_mem h') h
    rwa [mul_neg, inv_mul_cancel] at this

theorem reps_index : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ →
    ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  intro Γ hΓ hm
  have : (pmSub Γ).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSub Γ)
  let e : Fin (Nat.card (SL(2, ℤ) ⧸ pmSub Γ)) ≃ SL(2, ℤ) ⧸ pmSub Γ :=
    (Finite.equivFin (SL(2, ℤ) ⧸ pmSub Γ)).symm
  refine ⟨Nat.card (SL(2, ℤ) ⧸ pmSub Γ), fun i => (Quotient.out (e i))⁻¹, ⟨fun x => ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := e.surjective (QuotientGroup.mk x⁻¹)
    have hq : (QuotientGroup.mk (Quotient.out (e i)) : SL(2, ℤ) ⧸ pmSub Γ) = QuotientGroup.mk x⁻¹ := by
      rw [hi]; exact QuotientGroup.out_eq' _
    have hp := QuotientGroup.eq.1 hq
    have hx : x = ((Quotient.out (e i))⁻¹ * x⁻¹)⁻¹ * (Quotient.out (e i))⁻¹ := by group
    refine ⟨i, ?_⟩
    rcases mem_pmSub.1 ((pmSub Γ).inv_mem hp) with h | h
    · exact ⟨_, h, Or.inl hx⟩
    · refine ⟨_, h, Or.inr ?_⟩
      rw [neg_mul, neg_neg]
      exact hx
  · intro i j γ hγ hij
    dsimp only at hij
    have hp : ∃ p ∈ pmSub Γ, (Quotient.out (e i))⁻¹ = p * (Quotient.out (e j))⁻¹ := by
      rcases hij with h | h
      · exact ⟨γ, le_pmSub Γ hγ, h⟩
      · refine ⟨-γ, mem_pmSub.2 (Or.inr (by rw [neg_neg]; exact hγ)), ?_⟩
        rw [h, neg_mul]
    obtain ⟨p, hpP, hpe⟩ := hp
    have hmem : (Quotient.out (e j))⁻¹ * Quotient.out (e i) ∈ pmSub Γ := by
      have : (Quotient.out (e j))⁻¹ * Quotient.out (e i) = p⁻¹ := by
        have hi : Quotient.out (e i) = Quotient.out (e j) * p⁻¹ := by
          rw [← inv_inv (Quotient.out (e i)), hpe, mul_inv_rev, inv_inv]
        rw [hi, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact (pmSub Γ).inv_mem hpP
    have hq := QuotientGroup.eq.2 hmem
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at hq
    exact e.injective hq.symm
  · rw [← Subgroup.relIndex_mul_index (le_pmSub Γ), relIndex_pmSub hm]
    rfl

end GlobalTheory.OddFrame
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem slash_periodic_comp {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) := by
  have key : ∀ τ : ℍ, (f ∣[k] x) ((M : ℝ) +ᵥ τ) = (f ∣[k] x) τ := by
    intro τ
    have hT : (ModularGroup.T ^ (M : ℤ)) • τ = (M : ℝ) +ᵥ τ := by
      rw [modular_T_zpow_smul]; simp
    have hδ : x * ModularGroup.T ^ (M : ℤ) * x⁻¹ ∈ Γ := by
      have h1 : ModularGroup.T ^ (M : ℤ) ∈ CongruenceSubgroup.Gamma M := by
        simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
      exact hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem _ h1 x)
    have e : (f ∣[k] x) ∣[k] (ModularGroup.T ^ (M : ℤ)) = f ∣[k] x := by
      rw [← SlashAction.slash_mul,
        (inv_mul_cancel_right (x * ModularGroup.T ^ (M : ℤ)) x).symm,
        SlashAction.slash_mul, hf.1 _ hδ]
    have h := congrFun e τ
    have hden : denom (ModularGroup.T ^ (M : ℤ) : SL(2, ℤ)) τ = 1 := by
      rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
    rw [ModularForm.SL_slash_apply (f := f ∣[k] x), hT, hden, one_zpow, mul_one] at h
    exact h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert key ⟨w, hw⟩ using 2
    ext
    simp [ofComplex_apply_of_im_pos hw', add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_slash {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (M : ℝ) (f ∣[k] x)) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast hM) (slash_periodic_comp hΓ hf x)
    (mdiff_slash hf.2.1 k x) (hf.2.2 x)

theorem qParam_one_vadd_eq_exp_mul (M : ℕ) (τ : ℍ) :
    Function.Periodic.qParam (M : ℝ) (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / M) * Function.Periodic.qParam (M : ℝ) (τ : ℂ) := by
  simp only [Function.Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_unique_of_hasSum {h : ℝ} {g : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam h (τ : ℂ) ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem co_transform (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (hM : 0 < M)
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) :
    (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n =
        Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧
      (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧
      (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun x n => ?_, fun γ hγ x n => ?_, fun hk x n => ?_⟩
  · set ζ := Complex.exp (2 * Real.pi * Complex.I / M)
    have happ : ∀ τ : ℍ, (f ∣[k] (x * ModularGroup.T)) τ = (f ∣[k] x) ((1 : ℝ) +ᵥ τ) := by
      intro τ
      rw [slash_mul_apply, modular_T_smul]
      have hden : denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
        rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
      rw [hden, one_zpow, mul_one]
    have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (ζ ^ m * co M k f x m) •
        Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ m) ((f ∣[k] (x * ModularGroup.T)) τ) := by
      intro τ
      have h := hasSum_qExpansion hM' (slash_periodic_comp hΓ hf x) (mdiff_slash hf.2.1 k x)
        (hf.2.2 x) ((1 : ℝ) +ᵥ τ)
      rw [happ]
      convert h using 1
      funext m
      rw [qParam_one_vadd_eq_exp_mul, co, smul_eq_mul, smul_eq_mul, mul_pow]
      ring
    exact (coeff_unique_of_hasSum hM'
      (analyticAt_cuspFunction_slash hM hΓ hf (x * ModularGroup.T)) hsum n).symm
  · simp only [co, hf.slash_mul hγ x]
  · simp only [co, slash_neg_of_odd hk f x]
    rw [qExpansion_neg (analyticAt_cuspFunction_slash hM hΓ hf x)]
    simp

end GlobalTheory.OddFrame
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem weights_nonneg_of_det {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {r : ℕ} {s : Fin r → SL(2, ℤ)}
    {w : Fin r → ℤ} {F : Fin r → ℍ → ℂ} (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∃ τ, (evM s w F τ).det ≠ 0) (j : Fin r) : 0 ≤ w j := by
  by_contra hneg
  push_neg at hneg
  have h0 : F j = 0 := (hF j).eq_zero_of_neg hneg
  obtain ⟨τ, hτ⟩ := hdet
  apply hτ
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  simp [evM, h0, SlashAction.zero_slash]

theorem mul_det_evM_update {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (j₀ : Fin r) (w' : ℤ) (G E : ℍ → ℂ) (e : Fin r → ℍ → ℂ)
    (hrel : ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ * (G ∣[w'] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ) (τ : ℍ) :
    E τ * (evM s (Function.update w j₀ w') (Function.update F j₀ G) τ).det =
      e j₀ τ * (evM s w F τ).det := by
  have hM : evM s (Function.update w j₀ w') (Function.update F j₀ G) τ =
      (evM s w F τ).updateCol j₀ (fun i => (G ∣[w'] s i) τ) := by
    ext i j
    by_cases hj : j = j₀
    · subst hj; simp [evM, Matrix.updateCol_apply]
    · simp [evM, Matrix.updateCol_apply, hj, Function.update_of_ne hj]
  rw [hM, ← Matrix.det_updateCol_smul]
  have hc : (E τ • fun i => (G ∣[w'] s i) τ) =
      fun i => ∑ j, (fun j => e j τ) j • (evM s w F τ) i j := by
    ext i
    simp [evM, hrel]
  rw [hc, Matrix.det_updateCol_sum, smul_eq_mul]

theorem oddFrame_descent_of_weight_sum (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (r : ℕ) (s : Fin r → SL(2, ℤ)) :
    ∀ (n : ℕ) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), ∑ j, (w j).toNat = n →
      (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) →
      ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧
        (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w F hn hF hdet
  by_cases hR : Reduces Γ w F
  swap
  · exact ⟨w, F, hF, hdet, hR⟩
  obtain ⟨j₀, w₀, G, E, e, hlt, hodd, hG, he, hne, hrel⟩ := hR
  set w₁ := Function.update w j₀ w₀ with hw₁
  set F₁ := Function.update F j₀ G with hF₁
  have hF' : ∀ j, Odd (w₁ j) ∧ IsMF Γ (w₁ j) (F₁ j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj; simp [w₁, F₁, hodd, hG]
    · simp only [w₁, F₁, Function.update_of_ne hj]; exact hF j
  have hdet' : ∃ τ, (evM s w₁ F₁ τ).det ≠ 0 := by
    have hd0 : (fun τ => (evM s w F τ).det) ≠ 0 := by
      obtain ⟨τ, hτ⟩ := hdet
      intro h; exact hτ (congrFun h τ)
    have hmd : MDiff (fun τ => (evM s w F τ).det) := mdiff_det_evM s w (fun j => (hF j).2.2.1)
    have hprod : e j₀ * (fun τ => (evM s w F τ).det) ≠ 0 := by
      rw [Ne, UpperHalfPlane.mul_eq_zero_iff (he j₀) hmd]
      push_neg; exact ⟨hne, hd0⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, e j₀ τ * (evM s w F τ).det ≠ 0 := by
      by_contra h
      push_neg at h
      exact hprod (funext fun τ => by simpa using h τ)
    refine ⟨τ, fun h0 => hτ ?_⟩
    rw [← mul_det_evM_update s w F j₀ w₀ G E e hrel τ]
    rw [show w₁ = Function.update w j₀ w₀ from rfl, show F₁ = Function.update F j₀ G from rfl] at h0
    rw [h0, mul_zero]
  have hnn := weights_nonneg_of_det (fun j => (hF j).2) hdet
  have hnn' := weights_nonneg_of_det (fun j => (hF' j).2) hdet'
  have hlt' : ∑ j, (w₁ j).toNat < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = j₀
      · subst hj; simp only [w₁, Function.update_self]; omega
      · simp only [w₁, Function.update_of_ne hj]; exact le_rfl
    · refine ⟨j₀, Finset.mem_univ _, ?_⟩
      have := hnn' j₀
      simp only [w₁, Function.update_self] at this ⊢
      have := hnn j₀
      omega
  exact ih _ hlt' w₁ F₁ rfl hF' hdet'

theorem descent : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ),
    Γ.FiniteIndex → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) →
    ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧
      (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  intro Γ r s w F hΓ hF hdet
  exact oddFrame_descent_of_weight_sum Γ r s _ w F rfl hF hdet

end GlobalTheory.OddFrame
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section
namespace GlobalTheory.OddFrame

theorem levelOne_mul_slash {k w : ℤ} (g : ModularForm 𝒮ℒ (k - w)) (F : ℍ → ℂ) (x : SL(2, ℤ)) :
    ((⇑g) * F) ∣[k] x = (⇑g) * (F ∣[w] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w) w x (⇑g) F
  rw [sub_add_cancel] at h
  rw [h, (isMF_coe_top g).slash_top x]

theorem sum_finrank_le_finrank_cuspForm (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ) (hΓ : Γ.FiniteIndex) (hfin : FiniteDimensional ℂ (CuspForm Γ k))
    (hF : ∀ j, IsCF Γ (w j) (F j)) (hdet : ∀ τ, (evM s w F τ).det ≠ 0) :
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  have hcf : ∀ (j : Fin r) (g : ModularForm 𝒮ℒ (k - w j)), IsCF Γ k ((⇑g) * F j) := fun j g =>
    ((isMF_coe_top g).mono le_top).mul_isCF (hF j) (by ring)
  have happ : ∀ (c : Fin r → CuspForm Γ k) (τ : ℍ), (∑ j, c j) τ = ∑ j, c j τ := by
    intro c τ
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.add_apply, ih]
  let L : (Π j, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] CuspForm Γ k :=
    { toFun := fun g => ∑ j, (hcf j (g j)).toCF
      map_add' := by
        intro a b; ext τ
        simp only [CuspForm.add_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.add_apply, ModularForm.add_apply,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a; ext τ
        simp only [CuspForm.smul_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.smul_apply, ModularForm.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∀ τ, ∑ j, g j τ * F j τ = 0 := by
      intro τ
      have := congrArg (fun f : CuspForm Γ k => f τ) hg
      simpa [L, happ] using this
    have hfun : (∑ j, (⇑(g j)) * F j) = 0 := by
      ext τ; simpa [Finset.sum_apply] using h0 τ
    have hvec : ∀ τ, Matrix.mulVec (evM s w F τ) (fun j => g j τ) = 0 := by
      intro τ; ext i
      have h1 := congrArg (fun f => (f ∣[k] s i) τ) hfun
      simp only [SlashAction.zero_slash, Pi.zero_apply] at h1
      rw [SlashAction.sum_slash] at h1
      simp only [levelOne_mul_slash, Finset.sum_apply, Pi.mul_apply] at h1
      simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
      rw [← h1]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j; ext τ
    have := Matrix.eq_zero_of_mulVec_eq_zero (hdet τ) (hvec τ)
    exact congrFun this j
  haveI : FiniteDimensional ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := inferInstance
  calc ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j))
      = Module.finrank ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := (Module.finrank_pi_fintype ℂ).symm
    _ ≤ Module.finrank ℂ (CuspForm Γ k) := LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem discriminant_slash_specialLinearGroup (x : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] x) = ModularForm.discriminant :=
  (isCF_coe_top CuspForm.discriminant).1 x (Subgroup.mem_top x)

theorem exists_eq_discriminant_mul (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ) (hH : IsMF Γ K H)
    (hdec : ∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  have hsl : ∀ x : SL(2, ℤ), (H / ModularForm.discriminant) ∣[K - 12] x =
      (H ∣[K] x) / ModularForm.discriminant := by
    intro x
    have := ModularForm.div_slash_SL2 K 12 x H ModularForm.discriminant
    rw [discriminant_slash_specialLinearGroup] at this
    exact this
  refine ⟨H / ModularForm.discriminant, ⟨fun γ hγ => ?_, ?_, fun x => ?_⟩, ?_⟩
  · rw [hsl, hH.1 γ hγ]
  · exact hH.2.1.div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  · rw [hsl, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO ((hdec x).trans ModularForm.exp_isBigO_discriminant)).isBigO_one ℝ
  · ext τ
    simp [mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

end GlobalTheory
end

section

namespace GlobalTheory.PowerDifferenceNorm

theorem norm_pow_sub_pow_lt_one_of_ultra {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  rcases n with _ | n
  · simp
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1)
        = x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hx)) ih
    · have hp : ‖y ^ (n + 1)‖ ≤ 1 :=
        (norm_pow_le' y n.succ_pos).trans (pow_le_one₀ (norm_nonneg _) hy)
      exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hp)) h

theorem norm_pow_sub_pow_lt_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x y : Formalism.ConjugateSelfDual.Qbar l}, ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) →
      ‖x - y‖ < (1 : ℝ) → ∀ (n : ℕ), ‖x ^ n - y ^ n‖ < (1 : ℝ) := by
  intro l _ x y hx hy h n
  exact norm_pow_sub_pow_lt_one_of_ultra hx hy h n

end GlobalTheory.PowerDifferenceNorm
end

section


theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_exists_norm_one_mod : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → (∀ u v : ℚ, padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1) → (∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ e ∈ W, h e e = 1) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1 := by
  first | exact @GlobalTheory.selfDual_lattice_exists_norm_one_mod | exact GlobalTheory.selfDual_lattice_exists_norm_one_mod | (intros; apply GlobalTheory.selfDual_lattice_exists_norm_one_mod <;> assumption)
end
