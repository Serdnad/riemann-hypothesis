module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.NormTrace
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.kOpen :
    UpperTheory.V.Af.Nf.KOpen := by
  intro M hM
  refine ⟨Subgroup.isOpen_mono (H₁ := KLev ℚ 2 M) (fun g hg => ?_) (isOpen_KLev hM), fun u hu x hx => ?_⟩
  · obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
    refine (memK M g).2 ⟨ha, hb, ?_, ?_⟩
    · simpa using hc 1 0
    · simpa using hc 1 1
  · refine (memK M _).2 ⟨?_, ?_, ⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.1, hx⟩, Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.2, neg_mem (mul_mem hu.2 hx)⟩,
        Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · exact (mul_zero _).symm
    · exact (sub_self (1 : Af ℚ)).trans (mul_zero _).symm
end

section

open CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private def cj (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![δ 0 0, -δ 0 1; -δ 1 0, δ 1 1], by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

private theorem eps_mul_cj (δ : SL(2, ℤ)) :
    eps * δ.1.map (Int.cast : ℤ → ℝ) = (cj δ).1.map (Int.cast : ℤ → ℝ) * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, cj, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_map (δ : SL(2, ℤ)) : (δ.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h := (Int.castRingHom ℝ).map_det δ.1
  rw [δ.det_coe, map_one] at h
  have h' : (δ.1.map (Int.cast : ℤ → ℝ)).det = 1 := h.symm
  rw [h']
  exact one_ne_zero

private theorem pos_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) : nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rw [← (nslMul k f).1 _ x (det_map δ) hx, (nslSl k f).1 δ, h, (nslMul k f).2.2.2]

private theorem gen_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) (h' : f ∣[(k : ℤ)] (cj δ) = c • f) :
    nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd : 0 < (eps * x).det := by
      rw [Matrix.det_mul]
      have : eps.det = -1 := by simp [eps]
      rw [this]
      linarith
    rw [← (nslMul k f).2.1, ← Matrix.mul_assoc, eps_mul_cj, Matrix.mul_assoc, pos_case k f _ hd _ c h',
      (nslMul k f).2.1]
  · exact pos_case k f x hpos δ c h

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslInv :
    UpperTheory.V.Af.Nf.NslInv := by
  intro k M f x hx
  refine ⟨fun hf δ hδ => ?_, fun χ hχ δ hδ => ?_⟩
  · have hδ' : cj δ ∈ Gamma1 M := by
      rw [Gamma1_mem] at hδ ⊢
      obtain ⟨h1, h2, h3⟩ := hδ
      refine ⟨?_, ?_, ?_⟩
      · exact h1
      · exact h2
      · show (((-δ 1 0 : ℤ)) : ZMod M) = 0
        rw [Int.cast_neg, h3, neg_zero]
    have := gen_case k f x hx δ 1 (by rw [one_smul]; exact hf δ hδ) (by rw [one_smul]; exact hf _ hδ')
    rwa [one_smul] at this
  · have hδ' : cj δ ∈ Gamma0 M := by
      rw [Gamma0_mem] at hδ ⊢
      show (((-δ 1 0 : ℤ)) : ZMod M) = 0
      rw [Int.cast_neg, hδ, neg_zero]
    exact gen_case k f x hx δ _ (hχ δ hδ) (hχ _ hδ')
end

section

open CongruenceSubgroup UpperTheory.V.Af.Nf
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Pointwise

private lemma aux {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} (F : CuspForm Γ k) (z : ℍ) :
    ∃ N : ℕ, 0 < N ∧ Function.Periodic (fun t : ℝ => F (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, F (t +ᵥ z) = 0 := by
  have h1 : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [← Subgroup.mem_strictPeriods_iff, Subgroup.strictPeriods_SL2Z]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨N, hN, -, hm⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := Γ)).1.relIndex_ne_zero h1
  have hP : (N : ℝ) ∈ Γ.strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    have := (Subgroup.mem_inf.mp hm).1
    rw [← AddChar.map_nsmul_eq_pow] at this
    simpa only [nsmul_eq_mul, mul_one] using this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : ∀ w : ℍ, Function.Periodic (fun t : ℝ => F (t +ᵥ w)) N := fun w t => by
    have := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F (t +ᵥ w) hP
    simp only
    rw [add_comm, add_vadd]
    exact this
  refine ⟨N, hN, hper z, ?_⟩
  have h0 := CuspFormClass.qExpansion_coeff_zero F hN' hP
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral F hN' hP 0 z.im_pos] at h0
  have hne : (1 / ((N : ℝ) : ℂ)) ≠ 0 := by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa using this
  have h2 := (mul_eq_zero.mp h0).resolve_left hne
  set w : ℍ := (-z.re) +ᵥ z with hw
  have h3 : ∫ t in (0 : ℝ)..N, F (t +ᵥ w) = 0 := by
    rw [← h2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pow_zero, div_one, one_mul]
    congr 1
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [hw]
  have h4 := (hper w).intervalIntegral_add_eq z.re 0
  rw [zero_add, h3] at h4
  rw [← h4]
  have h5 := intervalIntegral.integral_comp_add_right (fun t : ℝ => F (t +ᵥ w)) z.re (a := 0) (b := N)
  rw [zero_add, add_comm (N : ℝ)] at h5
  rw [← h5]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hw, vadd_vadd]
  congr 2
  ring

private lemma aux2 (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (hγ : 0 < (toR γ).val.det) (z : ℍ) : ∃ N : ℕ, 0 < N ∧
    Function.Periodic (fun t : ℝ => nsl k f (toR γ) (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f (toR γ) (t +ᵥ z) = 0 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : (ConjAct.toConjAct (toR γ)⁻¹ • (Gamma1 M : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    have := Subgroup.IsArithmetic.conj (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) γ⁻¹
    rw [← map_inv]
    exact this
  obtain ⟨N, hN, hp, hi⟩ := aux (CuspForm.translate f (toR γ)) z
  refine ⟨N, hN, ?_, ?_⟩
  · intro t
    have := hp t
    simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply]
    congr 1
  · simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right _ hi

theorem UpperTheory.V.Af.Nf.classCT :
    UpperTheory.V.Af.Nf.ClassCT := by
  intro k M hM f γ z
  have hne : (toR γ).val.det ≠ 0 := (toR γ).det_ne_zero
  rcases hne.lt_or_gt with h | h
  · let e : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)
    have he : (toR (e * γ)).val = eps * (toR γ).val := by
      rw [map_mul, Units.val_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [toR, e, eps]
    have hd : 0 < (toR (e * γ)).val.det := by
      rw [he, Matrix.det_mul]
      simpa [eps] using h
    have := aux2 k M hM f (e * γ) hd z
    rwa [he, (nslMul k f).2.1] at this
  · exact aux2 k M hM f γ h z
end
