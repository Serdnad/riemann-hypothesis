module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.ModularForms.NormTrace
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem smul_vOp_eq_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : (q : ℂ) ^ (k - 1) • vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  set g := (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) with hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hdet : (g.det : ℝ) = q := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdpos : 0 < (g.det : ℝ) := by rw [hdet]; exact_mod_cast hq
  ext τ
  have hden : denom g τ = 1 := by simp [denom, h10, h11]
  have hnum : num g τ = q * τ := by simp [num, h00, h01]
  have hsmul : ((g • τ : ℍ) : ℂ) = q * τ := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, hnum, hden, div_one]
  have hof : ofComplex ((q : ℂ) * τ) = g • τ := by
    rw [← hsmul]; exact ofComplex_apply _
  rw [slash_apply, hden, one_zpow, mul_one, hdet, abs_of_pos (by exact_mod_cast hq : (0:ℝ) < q)]
  simp only [σ, hdpos, if_true, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, vOp, hof]
  push_cast
  ring_nf
  rfl

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem uOp_eq_sum_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  funext z
  rw [Finset.sum_apply, uOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set g := Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne')) with hg
  have hval : g.1 = !![(1 : ℝ), (j : ℝ); 0, (q : ℝ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hg]
  have hdet : g.det.val = (q : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval]; simp
  have hpos : 0 < g.det.val := by rw [hdet]; exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [slash_apply, σ, ite_eq_left hpos, abs_of_pos hpos, hdet, ← ofComplex_apply (g • z),
    coe_smul_of_det_pos hpos]
  simp [num, denom, hval]
  rw [mul_assoc, ← zpow_neg (q : ℂ) k, ← zpow_add₀ hq0,
    show k - 1 + -k = -1 by omega, zpow_neg_one, mul_comm]

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.Hk

private theorem finiteIndex_lev_of_pos' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

private theorem isCusp_SL2Z_ratGL_smul' (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspForm_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l →
    0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ,
    IsCusp c (GlobalTheory.Hk.lev N l) →
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := finiteIndex_lev_of_pos' N l hN hl
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [← OnePoint.IsZeroAt.smul_iff]
  have h := isCusp_SL2Z_ratGL_smul' g hc
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((GlobalTheory.Hk.lev N l : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ))] at h
  exact f.zero_at_cusps' h

end GlobalTheory.Hk
end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex : ∀ (N l : ℕ), 0 < N → 0 < l → (GlobalTheory.Hk.lev N l).FiniteIndex := by
  intro N l hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex_of_pos (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

theorem isCusp_SL2Z_smul_ratGL (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  refine ⟨g • c, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

theorem slash_rat_isBoundedAt :
    ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) →
      ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) →
        c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := lev_finiteIndex_of_pos N l hN hl
  have key : IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) (GlobalTheory.Hk.lev N l) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact isCusp_SL2Z_smul_ratGL g hc
  exact OnePoint.IsBoundedAt.smul_iff.1 (f.bdd_at_cusps' key)

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_mul_inv_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N →
    GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  intro N l d σ τ _ hσ hτ
  obtain ⟨hσc, hσd⟩ := hσ
  obtain ⟨hτc, hτd⟩ := hτ
  have detσ := Matrix.SpecialLinearGroup.det_coe σ
  have detτ := Matrix.SpecialLinearGroup.det_coe τ
  rw [Matrix.det_fin_two] at detσ detτ
  have e00 : ((τ * σ⁻¹) 0 0 : ℤ) = τ 0 0 * σ 1 1 - τ 0 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e10 : ((τ * σ⁻¹) 1 0 : ℤ) = τ 1 0 * σ 1 1 - τ 1 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e11 : ((τ * σ⁻¹) 1 1 : ℤ) = τ 1 1 * σ 0 0 - τ 1 0 * σ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσc hτc
  push_cast at hσc hτc
  have hNl : (N : ℤ) * l ∣ (τ * σ⁻¹) 1 0 := by
    rw [e10]
    exact dvd_sub (dvd_mul_of_dvd_left hτc _) (dvd_mul_of_dvd_right hσc _)
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hσc)
  have hτN : ((τ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hτc)
  have dσ : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - (σ 0 1 : ℤ) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detσ
  have dτ : ((τ 0 0 : ℤ) : ZMod N) * (τ 1 1 : ℤ) - (τ 0 1 : ℤ) * (τ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detτ
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; push_cast
      linear_combination (τ 0 0 : ZMod N) * hσd - (τ 0 0 : ZMod N) * hτd + dτ
        + (τ 0 1 : ZMod N) * hτN - (τ 0 1 : ZMod N) * hσN
    · rw [e11]; push_cast
      linear_combination (σ 0 0 : ZMod N) * hτd - (σ 0 0 : ZMod N) * hσd + dσ
        + (σ 0 1 : ZMod N) * hσN - (σ 0 1 : ZMod N) * hτN
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hNl)
  · rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) hNl)

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_conj_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), IsDia N l d σ → γ ∈ lev N l →
    σ * γ * σ⁻¹ ∈ lev N l := by
  intro N l d σ γ hσ hγ
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hσN : σ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_right N l)) hc)
  have hσl : σ ∈ Gamma0 l := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_left l N)) hc)
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  refine Subgroup.mem_inf.2
    ⟨?_, (Gamma0 l).mul_mem ((Gamma0 l).mul_mem hσl hγ0) ((Gamma0 l).inv_mem hσl)⟩
  have hγN : γ ∈ Gamma0 N := ((Gamma1_mem N γ).1 hγ1).2.2
  set S : Gamma0 N := ⟨σ, hσN⟩
  set G : Gamma0 N := ⟨γ, hγN⟩
  have hG : G ∈ Gamma1' N := (Gamma1_to_Gamma0_mem G).2 ((Gamma1_mem N γ).1 hγ1)
  have hX : S * G * S⁻¹ ∈ Gamma1' N := by
    rw [Gamma1_mem'] at hG ⊢
    rw [map_mul, map_mul, hG, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have h := (Gamma1_to_Gamma0_mem _).1 hX
  exact (Gamma1_mem N _).2 h

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

open ConjAct Pointwise

namespace GlobalTheory.Hk

theorem conj_entries (σ y : SL(2, ℤ)) :
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 0 0 = (σ 0 0 * y 0 0 + σ 0 1 * y 1 0) * σ 1 1 - (σ 0 0 * y 0 1 + σ 0 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 0 = (σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 1 1 - (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 1 = -(σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 0 1 + (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 0 0) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  refine ⟨by ring, by ring, by ring⟩

theorem dia_conj_mem {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {y : SL(2, ℤ)}
    (hy : y ∈ lev N l) : σ * y * σ⁻¹ ∈ lev N l := by
  obtain ⟨hy1, hy0⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hc, -⟩ := hσ
  rw [Gamma1_mem] at hy1
  rw [Gamma0_mem] at hy0
  obtain ⟨hp, hs, hr⟩ := hy1
  obtain ⟨e00, e10, e11⟩ := conj_entries σ y
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (σ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
  have hcN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdvd)
  have hcl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd)
  have hdet : (σ 0 0 : ℤ) * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdetN : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - ((σ 0 1 : ℤ) : ZMod N) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem, e00, e10, e11]
    push_cast
    rw [hp, hs, hr, hcN]
    rw [hcN] at hdetN
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetN
  · rw [Gamma0_mem, e10]
    push_cast
    rw [hy0, hcl]
    ring

theorem lev_le_conj {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) :
    (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ • (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]
  exact Subgroup.mem_map.2 ⟨σ * y * σ⁻¹, dia_conj_mem hσ hy, by simp [map_mul, map_inv]⟩

theorem dia_modularForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → IsDia N l d σ →
    ∀ f : ModularForm (lev N l) k, ∃ g : ModularForm (lev N l) k, ⇑g = dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  let F := ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  have hle := lev_le_conj hσ
  refine ⟨{ toFun := ⇑F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, ?_⟩
  show ⇑F = _
  rw [ModularForm.coe_translate, dia, ModularForm.SL_slash]
  rfl

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HkInvFin

theorem sigma_dg_mul_eq : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ →
    γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      mat σ * dg q 1 * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  intro N l q σ γ hq _ hσ hγ hc
  haveI := Fact.mk hq
  have hdetγ : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * mat γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hdetσ : mat σ 0 0 * mat σ 1 1 - mat σ 0 1 * mat σ 1 0 = 1 := by
    have := σ.2; rwa [Matrix.det_fin_two] at this
  have hcq : ((mat γ 1 0 : ℤ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hdiv : (q : ℤ) ∣ mat γ 1 1 - mat γ 1 0 *
      (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_comm ((mat γ 1 1 : ℤ) : ZMod q), ← mul_assoc,
      mul_inv_cancel₀ hcq, one_mul, sub_self]
  obtain ⟨x, hx⟩ := hdiv
  set j' : ℕ := (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val with hj'
  have hjlt : j' < q := ZMod.val_lt _
  let δ : Matrix (Fin 2) (Fin 2) ℤ := !![q * mat γ 0 0, mat γ 0 1 - mat γ 0 0 * j'; mat γ 1 0, x]
  have hdetδ : δ.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdetγ - mat γ 0 0 * hx
  let γ' : SL(2, ℤ) := ⟨mat σ * δ, by rw [Matrix.det_mul, hdetδ, σ.2, one_mul]⟩
  have hlev := hγ
  rw [GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem] at hlev
  obtain ⟨⟨ha, hd, hcN⟩, hcl⟩ := hlev
  obtain ⟨hs10, hs11⟩ := hσ
  have hs10' : ((N * l : ℕ) : ℤ) ∣ mat σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hs10
  have hsN : ((mat σ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_right _ _) hs10'
  have hsl : ((mat σ 1 0 : ℤ) : ZMod l) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_left _ _) hs10'
  refine ⟨j', hjlt, γ', ?_, ?_⟩
  · have e00 : γ'.1 0 0 = mat σ 0 0 * (q * mat γ 0 0) + mat σ 0 1 * mat γ 1 0 := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have e10 : γ'.1 1 0 = mat σ 1 0 * (q * mat γ 0 0) + mat σ 1 1 * mat γ 1 0 := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have e11 : γ'.1 1 1 = mat σ 1 0 * (mat γ 0 1 - mat γ 0 0 * j') + mat σ 1 1 * x := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have hxN := congrArg (Int.cast : ℤ → ZMod N) hx
    have hdN := congrArg (Int.cast : ℤ → ZMod N) hdetσ
    have ha' : ((mat γ 0 0 : ℤ) : ZMod N) = 1 := ha
    have hd' : ((mat γ 1 1 : ℤ) : ZMod N) = 1 := hd
    have hcN' : ((mat γ 1 0 : ℤ) : ZMod N) = 0 := hcN
    have hcl' : ((mat γ 1 0 : ℤ) : ZMod l) = 0 := hcl
    have h11 : ((mat σ 1 1 : ℤ) : ZMod N) = (q : ZMod N) := by
      have : ((mat σ 1 1 : ℤ) : ZMod N) = ((q : ℤ) : ZMod N) := hs11
      simpa using this
    push_cast at hxN hdN
    rw [hd', hcN'] at hxN
    rw [hsN, h11] at hdN
    rw [GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show ((γ'.1 0 0 : ℤ) : ZMod N) = 1
      rw [e00]; push_cast; rw [ha', hcN']; linear_combination hdN
    · show ((γ'.1 1 1 : ℤ) : ZMod N) = 1
      rw [e11]; push_cast; rw [hsN, h11]; linear_combination -hxN
    · show ((γ'.1 1 0 : ℤ) : ZMod N) = 0
      rw [e10]; push_cast; rw [hsN, hcN']; ring
    · show ((γ'.1 1 0 : ℤ) : ZMod l) = 0
      rw [e10]; push_cast; rw [hsl, hcl']; ring
  · show mat σ * dg q 1 * mat γ = (mat σ * δ) * _
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, δ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hx | ring

end GlobalTheory.HkInvFin
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem upper_mul_eq_mul_diamond_diag : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ →
    j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 →
    ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  intro N l q j σ γ _ _ hσ _ hγ hdiv
  obtain ⟨t, ht⟩ := hdiv
  obtain ⟨hσ10, hσ11⟩ := hσ
  have hγ1 := (Gamma1_mem N γ).1 (Subgroup.mem_inf.1 hγ).1
  have hcl := Gamma0_mem.1 (Subgroup.mem_inf.1 hγ).2
  obtain ⟨ha, hd, hc⟩ := hγ1
  have hdγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have ht' : γ 0 0 + (j : ℤ) * γ 1 0 = q * t := ht
  have hM : Matrix.det !![t * σ 1 1 - (γ 0 1 + j * γ 1 1) * σ 1 0, (γ 0 1 + j * γ 1 1) * σ 0 0 - t * σ 0 1;
      γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0, q * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (q * t * γ 1 1 - (γ 0 1 + j * γ 1 1) * γ 1 0) * hdσ + hdγ - γ 1 1 * ht'
  have hdvd : ((N * l : ℕ) : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ10
  have h10N : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans ⟨l, by push_cast; ring⟩ hdvd)
  have h10l : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans ⟨N, by push_cast; ring⟩ hdvd)
  have hdN := congrArg (fun x : ℤ => (x : ZMod N)) hdσ
  have htN := congrArg (fun x : ℤ => (x : ZMod N)) ht'
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, h10N, hσ11, ha, hc] at hdN htN
  refine ⟨⟨_, hM⟩, Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩, ?_⟩
  · show ((t * σ 1 1 - (γ 0 1 + j * γ 1 1) * σ 1 0 : ℤ) : ZMod N) = 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, h10N, hσ11]
    linear_combination -htN
  · show ((q * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1 : ℤ) : ZMod N) = 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hc, hd]
    linear_combination hdN
  · show ((γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0 : ℤ) : ZMod N) = 0
    simp only [Int.cast_sub, Int.cast_mul, hc, h10N]
    ring
  · show ((γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0 : ℤ) : ZMod l) = 0
    simp only [Int.cast_sub, Int.cast_mul, hcl, h10l]
    ring
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ht' - q * t * hdσ
    · linear_combination -(γ 0 1 + j * γ 1 1) * hdσ
    · linear_combination -(q * γ 1 0) * hdσ
    · linear_combination -(q * γ 1 1) * hdσ

end GlobalTheory.Hk
end
