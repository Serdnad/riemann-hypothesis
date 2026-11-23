module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDiagonalAlt

def diagEnergy {e : ℕ} (l : Fin (e + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (e + 1),
    chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k

theorem diag_posDef {e : ℕ} {l : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) :
    (Matrix.diagonal fun j => (l j : ℂ)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by simpa using hl j

theorem diag_congr {e : ℕ} (s d : Fin (e + 1) → ℝ) :
    (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (d j : ℂ)) *
        Matrix.diagonal (fun j => (s j : ℂ)) =
      Matrix.diagonal fun j => ((s j * d j * s j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem diagEnergy_mul (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {l l' : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) (hl' : ∀ j, 0 < l' j) :
    diagEnergy (l * l') = diagEnergy l + diagEnergy l' := by
  have hll' : ∀ j, 0 < (l * l') j := fun j => mul_pos (hl j) (hl' j)
  set s : Fin (e + 1) → ℝ := fun j => (Real.sqrt (l' j))⁻¹ with hs
  have hss : ∀ j, s j * s j * l' j = 1 := fun j => by
    simp only [hs]
    rw [← mul_inv, Real.mul_self_sqrt (hl' j).le, inv_mul_cancel₀ (hl' j).ne']
  have hsd : (Matrix.diagonal fun j => (s j : ℂ)).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have : (Real.sqrt (l' j)) ≠ 0 := (Real.sqrt_pos.mpr (hl' j)).ne'
    simpa [hs] using this
  have h1 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => ((l * l') j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = Matrix.diagonal fun j => (l j : ℂ) := by
    rw [diag_congr]
    congr 1
    funext j
    congr 1
    simp only [Pi.mul_apply]
    linear_combination (l j) * hss j
  have h2 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (l' j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = 1 := by
    rw [diag_congr, ← diagonal_one]
    congr 1
    funext j
    rw [show s j * l' j * s j = 1 by linarith [hss j]]
    simp
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => ((l * l') j : ℂ))
      (Matrix.diagonal fun j => (l' j : ℂ)) k = chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ _ (diag_posDef hll') (diag_posDef hl') hsd k, h1, h2]
  unfold diagEnergy
  rw [hC e _ (Matrix.diagonal fun j => (l' j : ℂ)) 1 (diag_posDef hll') (diag_posDef hl') PosDef.one,
    Finset.sum_congr rfl fun k _ => hterm k]

theorem diagEnergy_perm (hI : ChartEnergyLinearInvariant.Statement) {e : ℕ} {l : Fin (e + 1) → ℝ}
    (hl : ∀ j, 0 < l j) (σ : Equiv.Perm (Fin (e + 1))) : diagEnergy (l ∘ σ) = diagEnergy l := by
  set C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := σ.symm.toPEquiv.toMatrix with hCdef
  have hCH : Cᴴ = σ.toPEquiv.toMatrix := by
    ext i j
    rw [hCdef, conjTranspose_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.symm_apply_eq]
    by_cases h : σ i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hconj : ∀ A : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, Cᴴ * A * C = A.submatrix σ σ := by
    intro A
    rw [hCH, PEquiv.toMatrix_toPEquiv_mul, hCdef, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
    rfl
  have hCd : C.det ≠ 0 := by
    rw [hCdef, show (σ.symm.toPEquiv.toMatrix : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      Equiv.Perm.permMatrix ℂ σ.symm from rfl, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k =
      chartMixedEnergy (Matrix.diagonal fun j => ((l ∘ σ) j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ C (diag_posDef hl) PosDef.one hCd k, hconj, hconj, submatrix_diagonal_equiv,
      submatrix_one_equiv]
    rfl
  unfold diagEnergy
  exact (Finset.sum_congr rfl fun k _ => hterm k).symm

theorem cxHessian_add_const {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (κ : ℝ) :
    cxHessian (fun y => φ y + κ) = cxHessian φ := by
  have h : fderiv ℝ (fun y => φ y + κ) = fderiv ℝ φ := funext fun x => fderiv_add_const κ
  funext z
  unfold cxHessian
  simp only [h]
  rfl

theorem maDensity_congr {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (h : ∀ j, cxHessian (φ j) = cxHessian (ψ j))
    (z : Fin D → ℂ) : maDensity φ z = maDensity ψ z := by
  unfold maDensity
  simp only [h]

theorem hermChartPot_const {e : ℕ} {c : ℝ} (hc : 0 < c) (y : Fin e → ℂ) :
    hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) y =
      hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c := by
  set v : Fin (e + 1) → ℂ := Fin.cons 1 y with hv
  have hv0 : v ≠ 0 := fun h => by
    have := congr_fun h 0
    simp [hv] at this
  have hx : 0 < (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re :=
    PosDef.one.re_dotProduct_pos hv0
  have hq : (star v ⬝ᵥ ((Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) *ᵥ v)).re =
      c * (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re := by
    rw [← smul_one_eq_diagonal, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  unfold hermChartPot
  rw [← hv, hq, Real.sqrt_mul hc.le, Real.log_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hx).ne',
    Real.log_sqrt hc.le]
  ring

theorem diagEnergy_const {e : ℕ} {c : ℝ} (hc : 0 < c) :
    diagEnergy (fun _ : Fin (e + 1) => c) =
      (e + 1) * (1 / 2 * Real.log c) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have hpot : hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) =
      fun y => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c :=
    funext (hermChartPot_const hc)
  have hk : ∀ k, chartMixedEnergy (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) 1 k =
      1 / 2 * Real.log c * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
    intro k
    have hd : ∀ y, maDensity (fun j : Fin e => if (j : ℕ) < k then
        hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ))
        else hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y =
        maDensity (fun _ : Fin e => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y := by
      refine maDensity_congr _ _ fun j => ?_
      split_ifs
      · rw [hpot, cxHessian_add_const]
      · rfl
    unfold chartMixedEnergy chartMass
    simp_rw [hd]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [hpot]
    ring
  unfold diagEnergy
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem diagEnergy_one {e : ℕ} : diagEnergy (1 : Fin (e + 1) → ℝ) = 0 := by
  calc diagEnergy (1 : Fin (e + 1) → ℝ) = diagEnergy (fun _ : Fin (e + 1) => (1 : ℝ)) := rfl
    _ = 0 := by rw [diagEnergy_const one_pos, Real.log_one]; ring

theorem diagEnergy_prod (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Fin (e + 1) → ℝ) (hf : ∀ t j, 0 < f t j) :
    diagEnergy (∏ t ∈ s, f t) = ∑ t ∈ s, diagEnergy (f t) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact diagEnergy_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      diagEnergy_mul hI hC (hf a) (fun j => by rw [Finset.prod_apply]; exact Finset.prod_pos fun t _ => hf t j),
      ih]

end ChartEnergyDiagonalAlt


open ChartEnergyDiagonalAlt in
theorem ChartEnergyDiagonal.proof (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement) :
    ChartEnergyDiagonal.Statement := by
  intro e l hl
  change diagEnergy l = _
  set f : Fin (e + 1) → Fin (e + 1) → ℝ := fun t => l ∘ (Equiv.addRight t) with hf
  have hfpos : ∀ t j, 0 < f t j := fun t j => hl _
  have hprod : (∏ t, f t) = fun _ => ∏ j, l j := by
    funext i
    rw [Finset.prod_apply]
    exact Equiv.prod_comp (Equiv.addLeft i) l
  have key := diagEnergy_prod hI hC Finset.univ f hfpos
  rw [hprod, diagEnergy_const (Finset.prod_pos fun j _ => hl j),
    Finset.sum_congr rfl fun t _ => diagEnergy_perm hI hl (Equiv.addRight t), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.log_prod (fun j _ => (hl j).ne')] at key
  push_cast at key
  have he : (0 : ℝ) < e + 1 := by positivity
  have h2 : ((e : ℝ) + 1) * (diagEnergy l - 1 / 2 * (∑ j, Real.log (l j)) *
      chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) = 0 := by
    linear_combination -key
  have := (mul_eq_zero.mp h2).resolve_left he.ne'
  linarith

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyInvariance

open ChartMongeAmpereAffineInvariance

def EnergyInvariantUnder {e : ℕ} (C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : Prop :=
  ∀ M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k

variable {e : ℕ}

theorem posDef_conj {M C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hC : C.det ≠ 0) :
    (Cᴴ * M * C).PosDef :=
  hM.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)))

theorem conj_mul (M A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    (A * B)ᴴ * M * (A * B) = Bᴴ * (Aᴴ * M * A) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem invariantUnder_mul {A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hA : EnergyInvariantUnder A)
    (hB : EnergyInvariantUnder B) (hAdet : A.det ≠ 0) : EnergyInvariantUnder (A * B) := by
  intro M N hM hN k
  rw [conj_mul, conj_mul, hB _ _ (posDef_conj hM hAdet) (posDef_conj hN hAdet), hA M N hM hN]

theorem invariantUnder_of_mul_right {C V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hCV : EnergyInvariantUnder (C * V)) (hV : EnergyInvariantUnder V) (hC : C.det ≠ 0) :
    EnergyInvariantUnder C := by
  intro M N hM hN k
  rw [← hV _ _ (posDef_conj hM hC) (posDef_conj hN hC), ← conj_mul, ← conj_mul, hCV M N hM hN]

theorem maDensity_comp_affine_family {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j => fun y => φ j (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity φ (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hH : ∀ j, cxHessian (fun y => φ j (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian (φ j) (c + P *ᵥ z) * P.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_affine (φ j) c P hP κ z
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun j => cxHessian (φ j) (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem invariantUnder_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (hdet : T.det ≠ 0) : EnergyInvariantUnder T := by
  intro M N hM hN k
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set P := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hPdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hP : P.det ≠ 0 := by
    rw [hPdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfM : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  have hfN : hermChartPot (Tᴴ * N * T) = fun y => hermChartPot N (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj N T hN hT ht)
  set Φ : Fin e → (Fin e → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  have hfam : (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) =
      fun j => fun y => Φ j (c + P *ᵥ y) + Real.log ‖T 0 0‖ := by
    funext j y
    by_cases h : (j : ℕ) < k <;> simp [hΦ, h, hfM, hfN]
  set f : (Fin e → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y, (hermChartPot (Tᴴ * M * T) y - hermChartPot (Tᴴ * N * T) y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) y =
      Complex.normSq P.det * f (c + P *ᵥ y) := fun y => by
    rw [hfam, maDensity_comp_affine_family Φ c P hP, hfM, hfN, hf]
    ring
  unfold chartMixedEnergy
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_affine f c P hP, ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hP).ne', one_mul]

theorem invariantUnder_of_row_one (hS : ChartEnergySwapInvariant.Statement)
    (C : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hC : C.det ≠ 0) (h1 : C 0 1 ≠ 0) :
    EnergyInvariantUnder C := by
  have h01 : (0 : Fin (e + 1 + 1)) ≠ 1 := by simp
  set S : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := swapFirstTwo e with hSdef
  have hSinv : EnergyInvariantUnder S := fun M N hM hN k => hS e M N hM hN k
  have hSdet : S.det ≠ 0 := by
    rw [hSdef, swapFirstTwo, det_permutation, Equiv.Perm.sign_swap h01]
    norm_num
  set T : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ).updateRow 1 (C 0) with hTdef
  have hT0 : ∀ j : Fin (e + 1), T 0 j.succ = 0 := fun j => by
    rw [hTdef, updateRow_ne h01, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hTdet : T.det = C 0 1 := by
    have hrow : ∑ m, C 0 m • (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) m = C 0 := by
      funext p
      simp [Finset.sum_apply, Matrix.one_apply]
    have h := det_updateRow_sum (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) 1 (C 0)
    rw [hrow] at h
    simpa using h
  have hTdet' : T.det ≠ 0 := by rw [hTdet]; exact h1
  have hST0 : ∀ m, C 0 m = (S * T) 0 m := fun m => by
    rw [hSdef, swapFirstTwo, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, Equiv.swap_apply_left, id, hTdef,
      updateRow_self]
  have hSTdet : (S * T).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hSdet hTdet'
  have hU : IsUnit (S * T).det := isUnit_iff_ne_zero.mpr hSTdet
  set A := C * (S * T)⁻¹ with hAdef
  have hCA : C = A * (S * T) := by rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]
  have hA0 : ∀ j : Fin (e + 1), A 0 j.succ = 0 := fun j => by
    rw [hAdef, Matrix.mul_apply]
    simp_rw [hST0]
    rw [← Matrix.mul_apply, mul_nonsing_inv _ hU, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hAdet : A.det ≠ 0 := fun h => hC (by rw [hCA, det_mul, h, zero_mul])
  have h := invariantUnder_mul (invariantUnder_of_row_zero A hA0 hAdet)
    (invariantUnder_mul hSinv (invariantUnder_of_row_zero T hT0 hTdet') hSdet) hAdet
  rwa [← hCA] at h

end ChartEnergyInvariance


open ChartEnergyInvariance in
theorem ChartEnergyLinearInvariant.proof (hS : ChartEnergySwapInvariant.Statement) :
    ChartEnergyLinearInvariant.Statement := by
  intro e M N C hM hN hC k
  by_cases hrow : ∀ j : Fin e, C 0 j.succ = 0
  · exact invariantUnder_of_row_zero C hrow hC M N hM hN k
  · push Not at hrow
    obtain ⟨j, hj⟩ := hrow
    cases e with
    | zero => exact j.elim0
    | succ e =>
      set V : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
        (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ).permMatrix ℂ with hVdef
      have hs0 : Equiv.swap (1 : Fin (e + 1 + 1)) j.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero j).symm
      have hV0 : ∀ m : Fin (e + 1), V 0 m.succ = 0 := fun m => by
        simp [hVdef, PEquiv.toMatrix_apply, hs0, (Fin.succ_ne_zero m).symm]
      have hVdet : V.det ≠ 0 := by
        rw [hVdef, det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ)) with h | h <;>
          simp [h]
      have hCV1 : (C * V) 0 1 ≠ 0 := by
        rw [hVdef, PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, Equiv.symm_swap, Equiv.swap_apply_left, id]
        exact hj
      have hCVdet : (C * V).det ≠ 0 := by
        rw [det_mul]
        exact mul_ne_zero hC hVdet
      exact invariantUnder_of_mul_right (invariantUnder_of_row_one hS (C * V) hCVdet hCV1)
        (invariantUnder_of_row_zero V hV0 hVdet) hC M N hM hN k

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootLogNormBoundAlt

theorem norm_block_le (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    ‖WithLp.toLp 2 v‖ ≤ ‖a‖ * Real.sqrt ((1 + m : ℝ) ^ j) := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2
      = ‖a‖ ^ 2 * ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [hv, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h₃ j m Z hZ)) (norm_nonneg _)

theorem log_block (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) (hv0 : 0 < ‖WithLp.toLp 2 v‖) :
    -((j : ℝ) / 2 * Real.log (1 + m)) ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  have hb := norm_block_le h₃ j m Z hZ a v hv
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hm : (0 : ℝ) < (1 + m : ℝ) ^ j := by positivity
  have hl := Real.log_le_log hv0 hb
  rw [Real.log_mul ha'.ne' (Real.sqrt_pos.mpr hm).ne', Real.log_sqrt hm.le, Real.log_pow] at hl
  rw [Real.log_div ha'.ne' hv0.ne']
  linarith

end RootLogNormBoundAlt


open RootLogNormBoundAlt in
theorem RootLogNormBound.proof (h₁ : RootAnchorNonzero.Statement) (h₂ : RootPointConj.Statement)
    (h₃ : PlueckerKernel.Statement) : RootLogNormBound.Statement := by
  intro f j m ζ hζ z hz
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (ι := PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := h₂ f j m ζ hζ z hz τ
    exact log_block h₃ j m ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz' (hpos τ)
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e]
  calc -grassConst f j m = ∑ _τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) := by
        simp [grassConst]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

end

end GroundTheory.Heights₂.Heights
end
