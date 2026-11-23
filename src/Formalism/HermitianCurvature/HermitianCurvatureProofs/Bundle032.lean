module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Mathlib.Analysis.Fourier.FourierTransform
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle002
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle028
public import Formalism.HermitianCurvature.StatementFr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Real Complex
open scoped FourierTransform ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

theorem integral_fsv_eq_fourier (D : ℂ → ℂ) (s : ℂ) :
    ∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t = 𝓕 D (-(I * conj s) / (π : ℂ)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1
  unfold Formalism.FourierDecayAlt.P5.fsv
  congr 1
  rw [Complex.inner]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : s * t - conj s * conj t = ((2 * (s * t).im : ℝ) : ℂ) * I := by
    rw [← map_mul, Complex.sub_conj]
  rw [e1]
  congr 1
  push_cast
  have e2 : (-(I * conj s) / (π : ℂ) * conj t).re = -((s * t).im) / π := by
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [e2]
  push_cast
  field_simp

theorem smooth_bounded_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  refine fourier_smooth D m C hD fun w => ?_
  rw [Complex.finrank_real_complex]
  set s : ℂ := -(I * π * conj w) with hs
  have hw : w = -(I * conj s) / (π : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hs]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hns : ‖s‖ = π * ‖w‖ := by
    rw [hs, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have h := hdec s
  rw [integral_fsv_eq_fourier, ← hw] at h
  refine h.trans ?_
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg _).trans (hdec 0)
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have e : (-((m : ℝ) + ((2 : ℕ) : ℝ) + 1)) = -((m : ℝ) + 3) := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [hns]
  nlinarith [Real.pi_gt_three, norm_nonneg w]

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem sum_lt_castLE {j : ℕ} (hj : j ≤ n) (f : Fin n → ℂ) :
    ∑ i : Fin n, (if i.val < j then f i else 0) = ∑ b : Fin j, f (Fin.castLE hj b) := by
  rw [← Finset.sum_filter]
  have e : (Finset.univ.filter fun i : Fin n => i.val < j) = Finset.univ.map (Fin.castLEEmb hj) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩; simp
  rw [e, Finset.sum_map]
  rfl

def gram (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Zᴴ * Z

def blkJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => A (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)

def colJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Fin j → ℂ := fun a => A (Fin.castLE j.isLt.le a) j

def Wm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j =>
  if h : i.val < j.val then -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) ⟨i.val, h⟩) else if i = j then 1 else 0

theorem Wm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [Wm, Matrix.of_apply]
    rw [dif_neg (by have : j.val < i.val := h; omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h)]
  · simp [Wm]

theorem mul_col_split (A V : Matrix (Fin n) (Fin n) ℂ) (hV : V ∈ C2.UTset n) (l j : Fin n) :
    (A * V) l j = ∑ b : Fin j, A l (Fin.castLE j.isLt.le b) * V (Fin.castLE j.isLt.le b) j + A l j := by
  rw [Matrix.mul_apply, ← sum_lt_castLE j.isLt.le (fun i => A l i * V i j)]
  have hsplit : ∀ i : Fin n, A l i * V i j = (if i.val < j.val then A l i * V i j else 0) +
      (if i = j then A l j else 0) := by
    intro i
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [if_pos h, if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), add_zero]
    · have e : i = j := Fin.ext h
      subst e
      rw [if_neg (lt_irrefl _), if_pos rfl, hV.2, mul_one, zero_add]
    · rw [if_neg (by omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), hV.1 i j h, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem blk_gram_eq (Z : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    blkJ (gram Z) j = (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b))ᴴ *
      Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b) := by
  ext a b
  simp [blkJ, gram, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem blk_det_ne {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (j : Fin n) : (blkJ (gram Z) j).det ≠ 0 := by
  rw [blk_gram_eq]
  refine (Matrix.PosDef.det_pos (Matrix.PosDef.conjTranspose_mul_self _ ?_)).ne'
  intro x y hxy
  set ex : (Fin j → ℂ) → Fin n → ℂ := fun x l => if h : l.val < j.val then x ⟨l.val, h⟩ else 0 with hex
  have hm : ∀ x : Fin j → ℂ, (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b)) *ᵥ x = Z *ᵥ ex x := by
    intro x
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    set f : Fin n → ℂ := fun l => Z a l * ex x l with hf
    calc ∑ b : Fin j, Z a (Fin.castLE j.isLt.le b) * x b = ∑ b : Fin j, f (Fin.castLE j.isLt.le b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hf, hex, Fin.val_castLE, dif_pos b.isLt]
      _ = ∑ l : Fin n, (if l.val < j.val then f l else 0) := (sum_lt_castLE _ f).symm
      _ = ∑ l : Fin n, f l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases h : l.val < j.val
          · rw [if_pos h]
          · rw [if_neg h]; simp only [hf, hex, dif_neg h, mul_zero]
  rw [hm, hm] at hxy
  have hinj : Function.Injective (Z *ᵥ ·) := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr hZ))
  have := hinj hxy
  funext a
  have h2 := congrFun this (Fin.castLE j.isLt.le a)
  simp only [hex, Fin.val_castLE, dif_pos a.isLt] at h2
  exact h2

theorem Wm_spec {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (l j : Fin n) (hlj : l.val < j.val) :
    (gram Z * Wm Z) l j = 0 := by
  rw [mul_col_split _ _ (Wm_ut Z)]
  have hBc : blkJ (gram Z) j *ᵥ ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) = colJ (gram Z) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)), Matrix.one_mulVec]
  have hrow := congrFun hBc ⟨l.val, hlj⟩
  simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply] at hrow
  have hl : Fin.castLE j.isLt.le ⟨l.val, hlj⟩ = l := Fin.ext rfl
  rw [hl] at hrow
  have hW : ∀ b : Fin j, Wm Z (Fin.castLE j.isLt.le b) j =
      -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) b) := by
    intro b
    simp only [Wm, Matrix.of_apply, Fin.val_castLE, dif_pos b.isLt, Fin.eta]
  simp only [hW, mul_neg, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin j, gram Z l (Fin.castLE j.isLt.le x) * ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) x =
      gram Z l j from hrow]
  ring

theorem Wm_unique {Z V : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hV : V ∈ C2.UTset n)
    (hlow : ∀ l j : Fin n, l.val < j.val → (gram Z * V) l j = 0) : V = Wm Z := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hu : IsUnit (blkJ (gram Z) j).det := isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)
    set x : Fin j → ℂ := fun b => V (Fin.castLE j.isLt.le b) j with hx
    have hB : blkJ (gram Z) j *ᵥ x = -colJ (gram Z) j := by
      ext a
      have h0 := hlow (Fin.castLE j.isLt.le a) j (by simp [a.isLt])
      rw [mul_col_split _ _ hV] at h0
      simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply, hx, Pi.neg_apply]
      linear_combination h0
    have hx' : x = -((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) := by
      have e : x = (blkJ (gram Z) j)⁻¹ *ᵥ (blkJ (gram Z) j *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      rw [e, hB, Matrix.mulVec_neg]
    have h1 := congrFun hx' ⟨i.val, h⟩
    simp only [hx, Pi.neg_apply] at h1
    rw [show Fin.castLE j.isLt.le ⟨i.val, h⟩ = i from Fin.ext rfl] at h1
    rw [h1]
    simp only [Wm, Matrix.of_apply, dif_pos h]
  · have e : i = j := Fin.ext h
    subst e
    rw [hV.2, (Wm_ut Z).2]
  · rw [hV.1 i j h, (Wm_ut Z).1 i j h]

theorem gram_mul (Z u : Matrix (Fin n) (Fin n) ℂ) : gram (Z * u) = uᴴ * gram Z * u := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem Wm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Wm (Z * u) = u⁻¹ * Wm Z := by
  have hZu : (Z * u).det ≠ 0 := by rw [Matrix.det_mul, C2x2.ut_det hu, mul_one]; exact hZ
  refine (Wm_unique hZu (C2x2.ut_mul (C2x2.ut_inv hu) (Wm_ut Z)) ?_).symm
  intro l j hlj
  rw [gram_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ l.val
  · rw [Wm_spec hZ i j (by omega), mul_zero]
  · rw [Matrix.conjTranspose_apply, hu.1 i l (by show l.val < i.val; omega), star_zero, zero_mul]

def Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Wm Z).adjugate

theorem Sm_eq_inv (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z = (Wm Z)⁻¹ := by
  rw [Sm, Matrix.inv_def, C2x2.ut_det (Wm_ut Z), Ring.inverse_one, one_smul]

theorem Sm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z ∈ C2.UTset n := by
  rw [Sm_eq_inv]; exact C2x2.ut_inv (Wm_ut Z)

theorem Sm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Sm (Z * u) = Sm Z * u := by
  rw [Sm_eq_inv, Sm_eq_inv, Wm_mul hZ hu, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (C2x2.ut_unit hu)]

theorem Wm_mul_Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z * Sm Z = 1 := by
  rw [Sm_eq_inv]; exact Matrix.mul_nonsing_inv _ (C2x2.ut_unit (Wm_ut Z))

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Ring

end Ring

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

structure WaveHyp (L : R.LevelData A r) (st : Fr.Start A) (f fi : A) (s : ℂ) : Prop where
  f_fi : f * fi = 1
  fi_f : fi * f = 1
  star_f : star f = fi
  fn : ∀ g ∈ Fr.zfns L, Commute f g
  x : ∀ Y, Commute f (st.x Y)
  l : ∀ Y ∈ st.inv, fi * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * f =
    L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ A s

theorem mem_zfns (L : R.LevelData A r) : L.ζ ∈ Fr.zfns L ∧ L.ζi ∈ Fr.zfns L ∧ L.ζb ∈ Fr.zfns L ∧
    L.ζbi ∈ Fr.zfns L ∧ L.GG ∈ Fr.zfns L ∧ L.GGi ∈ Fr.zfns L := by
  simp [Fr.zfns]

theorem lowering_constant_sub (L : R.LevelData A r) (Y Y' : ℂ) :
    L.l0 Y - L.l0 Y' = algebraMap ℂ A (Y' - Y) * (L.ζb * L.GGi) := by
  simp only [R.LevelData.l0, map_sub, map_add (f := _)]
  noncomm_ring

theorem embed_lowering_constant (L : R.LevelData A r) (Y : ℂ) :
    (io (L.l0 Y) : SlopeTestRemainingChoices S A) = -io L.nab - ((Y + 1 / 2) • (1 : SlopeTestRemainingChoices S A)) * (io L.ζb * io L.GGi) := by
  simp only [R.LevelData.l0, io_sub', io_neg', io_mul', io_algebraMap]

theorem wti_wt (L : R.LevelData A r) : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
  have h1 : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by rw [h1]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

theorem wt_wti (L : R.LevelData A r) : L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = 1 := by
  have h2 : L.ζb * L.ζi = L.ζi * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  calc L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = L.ζ * L.ζb * (L.GGi * L.GG) * L.ζi * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζ * (L.ζb * L.ζi) * L.ζbi := by rw [L.GGi_GG, mul_one]; simp only [mul_assoc]
    _ = (L.ζ * L.ζi) * (L.ζb * L.ζbi) := by rw [h2]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζ_ζi, L.ζb_ζbi, mul_one]

theorem di_d (L : R.LevelData A r) (fr : Fr.FrameData S A) (hc : fr.ci * fr.c = 1) : fr.di L * fr.d L = 1 := by
  have h1 : (Fr.wti L : SlopeTestRemainingChoices S A) * Fr.wt L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wti_wt, io_one']
  have h2 : (Fr.wt L : SlopeTestRemainingChoices S A) * Fr.wti L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wt_wti, io_one']
  have hc' : Commute (Fr.wti L : SlopeTestRemainingChoices S A) (Fr.wt L) := by
    show _ = _; rw [h1, h2]
  have hp : (Fr.wti L : SlopeTestRemainingChoices S A) ^ fr.N * Fr.wt L ^ fr.N = 1 := by
    rw [← hc'.mul_pow, h1, one_pow]
  unfold Fr.FrameData.di Fr.FrameData.d
  calc fr.ci * Fr.wti L ^ fr.N * (Fr.wt L ^ fr.N * fr.c) = fr.ci * (Fr.wti L ^ fr.N * Fr.wt L ^ fr.N) * fr.c := by
        simp only [mul_assoc]
    _ = 1 := by rw [hp, mul_one, hc]

variable {L : R.LevelData A r} {st : Fr.Start A} {f fi : A} {s : ℂ}

theorem WaveHyp.io_fn (hW : WaveHyp L st f fi s) {g : A} (hg : g ∈ Fr.zfns L) :
    Commute (io f : SlopeTestRemainingChoices S A) (io g) :=
  commute_io_io (hW.fn g hg)

theorem WaveHyp.kap (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.kapL L) := by
  obtain ⟨-, h1, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.kapL
  exact commute_io_io (((hW.fn _ h2).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h5))

theorem WaveHyp.tz (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.tz L) := by
  obtain ⟨-, -, -, h3, -, -⟩ := mem_zfns L
  unfold Fr.tz
  exact commute_io_io ((hW.fn _ h3).smul_right _)

theorem WaveHyp.wt (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wt L) := by
  obtain ⟨h0, -, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.wt
  exact commute_io_io (((hW.fn _ h0).mul_right (hW.fn _ h2)).mul_right (hW.fn _ h5))

theorem WaveHyp.wti (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wti L) := by
  obtain ⟨-, h1, -, h3, h4, -⟩ := mem_zfns L
  unfold Fr.wti
  exact commute_io_io (((hW.fn _ h4).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h3))

theorem WaveHyp.lowering_constant_sub (hW : WaveHyp L st f fi s) (Y Y' : ℂ) : Commute f (L.l0 Y - L.l0 Y') := by
  obtain ⟨-, -, h2, -, -, h5⟩ := mem_zfns L
  rw [TwistedTransfer.lowering_constant_sub L Y Y']
  exact (Algebra.commute_algebraMap_right _ f).mul_right ((hW.fn _ h2).mul_right (hW.fn _ h5))

theorem frame_step (hW1 : f * fi = 1) (a : S) (t : ℂ) (D : M2 (SlopeTestRemainingChoices S A)) (Fw UU : SlopeTestRemainingChoices S A) (hD : FreeOf2 a D)
    (hFw : FreeOf a Fw) (hIH : Fw * (io f * UU) = io f * Fw)
    (hE : (D * lift0 (Uinv (A := A) t)).map (cj f fi) = D) :
    ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU)) = io f * (ins a D * Fw) := by
  have hcent : ∀ z : SlopeTestRemainingChoices S A, ∀ i j, Commute z ((lift0 (Uinv (A := A) t) : M2 (SlopeTestRemainingChoices S A)) i j) := by
    intro z i j
    rw [lift_unipotent_inverse]
    fin_cases i <;> fin_cases j <;> simp [commute_smul_one]
  have hUf : Commute (io f) (ins a (lift0 (Uinv (A := A) t))) :=
    Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ (Formalism.FourierDecayAlt.P.Fr4.free_io a f) (hcent _)
  have hUF : Commute Fw (ins a (lift0 (Uinv (A := A) t))) := Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ hFw (hcent _)
  have hins : ins a D * ins a (lift0 (Uinv (A := A) t)) = ins a (D * lift0 (Uinv (A := A) t)) :=
    (Formalism.FourierDecayAlt.P.Wd1.ins_mul a D _ hD).symm
  have hcj : ins a (D * lift0 (Uinv (A := A) t)) * io f = io f * ins a D := by
    have h := cj_ins (f := f) (fi := fi) a (D * lift0 (Uinv (A := A) t))
    rw [hE] at h
    calc ins a (D * lift0 (Uinv (A := A) t)) * io f
        = (io f * io fi) * ins a (D * lift0 (Uinv (A := A) t)) * io f := by rw [io_f_fi hW1, one_mul]
      _ = io f * cj f fi (ins a (D * lift0 (Uinv (A := A) t))) := by simp only [cj, mul_assoc]
      _ = io f * ins a D := by rw [h]
  calc ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU))
      = ins a D * (Fw * ((io f * ins a (lift0 (Uinv (A := A) t))) * UU)) := by simp only [mul_assoc]
    _ = ins a D * (Fw * ((ins a (lift0 (Uinv (A := A) t)) * io f) * UU)) := by rw [hUf.eq]
    _ = ins a D * ((Fw * ins a (lift0 (Uinv (A := A) t))) * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a D * ((ins a (lift0 (Uinv (A := A) t)) * Fw) * (io f * UU)) := by rw [hUF.eq]
    _ = ins a D * ins a (lift0 (Uinv (A := A) t)) * (Fw * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a (D * lift0 (Uinv (A := A) t)) * io f * Fw := by rw [hIH, hins]; simp only [mul_assoc]
    _ = io f * (ins a D * Fw) := by rw [hcj, mul_assoc]

theorem block_twist (hW1 : f * fi = 1) (hW2 : fi * f = 1) (t : ℂ) (p q g l : SlopeTestRemainingChoices S A) (hp : Commute (io f) p)
    (hq : Commute (io f) q) (hg : Commute (io f) g) (hl : Tw f fi t l) :
    ((!![p, 0; 0, q] * !![1, 0; g * l, g]) * lift0 (Uinv (A := A) t)).map (cj f fi) =
      !![p, 0; 0, q] * !![1, 0; g * l, g] := by
  rw [lift_unipotent_inverse]
  simp only [Matrix.mul_fin_two, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · simp [cj_of_comm hW2 hp]
  · simp [cj_zero]
  · simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.zero_eta]
    unfold Tw at hl
    rw [cj_add, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_of_comm hW2 hq, cj_of_comm hW2 hg, hl,
      cj_of_comm hW2 (commute_smul_one t _), mul_sub, mul_sub, mul_assoc q g, sub_add_cancel]
  · simp [cj_of_comm hW2 (hq.mul_right hg)]

end Frame

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
end
end
