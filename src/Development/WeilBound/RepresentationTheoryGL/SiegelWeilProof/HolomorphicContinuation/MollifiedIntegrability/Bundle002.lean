module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.B

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem herm_apply (y : E n) (i j : Fin n) : herm y i j = ⟨(y i j + y j i) / 2, (y i j - y j i) / 2⟩ := by
  apply Complex.ext <;> simp [herm]

theorem herm_conjTranspose (y : E n) : (herm y)ᴴ = herm y := by
  ext i j
  rw [conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext <;> simp <;> ring

def Am (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 - (Complex.I * s) • herm y

def Bm (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 + (Complex.I * s) • herm y

theorem sq_of_pm {s : ℂ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem star_of_pm {s : ℂ} (hs : s = 1 ∨ s = -1) : star s = s := by
  rcases hs with rfl | rfl <;> simp

theorem Is_sq {s : ℂ} (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rw [mul_mul_mul_comm, Complex.I_mul_I, sq_of_pm hs]
  ring

theorem Am_conjTranspose {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y)ᴴ = Bm s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, sub_neg_eq_add]

theorem Bm_conjTranspose {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y)ᴴ = Am s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, ← sub_eq_add_neg]

theorem Bm_mul_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Bm s y * Am s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel

theorem Am_mul_Bm {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Am s y * Bm s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel

theorem posDef_one_add (y : E n) : (1 + herm y * herm y).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (herm y)
  rw [herm_conjTranspose] at h
  exact Matrix.PosDef.one.add_posSemidef h

theorem det_one_add_eq (y : E n) : (1 + herm y * herm y).det = ((dP y : ℝ) : ℂ) := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  apply Complex.ext
  · simp [dP]
  · simp only [Complex.ofReal_im]
    simpa using h.2.symm

theorem dP_pos (y : E n) : 0 < dP y := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  simpa [dP] using h.1

theorem det_Bm_mul_det_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) :
    (Bm s y).det * (Am s y).det = ((dP y : ℝ) : ℂ) := by
  rw [← det_mul, Bm_mul_Am hs, det_one_add_eq]

theorem det_Am_ne {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, mul_zero] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)

theorem det_Bm_ne {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, zero_mul] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)

theorem uM_eq (s : ℂ) (y : E n) : uM s y = (Am s y)⁻¹ := rfl

theorem vM_eq (s : ℂ) (y : E n) : vM s y = (Bm s y)⁻¹ := rfl

theorem star_dot_self (v : Fin n → ℂ) : (star v ⬝ᵥ v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Complex.conj_mul' (v i)

theorem norm_sq_ge {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y) (x : Fin n → ℂ) :
    ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ x) i‖ ^ 2 := by
  have key : ((∑ i, ‖(M *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) + ((∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← star_dot_self (M *ᵥ x), ← star_dot_self x, ← star_dot_self (herm y *ᵥ x)]
    simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hM, herm_conjTranspose, add_mulVec, one_mulVec,
      dotProduct_add]
  have key' : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 + ∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 := by
    exact_mod_cast key
  rw [key']
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => by positivity)

theorem norm_entry_le {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y)
    (hd : M.det ≠ 0) (a b : Fin n) : ‖M⁻¹ a b‖ ≤ 1 := by
  have hMx : M *ᵥ (M⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  have h1 := norm_sq_ge y hM (M⁻¹ *ᵥ Pi.single b 1)
  rw [hMx] at h1
  have hsum1 : ∑ i, ‖(Pi.single b (1 : ℂ) : Fin n → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hxa : (M⁻¹ *ᵥ Pi.single b 1) a = M⁻¹ a b := by
    simp [mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖M⁻¹ a b‖ ^ 2 ≤ 1 := by
    rw [← hxa, ← hsum1]
    refine le_trans ?_ h1
    exact Finset.single_le_sum (f := fun i => ‖(M⁻¹ *ᵥ Pi.single b 1) i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ a)
  nlinarith [norm_nonneg (M⁻¹ a b)]

theorem norm_uM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖uM s y a b‖ ≤ 1 := by
  rw [uM_eq]
  exact norm_entry_le y (by rw [Am_conjTranspose hs, Bm_mul_Am hs]) (det_Am_ne hs y) a b

theorem norm_vM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖vM s y a b‖ ≤ 1 := by
  rw [vM_eq]
  exact norm_entry_le y (by rw [Bm_conjTranspose hs, Am_mul_Bm hs]) (det_Bm_ne hs y) a b

theorem norm_det_Am_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Am s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Am_conjTranspose hs, det_conjTranspose] at h
  have h2 : star (Am s y).det * (Am s y).det = ((‖(Am s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h

theorem norm_det_Bm_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Bm s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Bm_conjTranspose hs, det_conjTranspose, mul_comm] at h
  have h2 : star (Bm s y).det * (Bm s y).det = ((‖(Bm s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h

theorem norm_det_uM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(uM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [uM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Am_sq hs]

theorem norm_det_vM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(vM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [vM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Bm_sq hs]

theorem norm_det_pow {x : ℂ} {d : ℝ} (hd : 0 < d) (h : ‖x‖ ^ 2 = d⁻¹) (p : ℕ) : ‖x ^ p‖ = d ^ (-(p : ℝ) / 2) := by
  have h1 : (d ^ (-(1 : ℝ) / 2)) ^ 2 = d⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
    exact Real.rpow_neg_one d
  have h2 : 0 ≤ d ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hd.le _
  have hx : ‖x‖ = d ^ (-(1 : ℝ) / 2) := (pow_left_inj₀ (norm_nonneg _) h2 two_ne_zero).mp (h.trans h1.symm)
  rw [norm_pow, hx, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  congr 1
  ring

end PositivityTheory.Rg.Sw.WR.B
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  exact Complex.continuous_re.comp ((continuous_const.add (continuous_herm.matrix_mul continuous_herm)).matrix_det)

theorem continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := by
  unfold chr
  fun_prop

theorem norm_chr (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  unfold chr
  rw [Complex.norm_exp]
  simp

theorem abs_log_le (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) : |Real.log x| ≤ (x ^ δ + x ^ (-δ)) / δ := by
  have h1 : δ * Real.log x ≤ x ^ δ := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
    linarith
  have h2 : -δ * Real.log x ≤ x ^ (-δ) := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-δ))
    linarith
  have p1 := Real.rpow_pos_of_pos hx δ
  have p2 := Real.rpow_pos_of_pos hx (-δ)
  rcases abs_cases (Real.log x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, le_div_iff₀ hδ] <;> nlinarith

theorem rpow_neg_le_add (x a a0 d : ℝ) (hx : 0 < x) (ha : |a - a0| ≤ d) :
    x ^ (-a) ≤ x ^ (-(a0 - d)) + x ^ (-(a0 + d)) := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  have p1 := Real.rpow_pos_of_pos hx (-(a0 - d))
  have p2 := Real.rpow_pos_of_pos hx (-(a0 + d))
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-a) ≤ x ^ (-(a0 - d)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith
  · have : x ^ (-a) ≤ x ^ (-(a0 + d)) := Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith)
    linarith

theorem rp3 {x : ℝ} (hx : 0 < x) (a b c : ℝ) : x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [Real.rpow_add hx, Real.rpow_add hx]

theorem dP_pos (hI : Integr) (y : E n) : 0 < dP y := by
  obtain ⟨⟨c0, hc0, hc0le⟩, -⟩ := hI n
  exact lt_of_lt_of_le (mul_pos hc0 (by positivity)) (hc0le y)

theorem norm_term (hI : Integr) (t : ℝ) (β : E n) (h : E n → ℂ) (z : ℂ) (y : E n) :
    ‖((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y‖ = dP y ^ (-z.re) * ‖h y‖ := by
  rw [norm_mul, norm_mul, norm_chr, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (dP_pos hI y), Complex.neg_re]

theorem continuous_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (z : ℂ) :
    Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
  have : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) :=
    (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
  exact (this.mul hh).mul (continuous_chr t β)

theorem integ_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) {κ C : ℝ}
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) {z : ℂ} (hz : (n : ℝ) ^ 2 / 2 < z.re + κ) :
    Integrable fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  obtain ⟨-, hint⟩ := hI n
  refine Integrable.mono' ((hint (z.re + κ) hz).const_mul C) (continuous_term hI t β hh z).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [norm_term hI]
  have hp := dP_pos hI y
  calc dP y ^ (-z.re) * ‖h y‖ ≤ dP y ^ (-z.re) * (C * dP y ^ (-κ)) :=
        mul_le_mul_of_nonneg_left (hb y) (Real.rpow_nonneg hp.le _)
    _ = C * dP y ^ (-(z.re + κ)) := by
        rw [neg_add, Real.rpow_add hp]; ring

theorem holo (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (κ C : ℝ)
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y)
      {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + κ} := by
  obtain ⟨-, hint⟩ := hI n
  intro z0 hz0
  simp only [Set.mem_ofPred_eq] at hz0
  set σs := z0.re + κ with hσs
  set δ := (σs - (n : ℝ) ^ 2 / 2) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hb' : ∀ y, ‖h y‖ ≤ C' * dP y ^ (-κ) := fun y =>
    (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (dP_pos hI y).le _))
  let F : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y
  let F' : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
  have hF'c : Continuous (F' z0) := by
    have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
    have h1 : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z0) :=
      (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
    have h2 : Continuous fun y : E n => ((Real.log (dP y) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_dP.log fun y => (dP_pos hI y).ne')
    exact ((h1.mul h2.neg).mul hh).mul (continuous_chr t β)
  let B : E n → ℝ := fun y => C' / δ * 2 * (dP y ^ (-(σs - 2 * δ)) + dP y ^ (-(σs + 2 * δ)))
  have hBint : Integrable B := by
    refine ((hint _ ?_).add (hint _ ?_)).const_mul (C' / δ * 2)
    · rw [hδ]; linarith
    · rw [hδ]; linarith
  have hbound : ∀ y, ∀ z ∈ Metric.ball z0 δ, ‖F' z y‖ ≤ B y := by
    intro y z hz
    have hp := dP_pos hI y
    have hre : |z.re - z0.re| < δ := by
      have := Complex.abs_re_le_norm (z - z0)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hz)
    have hn : ‖F' z y‖ = dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖ := by
      simp only [F', norm_mul, norm_neg, norm_chr, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
    rw [hn]
    have e1 := abs_log_le (dP y) δ hp hδpos
    have e2 := hb' y
    have q1 : dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ - δ)) := by
      rw [rp3 hp]; congr 1; ring
    have q2 : dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ + δ)) := by
      rw [rp3 hp]; congr 1; ring
    have r1 := rpow_neg_le_add (dP y) (z.re + κ - δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have r2 := rpow_neg_le_add (dP y) (z.re + κ + δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have a0 := Real.rpow_nonneg hp.le (-z.re)
    have a1 := Real.rpow_nonneg hp.le δ
    have a2 := Real.rpow_nonneg hp.le (-δ)
    have a3 := Real.rpow_nonneg hp.le (-κ)
    calc dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖
        ≤ dP y ^ (-z.re) * ((dP y ^ δ + dP y ^ (-δ)) / δ) * (C' * dP y ^ (-κ)) := by
          gcongr
      _ = C' / δ * (dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) + dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ)) := by
          ring
      _ = C' / δ * (dP y ^ (-(z.re + κ - δ)) + dP y ^ (-(z.re + κ + δ))) := by rw [q1, q2]
      _ ≤ B y := by
          have : 0 ≤ C' / δ := div_nonneg hC'0 hδpos.le
          simp only [B]
          nlinarith
  have hdiff : ∀ y, ∀ z ∈ Metric.ball z0 δ, HasDerivAt (fun w => F w y) (F' z y) z := by
    intro y z _
    have hp := dP_pos hI y
    have hx : ((dP y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have h1 : HasDerivAt (fun w : ℂ => ((dP y : ℝ) : ℂ) ^ (-w))
        (((dP y : ℝ) : ℂ) ^ (-z) * Complex.log ((dP y : ℝ) : ℂ) * (-1)) z :=
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl hx)).hasDerivAt).comp z (hasDerivAt_neg z)
    have h2 := (h1.mul_const (h y)).mul_const (chr t β y)
    refine h2.congr_deriv ?_
    show _ = ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
    rw [Complex.ofReal_log hp.le]
    ring
  have hF0 : Integrable (F z0) := integ_term hI t β hh hb' hz0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (x₀ := z0)
    (Metric.ball_mem_nhds z0 hδpos)
    (Eventually.of_forall fun z => (continuous_term hI t β hh z).aestronglyMeasurable) hF0
    hF'c.aestronglyMeasurable (ae_of_all _ hbound) hBint (ae_of_all _ hdiff)
  exact key.2.differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.WR.T
end
end

section

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * star (x a i) * x a j := by

  simp only [gramX, Qp, Qb, map_sub, map_sum, map_mul, evX, eval_X, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
  rw [this]; ring

theorem trace_im_zero (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : (b * gramX ε x).trace.im = 0 := by
  have h : star (b * gramX ε x).trace = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, gramX_herm, hb.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem norm_exp_tr (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h := trace_im_zero ε b hb x
  simp [Complex.mul_re, h]

def phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  -∑ a, ∑ k, ∑ j, C ((Amat ε c t b a) k j) * X (a, k, true) * X (a, j, false)

theorem evX_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (phiP ε c t b) x = -∑ a, ∑ k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j := by
  simp [phiP, evX]

theorem exp_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) = Complex.exp (evX (phiP ε c t b) x) := by
  rw [gs, ← Complex.exp_add, evX_phiP]
  congr 1
  have h1 : (((c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)) : ℂ) = ∑ a, ∑ k, (c : ℂ) * (star (x a k) * x a k) := by
    push_cast
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    have hz : (starRingEnd ℂ) (x a k) * x a k = ((‖x a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.star_def, hz]; push_cast; ring
  have h2 : (b * gramX ε x).trace = ∑ a, ∑ k, ∑ j, sgn ε a * b j k * star (x a k) * x a j := by
    simp only [trace, diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∀ a k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j =
      (c : ℂ) * (star (x a k) * x a k) - ∑ j, Complex.I * t * (sgn ε a * b j k * star (x a k) * x a j) := by
    intro a k
    simp only [Amat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_eq, mul_assoc]
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [h1, h2]
  simp only [h3, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end PositivityTheory.Rg.Sw.WR.G
end
end
