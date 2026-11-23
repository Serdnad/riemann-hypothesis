module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.VolumeUnivFinZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle002
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
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private lemma rho_den (t : ℝ) : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (by positivity)

private theorem norm_rho (t : ℝ) : ‖rho t‖ = 1 := by
  have h2 : ‖(1 + (t : ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hd : ‖((1 + t ^ 2 : ℝ) : ℂ)‖ = 1 + t ^ 2 := by
    exact Complex.norm_of_nonneg (by positivity)
  unfold rho
  rw [norm_div, norm_pow, h2, hd, div_self (by positivity)]

private theorem rho_mul_star (t : ℝ) : rho t * star (rho t) = 1 := by
  have h := norm_rho t
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp

private theorem rho_mp (t : ℝ) : MeasurePreserving (fun z : ℂ => rho t * z) volume volume := by
  have h1 := rho_mul_star t
  have h1' : star (rho t) * rho t = 1 := by rw [mul_comm]; exact h1
  have hn := norm_rho t
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => rho t * z
      invFun := fun z => star (rho t) * z
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun r x => by
        exact mul_smul_comm r (rho t) x
      left_inv := fun z => by
        show star (rho t) * (rho t * z) = z
        rw [← mul_assoc, h1', one_mul]
      right_inv := fun z => by
        show rho t * (star (rho t) * z) = z
        rw [← mul_assoc, h1, one_mul]
      norm_map' := fun z => by
        show ‖rho t * z‖ = ‖z‖
        rw [norm_mul, hn, one_mul] }
  exact e.measurePreserving

theorem rot_mp {p m : ℕ} (t : ℝ) : MeasurePreserving (rot (p := p) (m := m) t) volume volume := by
  have h0 := rho_mp t
  have hp : ∀ n : ℕ, MeasurePreserving (fun (v : Fin n → ℂ) (j : Fin n) => rho t * v j) volume volume := by
    intro n
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => h0)
  have h := (hp p).prod ((hp p).prod ((hp m).prod (MeasurePreserving.id (volume : Measure ℝ))))
  exact h

private theorem continuous_rho_tail_integrals : Continuous rho := by
  unfold rho
  exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2).div
    (Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))) rho_den

theorem rot_meas {p m : ℕ} : Measurable (fun q : ℝ × Xp p m => rot q.1 q.2) := by
  have hu : Continuous rho := continuous_rho_tail_integrals
  have hc : Continuous (fun q : ℝ × ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => rot q.1 q.2) := by
    unfold rot
    fun_prop
  exact hc.measurable

theorem de_rot {p m : ℕ} (t : ℝ) (x : Xp p m) (l : Fin (p + 1)) : de (rot t x) l = de x l := by
  have hn : ∀ z : ℂ, ‖rho t * z‖ = ‖z‖ := fun z => by rw [norm_mul, norm_rho, one_mul]
  have hc : ∀ a b : ℂ, rho t * a * star (rho t * b) = a * star b := by
    intro a b
    rw [star_mul']
    linear_combination (a * star b) * rho_mul_star t
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.de, ReciprocityTheory.ChartRestriction.DS.Xi.Lsq, ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq, ReciprocityTheory.ChartRestriction.DS.Xi.bco, rot, hn, hc]

theorem linF_rot {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (t : ℝ) (x : Xp p m) :
    linF η η' ζ (rot t x) = rho t * linF η η' ζ x := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.linF, rot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

private lemma key (t c₀ : ℝ) (X : ℂ) : 2 * (rho t * X).im + c₀ =
    ((2 * X.im + c₀) + 4 * X.re * t + (c₀ - 2 * X.im) * t ^ 2) / (1 + t ^ 2) := by
  have hd : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have key : rho t * ((1 + t ^ 2 : ℝ) : ℂ) = (1 + t * Complex.I) ^ 2 := by
    unfold rho
    exact div_mul_cancel₀ _ (rho_den t)
  have hre : (rho t).re = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.re key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  have him : (rho t).im = (2 * t) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.im key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  rw [Complex.mul_im, hre, him]
  field_simp
  ring

private theorem rpow_neg_le_rpow_neg_of_pos_of_le {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 ≤ δ) : y ^ (-δ) ≤ x ^ (-δ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  have ha : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  have hb : x ^ δ ≤ y ^ δ := Real.rpow_le_rpow hx.le hxy hδ
  exact inv_anti₀ ha hb

private theorem complex_norm_le_abs_re_add_abs_im (X : ℂ) : ‖X‖ ≤ |X.re| + |X.im| := by
  calc ‖X‖ = ‖(X.re : ℂ) + X.im * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(X.re : ℂ)‖ + ‖(X.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |X.re| + |X.im| := by simp

private theorem complex_norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simp

theorem rot_weight (hS : SUB) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℂ) (c₀ : ℝ),
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal (C * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
  obtain ⟨C₁, hC₁⟩ := hS δ hδ0 hδ1
  set K : ℝ := (5 : ℝ)⁻¹ ^ (-δ) with hKdef
  have hK : 0 < K := by positivity
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K * max C₁ 1, mul_pos hK hM, fun X c₀ => ?_⟩
  set A : ℝ := 2 * X.im + c₀ with hA
  set B : ℝ := 4 * X.re with hB
  set D : ℝ := c₀ - 2 * X.im with hD
  set c : Fin 3 → ℂ := ![(A : ℂ), (B : ℂ), (D : ℂ)] with hc
  have c0 : c 0 = (A : ℂ) := rfl
  have c1 : c 1 = (B : ℂ) := rfl
  have c2 : c 2 = (D : ℂ) := rfl
  set N : ℝ := ‖c‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hAN : |A| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c0]; exact norm_le_pi_norm c 0
  have hBN : |B| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c1]; exact norm_le_pi_norm c 1
  have hDN : |D| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c2]; exact norm_le_pi_norm c 2
  have hc₀ : |c₀| ≤ N := by
    rw [abs_le] at hAN hDN ⊢
    constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
  have hX : ‖X‖ ≤ N := by
    have h1 := complex_norm_le_abs_re_add_abs_im X
    have hre : |X.re| ≤ N / 4 := by
      rw [abs_le] at hBN ⊢; constructor <;> linarith [hBN.1, hBN.2]
    have him : |X.im| ≤ N / 2 := by
      rw [abs_le] at hAN hDN ⊢; constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
    linarith
  have hpt : ∀ t ∈ Icc (1 : ℝ) 2,
      ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    intro t ht
    rw [← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    have hq : c 0 + c 1 * t + c 2 * t ^ 2 = ((A + B * t + D * t ^ 2 : ℝ) : ℂ) := by
      rw [c0, c1, c2]; push_cast; ring
    rw [hq, complex_norm_ofReal_eq_abs, key]
    set q : ℝ := A + B * t + D * t ^ 2 with hqdef
    have hdpos : 0 < 1 + t ^ 2 := by positivity
    have hd5 : 1 + t ^ 2 ≤ 5 := by nlinarith [ht.1, ht.2]
    rw [hKdef, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) _ hδ0.le
    rw [abs_div, abs_of_pos hdpos]
    have hw0 : 0 ≤ |q| / (1 + t ^ 2) := div_nonneg (abs_nonneg _) hdpos.le
    have hwd : |q| / (1 + t ^ 2) * (1 + t ^ 2) = |q| := by
      exact div_mul_cancel₀ _ hdpos.ne'
    have := mul_le_mul_of_nonneg_left hd5 hw0
    linarith
  have hfin : C₁ * (1 + N) ^ (-δ / 2) ≤ max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
    have hpos : 0 < 1 + N := by linarith
    have e : (1 + N) ^ (-δ / 2) = (1 + N) ^ (-δ / 4) * (1 + N) ^ (-δ / 4) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have hδ4 : 0 ≤ δ / 4 := by positivity
    have ha : (1 + N) ^ (-δ / 4) ≤ (1 + |c₀|) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hb : (1 + N) ^ (-δ / 4) ≤ (1 + ‖X‖) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hab : (1 + N) ^ (-δ / 2) ≤ (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4) := by
      rw [e]; exact mul_le_mul ha hb (by positivity) (by positivity)
    exact mul_le_mul (le_max_left _ _) hab (by positivity) hM.le
  have hmono : ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    exact setLIntegral_mono' measurableSet_Icc hpt
  calc ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ))
      ≤ ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := hmono
    _ = ENNReal.ofReal K * ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (C₁ * (1 + ‖c‖) ^ (-δ / 2)) := by
        gcongr
        exact hC₁ c
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4))) := by
        gcongr
    _ = ENNReal.ofReal (K * max C₁ 1 * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
        rw [← ENNReal.ofReal_mul hK.le]; congr 1; ring

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section

noncomputable section
open MeasureTheory Module
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2

abbrev TDom (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ

def chF (p m : ℕ) (ν : Fin (p + 1) → ℝ) (x : Xp p m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-(s0N p m l + ν l)))

def tailF (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (x : TDom p m) : ℝ≥0∞ :=
  ENNReal.ofReal (Lsq (tailPt x) 1 ^ ((-2 + α) / 2)) * ENNReal.ofReal (de (tailPt x) 1 ^ (-α)) *
    ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt x) i.succ ^ (-(s0N (p + 1) m i.succ + ν i)))

lemma chF_meas (p m : ℕ) (ν : Fin (p + 1) → ℝ) : Measurable (chF p m ν) := by
  unfold chF
  exact Finset.measurable_prod _ fun l _ =>
    ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)

lemma tailF_meas (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) : Measurable (tailF p m α ν) := by
  unfold tailF
  have h := cont_tailPt (p := p) (m := m)
  exact ((ENNReal.measurable_ofReal.comp (((cont_lsq 1).comp h).measurable.pow_const _)).mul
    (ENNReal.measurable_ofReal.comp (((cont_de 1).comp h).measurable.pow_const _))).mul
    (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp (((cont_de i.succ).comp h).measurable.pow_const _))

lemma criticalExponent_succ (p m : ℕ) (i : Fin (p + 1)) : s0N (p + 1) m i.succ = s0N p m i := by
  simp [s0N, Fin.val_succ]

lemma sum_s0N (p m : ℕ) : ∑ i, s0N p m i = 2 * p + m + 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [s0N]
  ring

lemma prod_update {p : ℕ} (d s ν : Fin (p + 1) → ℝ) (hd : ∀ l, 0 < d l) (α : ℝ) :
    ∏ l, d l ^ (-(s l + Function.update ν 0 (α + ν 0) l)) = d 0 ^ (-α) * ∏ l, d l ^ (-(s l + ν l)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
  rw [show -(s 0 + (α + ν 0)) = -α + -(s 0 + ν 0) by ring, Real.rpow_add (hd 0)]
  ring

lemma tail_pt (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (a0 : ℂ) (t : ℝ) (hr : 1 + ‖a0‖ ^ 2 = t ^ 2)
    (q : Xp p m) :
    tailF p m α ν (sclPt a0 t q) =
      ENNReal.ofReal ((1 + ‖a0‖ ^ 2) ^ ((-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i))) *
        chF p m (Function.update ν 0 (α + ν 0)) q := by
  have hL : 0 < 1 + ‖a0‖ ^ 2 := by positivity
  unfold tailF chF
  rw [lsq_scl_one, ← Fin.succ_zero_eq_one, de_scl a0 t hr q 0]
  simp only [de_scl a0 t hr q, criticalExponent_succ]
  rw [← hr, ← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.rpow_nonneg (mul_nonneg hL.le (de_pos q i).le) _),
    ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (de_pos q l).le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hL.le _)
      (Real.rpow_nonneg (mul_nonneg hL.le (de_pos q 0).le) _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  congr 1
  rw [prod_update (de q) (s0N p m) ν (de_pos q) α,
    Finset.prod_congr rfl fun i _ => Real.mul_rpow hL.le (de_pos q i).le, Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos hL, Real.mul_rpow hL.le (de_pos q 0).le]
  rw [show (-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i) = (-2 + α) / 2 + -α + ∑ i, -(s0N p m i + ν i) by
    rw [Finset.sum_neg_distrib]; ring, Real.rpow_add hL, Real.rpow_add hL]
  ring

lemma tail_inner (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (a0 : ℂ) :
    ∫⁻ q : Xp p m, tailF p m α ν (Fin.cons a0 q.1, q.2) =
      ENNReal.ofReal ((1 + ‖a0‖ ^ 2) ^ (-(2 + α + 2 * ∑ i, ν i) / 2)) *
        CHInt p m (Function.update ν 0 (α + ν 0)) := by
  have hL : 0 < 1 + ‖a0‖ ^ 2 := by positivity
  set t := Real.sqrt (1 + ‖a0‖ ^ 2) with ht_def
  have ht : 0 < t := Real.sqrt_pos.2 hL
  have htt : 1 + ‖a0‖ ^ 2 = t ^ 2 := (Real.sq_sqrt hL.le).symm
  have hc : Continuous fun q : Xp p m => ((Fin.cons a0 q.1, q.2) : TDom p m) :=
    (cont_cons.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd
  have hG : Measurable fun q : Xp p m => tailF p m α ν (Fin.cons a0 q.1, q.2) :=
    (tailF_meas p m α ν).comp hc.measurable
  have hpt : ∀ x : Xp p m, tailF p m α ν (Fin.cons a0 (sclL p m t x).1, (sclL p m t x).2) =
      tailF p m α ν (sclPt a0 t x) := fun x => by rw [sclL_apply]; rfl
  rw [lint_scl hG ht]
  simp only [hpt, tail_pt p m α ν a0 t htt]
  rw [lintegral_const_mul _ (chF_meas _ _ _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hreal : t ^ (4 * p + 2 * m + 2) * (1 + ‖a0‖ ^ 2) ^ ((-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i)) =
      (1 + ‖a0‖ ^ 2) ^ (-(2 + α + 2 * ∑ i, ν i) / 2) := by
    rw [show 4 * p + 2 * m + 2 = 2 * (2 * p + m + 1) by ring, pow_mul, ← htt, ← Real.rpow_natCast,
      ← Real.rpow_add hL, Finset.sum_add_distrib, sum_s0N]
    congr 1
    push_cast
    ring
  rw [hreal]
  rfl

lemma tail_eq (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) :
    TailInt p m α ν = kc (2 + α + 2 * ∑ i, ν i) * CHInt p m (Function.update ν 0 (α + ν 0)) := by
  show ∫⁻ x : TDom p m, tailF p m α ν x = _
  rw [split_cons _ (tailF_meas p m α ν), lintegral_congr fun w => tail_inner p m α ν w,
    lintegral_mul_const _ (by fun_prop)]
  rfl

private lemma norm_sq_add_norm_sq_sub_eq_complete_square (w B a : ℂ) :
    ‖w‖ ^ 2 + ‖B - w * star a‖ ^ 2 =
      (1 + ‖a‖ ^ 2) * ‖w - B * a / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 + ‖B‖ ^ 2 / (1 + ‖a‖ ^ 2) := by
  have key : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hL : (1 + (a.re ^ 2 + a.im ^ 2)) ≠ 0 := by positivity
  simp only [key, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

lemma ch_pt (p m : ℕ) (ν : Fin (p + 2) → ℝ) (y : TDom p m) :
    ∫⁻ w : ℂ, chF (p + 1) m ν (y.1, Fin.cons w y.2.1, y.2.2) =
      kc (2 + ν 0) * tailF p m (ν 0) (Fin.tail ν) y := by
  rcases y with ⟨a, b, r⟩
  dsimp only
  have hlsq0 : ∀ w : ℂ, Lsq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 = 1 := by
    intro w; simp [Lsq]
  have hrho : ∀ w : ℂ, rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 =
      rhoSq (tailPt ((a, b, r) : TDom p m)) 1 + ‖w‖ ^ 2 := by
    intro w
    simp [rhoSq, Lsq, tailPt, Fin.sum_univ_succ]
    ring
  have hbco : ∀ w : ℂ, bco ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 =
      bco (tailPt ((a, b, r) : TDom p m)) 1 - w * star (a 0) := by
    intro w
    simp [bco, tailPt, Fin.sum_univ_succ]
    ring
  have hL1 : Lsq (tailPt ((a, b, r) : TDom p m)) 1 = 1 + ‖a 0‖ ^ 2 := by
    simp [Lsq, tailPt, Fin.sum_univ_succ]
  have hd1 : de (tailPt ((a, b, r) : TDom p m)) 1 ^ 2 =
      (1 + ‖a 0‖ ^ 2) * rhoSq (tailPt ((a, b, r) : TDom p m)) 1 + ‖bco (tailPt ((a, b, r) : TDom p m)) 1‖ ^ 2 := by
    rw [de, Real.sq_sqrt (add_nonneg (mul_nonneg (by linarith [one_le_lsq (tailPt ((a, b, r) : TDom p m)) 1])
      (rhoSq_nonneg _ _)) (sq_nonneg _)), hL1]
  have hM := one_le_rhoSq (tailPt ((a, b, r) : TDom p m)) 1
  have hd1p := de_pos (tailPt ((a, b, r) : TDom p m)) 1
  set M := rhoSq (tailPt ((a, b, r) : TDom p m)) 1
  set B := bco (tailPt ((a, b, r) : TDom p m)) 1
  set d1 := de (tailPt ((a, b, r) : TDom p m)) 1
  set L := 1 + ‖a 0‖ ^ 2 with hL_def
  have hL : 0 < L := by positivity
  set D := M + ‖B‖ ^ 2 / L with hD_def
  have hD : 0 < D := add_pos_of_pos_of_nonneg (by linarith) (by positivity)
  set c : ℂ := B * a 0 / ((L : ℝ) : ℂ) with hc_def
  have hquad : ∀ w : ℂ, de ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 ^ 2 = L * ‖w - c‖ ^ 2 + D := by
    intro w
    rw [de, Real.sq_sqrt (add_nonneg (mul_nonneg (by linarith [one_le_lsq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0])
      (rhoSq_nonneg _ _)) (sq_nonneg _)), hlsq0, hrho, hbco, one_mul, add_assoc, norm_sq_add_norm_sq_sub_eq_complete_square, hD_def, hc_def, hL_def]
    ring
  have hzero : ∀ w : ℂ, de ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 ^ (-(s0N (p + 1) m 0 + ν 0)) =
      (L * ‖w - c‖ ^ 2 + D) ^ (-(2 + ν 0) / 2) := by
    intro w
    have hs : s0N (p + 1) m 0 = 2 := by simp [s0N]
    rw [hs, ← hquad w, ← Real.rpow_natCast, ← Real.rpow_mul (de_pos _ _).le]
    congr 1
    push_cast
    ring
  have htp : tailPt ((a, b, r) : TDom p m) = (a, Fin.cons 0 b, r) := rfl
  unfold chF tailF
  simp only [Fin.prod_univ_succ, de_cons, hzero]
  rw [lintegral_mul_const _ (by fun_prop), kernel L D hL hD c (2 + ν 0), hL1]
  have hkey : ENNReal.ofReal (L⁻¹ * D ^ (1 - (2 + ν 0) / 2)) =
      ENNReal.ofReal (L ^ ((-2 + ν 0) / 2)) * ENNReal.ofReal (d1 ^ (-ν 0)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : D = d1 ^ 2 / L := by
      rw [hd1, hD_def]
      field_simp
    rw [e1, Real.div_rpow (sq_nonneg _) hL.le, ← Real.rpow_natCast d1 2, ← Real.rpow_mul hd1p.le,
      show (1 - (2 + ν 0) / 2) = -ν 0 / 2 by ring,
      show ((2 : ℕ) : ℝ) * (-ν 0 / 2) = -ν 0 by push_cast; ring,
      show (-2 + ν 0) / 2 = -1 - (-ν 0 / 2) by ring, Real.rpow_sub hL, Real.rpow_neg_one]
    field_simp
  rw [hkey, htp, show de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) 1 = d1 from rfl]
  simp only [Fin.tail]
  ring

lemma ch_step (p m : ℕ) (ν : Fin (p + 2) → ℝ) :
    CHInt (p + 1) m ν = kc (2 + ν 0) * TailInt p m (ν 0) (Fin.tail ν) := by
  have hF := chF_meas (p + 1) m ν
  have hT := tailF_meas p m (ν 0) (Fin.tail ν)
  have step : ∀ a : Fin (p + 1) → ℂ,
      ∫⁻ z : (Fin (p + 1) → ℂ) × ((Fin m → ℂ) × ℝ), chF (p + 1) m ν (a, z) =
        ∫⁻ q : (Fin p → ℂ) × ((Fin m → ℂ) × ℝ), kc (2 + ν 0) * tailF p m (ν 0) (Fin.tail ν) (a, q) := by
    intro a
    rw [split_cons' (fun z => chF (p + 1) m ν (a, z)) (hF.comp measurable_prodMk_left)]
    exact lintegral_congr fun q => ch_pt p m ν (a, q)
  show ∫⁻ x : Xp (p + 1) m, chF (p + 1) m ν x =
    kc (2 + ν 0) * ∫⁻ y : TDom p m, tailF p m (ν 0) (Fin.tail ν) y
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable,
    lintegral_congr fun a => (step a).trans (lintegral_const_mul _ (hT.comp measurable_prodMk_left)),
    lintegral_const_mul _ hT.lintegral_prod_right']
  congr 1
  rw [Measure.volume_eq_prod (Fin (p + 1) → ℂ), lintegral_prod _ hT.aemeasurable]

end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
