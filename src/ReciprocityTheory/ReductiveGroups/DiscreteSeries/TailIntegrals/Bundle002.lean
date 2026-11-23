module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.IntegrableUnitIndicator
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
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace PolynomialGrowthIntegrals

lemma int_pos_rpow {R κ : ℝ} (hR : 0 < R) (hκ : κ < 1) :
    ∫⁻ β in Ioc 0 R, ENNReal.ofReal (β ^ (-κ)) = ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hr : (-1 : ℝ) < -κ := by linarith
  have hint : IntegrableOn (fun β : ℝ => β ^ (-κ)) (Ioc 0 R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1 (intervalIntegral.intervalIntegrable_rpow' hr)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] fun β : ℝ => β ^ (-κ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg hx.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl hr)]
  have h1 : -κ + 1 = 1 - κ := by ring
  rw [h1, Real.zero_rpow (by linarith), sub_zero]

lemma int_abs_rpow {R κ : ℝ} (hR : 0 < R) (hκ0 : 0 < κ) (hκ : κ < 1) :
    ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) ≤ 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hpos : ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) =
      ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, ← int_pos_rpow hR hκ]
    exact setLIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [abs_of_pos hx.1]
  have hneg : ∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ)) =
      ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (measurableSet_Icc (a := (0 : ℝ)) (b := R))
      (f := fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ))) (by fun_prop)
    have hs : Neg.neg ⁻¹' Icc (0 : ℝ) R = Icc (-R) 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
    simp only [abs_neg] at h
    rw [hs] at h
    exact h
  calc ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ))
      ≤ (∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
        rw [← Icc_union_Icc_eq_Icc (by linarith : -R ≤ 0) hR.le]
        exact lintegral_union_le _ _ _
    _ = 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by rw [hneg, hpos, two_mul]

lemma fac_le {A b t β β' R : ℝ} (hR : 0 < R) (hA : R ≤ A) (ht : 0 ≤ t) (hβ : |β| ≤ R)
    (hβ' : |β'| ≤ R) :
    (A ^ 2 + (β - b) ^ 2) ^ (-t / 2) ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) := by
  have hA0 : 0 < A := lt_of_lt_of_le hR hA
  have hx : 0 < A ^ 2 + (β - b) ^ 2 := by positivity
  have hy : 0 < A ^ 2 + (β' - b) ^ 2 := by positivity
  have h1 := abs_le.1 hβ
  have h2 := abs_le.1 hβ'
  have hd : (β' - β) ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have h9 : A ^ 2 + (β' - b) ^ 2 ≤ 9 * (A ^ 2 + (β - b) ^ 2) := by
    nlinarith [sq_nonneg ((β' - β) - (β - b))]
  calc (A ^ 2 + (β - b) ^ 2) ^ (-t / 2)
      = 3 ^ t * (9 * (A ^ 2 + (β - b) ^ 2)) ^ (-t / 2) := by
        rw [Real.mul_rpow (by norm_num) hx.le, show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        have h0 : t + 2 * (-t / 2) = 0 := by ring
        rw [h0, Real.rpow_zero, one_mul]
    _ ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy h9 (by linarith)) (by positivity)

lemma slowWeight_le {n : ℕ} {t A b : Fin n → ℝ} {R β β' : ℝ} (hR : 0 < R) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i, R ≤ A i) (hβ : |β| ≤ R) (hβ' : |β'| ≤ R) :
    slowly t A b β ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * slowly t A b β' := by
  unfold slowly
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun i _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (fac_le hR (hA i) (ht i) hβ hβ')

lemma measurable_slowWeight {n : ℕ} (t A b : Fin n → ℝ) : Measurable (slowly t A b) := by
  unfold slowly
  fun_prop

end PolynomialGrowthIntegrals

open PolynomialGrowthIntegrals in
theorem slowWeightBound' : SLOW := by
  intro n T κ hκ0 hκ1
  refine ⟨3 ^ T / (1 - κ) + 1, fun t A b R hR ht hT hA => ?_⟩
  set f := slowly t A b with hf_def
  set I := ∫⁻ β, f β with hI
  have hfm : Measurable f := measurable_slowWeight t A b
  have hw : Measurable fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ)) := by fun_prop
  set c : ℝ := 3 ^ (∑ i, t i) / (2 * R) with hc
  set q : ℝ := R ^ (1 - κ) / (1 - κ) with hq

  have hcen : ∀ β ∈ Icc (-R) R, f β ≤ ENNReal.ofReal c * I := by
    intro β hβ
    have hb : |β| ≤ R := abs_le.2 ⟨hβ.1, hβ.2⟩
    have key : f β * ENNReal.ofReal (2 * R) ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by
      calc f β * ENNReal.ofReal (2 * R) = ∫⁻ _ in Icc (-R) R, f β := by
            rw [setLIntegral_const, Real.volume_Icc]; congr 2; ring
        _ ≤ ∫⁻ β' in Icc (-R) R, ENNReal.ofReal (3 ^ ∑ i, t i) * f β' :=
            setLIntegral_mono (measurable_const.mul hfm) fun β' hβ' =>
              slowWeight_le hR ht hA hb (abs_le.2 ⟨hβ'.1, hβ'.2⟩)
        _ = ENNReal.ofReal (3 ^ ∑ i, t i) * ∫⁻ β' in Icc (-R) R, f β' := lintegral_const_mul _ hfm
        _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by gcongr; exact setLIntegral_le_lintegral _ _
    have hinv : ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
    calc f β = f β * ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I * ENNReal.ofReal (1 / (2 * R)) := by gcongr
      _ = ENNReal.ofReal c * I := by
          rw [hc, div_eq_mul_one_div (3 ^ ∑ i, t i), ENNReal.ofReal_mul (by positivity)]; ring

  have hA1 : ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤
      ENNReal.ofReal (c * (2 * q)) * I := by
    calc ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in Icc (-R) R, ENNReal.ofReal c * I * ENNReal.ofReal (|β| ^ (-κ)) :=
          setLIntegral_mono (measurable_const.mul hw) fun β hβ => by gcongr; exact hcen β hβ
      _ = ENNReal.ofReal c * I * ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) :=
          lintegral_const_mul _ hw
      _ ≤ ENNReal.ofReal c * I * (2 * ENNReal.ofReal q) :=
          by gcongr; exact int_abs_rpow hR hκ0 hκ1
      _ = ENNReal.ofReal (c * (2 * q)) * I := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          try ring

  have hA2 : ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤ ENNReal.ofReal (R ^ (-κ)) * I := by
    calc ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (R ^ (-κ)) := by
          refine setLIntegral_mono (hfm.mul measurable_const) fun β hβ => ?_
          have hb : R < |β| := by
            by_contra h
            exact hβ (abs_le.1 (not_lt.1 h))
          gcongr f β * ?_
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hR hb.le (by linarith))
      _ = (∫⁻ β in (Icc (-R) R)ᶜ, f β) * ENNReal.ofReal (R ^ (-κ)) := lintegral_mul_const _ hfm
      _ ≤ I * ENNReal.ofReal (R ^ (-κ)) := by gcongr; exact setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (R ^ (-κ)) * I := mul_comm _ _

  have hRk : R ^ (1 - κ) = R * R ^ (-κ) := by
    rw [show 1 - κ = 1 + -κ by ring, Real.rpow_add hR, Real.rpow_one]
  have hcq : c * (2 * q) = 3 ^ (∑ i, t i) * R ^ (-κ) / (1 - κ) := by
    rw [hc, hq, hRk]
    have : (1 - κ) ≠ 0 := by linarith
    field_simp
    try ring
  have hsT : (3 : ℝ) ^ (∑ i, t i) ≤ 3 ^ T := Real.rpow_le_rpow_of_exponent_le (by norm_num) hT
  have hRp : 0 < R ^ (-κ) := Real.rpow_pos_of_pos hR _
  have hreal : c * (2 * q) + R ^ (-κ) ≤ (3 ^ T / (1 - κ) + 1) * R ^ (-κ) := by
    rw [hcq, add_mul, one_mul, div_mul_eq_mul_div]
    gcongr
    try linarith
  calc ∫⁻ β, slowly t A b β * ENNReal.ofReal (|β| ^ (-κ))
      = (∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) :=
        (lintegral_add_compl (fun β => f β * ENNReal.ofReal (|β| ^ (-κ))) measurableSet_Icc).symm
    _ ≤ ENNReal.ofReal (c * (2 * q)) * I + ENNReal.ofReal (R ^ (-κ)) * I := add_le_add hA1 hA2
    _ = ENNReal.ofReal (c * (2 * q) + R ^ (-κ)) * I := by
        rw [ENNReal.ofReal_add (by positivity) hRp.le, add_mul]
    _ ≤ ENNReal.ofReal ((3 ^ T / (1 - κ) + 1) * R ^ (-κ)) * I :=
        by gcongr
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2

lemma lsq_zero {p m : ℕ} (x : Xp p m) : Lsq x 0 = 1 := by simp [Lsq]

lemma lsq_one {p m : ℕ} (x : Xp (p + 1) m) : Lsq x 1 = 1 + ‖x.1 0‖ ^ 2 := by
  simp [Lsq]

lemma rhoSq_zero {p m : ℕ} (x : Xp (p + 1) m) : rhoSq x 0 = rhoSq x 1 + ‖x.2.1 0‖ ^ 2 := by
  simp only [rhoSq, Fin.sum_univ_succ]
  simp
  ring_nf

lemma bco_zero {p m : ℕ} (x : Xp (p + 1) m) : bco x 0 = bco x 1 - x.2.1 0 * star (x.1 0) := by
  simp only [bco, Fin.sum_univ_succ]
  simp
  ring_nf

lemma one_le_lsq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

lemma rhoSq_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma de_sq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by
  unfold de
  rw [Real.sq_sqrt]
  have := one_le_lsq x l; have := rhoSq_nonneg x l
  positivity

lemma de_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ de x l := Real.sqrt_nonneg _

lemma one_le_rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma de_pos {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 < de x l := by
  unfold de
  apply Real.sqrt_pos.2
  have h1 := one_le_lsq x l; have h2 := one_le_rhoSq x l
  have : 0 ≤ ‖bco x l‖ ^ 2 := by positivity
  nlinarith

lemma rhoSq_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = rhoSq ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [rhoSq, Lsq, Fin.sum_univ_succ]

lemma bco_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    bco ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = bco ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [bco, Fin.sum_univ_succ]

lemma de_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    de ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp only [de, rhoSq_cons, bco_cons]
  rfl

def sclPt {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ :=
  (Fin.cons a0 (r • x.1), r • x.2.1, r • x.2.2.1, r ^ 2 * x.2.2.2)

lemma lsq_scl_one {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    Lsq (tailPt (sclPt a0 r x)) 1 = 1 + ‖a0‖ ^ 2 := by
  simp [Lsq, tailPt, sclPt]

lemma lsq_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    Lsq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * Lsq x i := by
  simp only [Lsq, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [Nat.zero_lt_succ, if_true, add_lt_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  linarith

lemma rhoSq_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    rhoSq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * rhoSq x i := by
  have hl := lsq_scl a0 r hr x (Fin.last p)
  rw [Fin.succ_last] at hl
  unfold rhoSq
  rw [hl]
  simp only [tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  simp

lemma bco_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) (i : Fin (p + 1)) :
    bco (tailPt (sclPt a0 r x)) i.succ = ((r ^ 2 : ℝ) : ℂ) * bco x i := by
  simp only [bco, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, Complex.real_smul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp
  have s1 : ∑ j, (r : ℂ) ^ 2 * ((‖x.2.2.1 j‖ : ℂ)) ^ 2 = (r : ℂ) ^ 2 * ∑ j, ((‖x.2.2.1 j‖ : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
  have s2 : (∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then (r : ℂ) * x.2.1 j * ((r : ℂ) * (starRingEnd ℂ) (x.1 j)) else 0)
      = (r : ℂ) ^ 2 * ∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then x.2.1 j * (starRingEnd ℂ) (x.1 j) else 0 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> ring
  rw [s1, s2]; ring

lemma de_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    de (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * de x i := by
  have h := de_sq (tailPt (sclPt a0 r x)) i.succ
  rw [lsq_scl a0 r hr, rhoSq_scl a0 r hr, bco_scl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r)] at h
  have h2 := de_sq x i
  have : de (tailPt (sclPt a0 r x)) i.succ ^ 2 = (r ^ 2 * de x i) ^ 2 := by rw [h, mul_pow (r ^ 2) (de x i), h2]; ring
  have p1 := de_nonneg (tailPt (sclPt a0 r x)) i.succ
  have p2 := de_nonneg x i
  exact (pow_left_inj₀ p1 (by positivity) two_ne_zero).1 this

lemma cont_lsq {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => Lsq x l := by
  unfold Lsq
  exact continuous_const.add (continuous_finsetSum (Finset.univ : Finset (Fin _)) fun j _ => by split_ifs <;> fun_prop)

lemma cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => rhoSq x l := by
  unfold rhoSq
  refine ((cont_lsq _).add (continuous_finsetSum _ fun j _ => by fun_prop)).add
    (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)

lemma cont_bco {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => bco x l := by
  unfold bco
  refine Continuous.sub ?_ (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)
  fun_prop

lemma cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l :=
  Real.continuous_sqrt.comp (((cont_lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

lemma cont_cons {p : ℕ} : Continuous fun q : ℂ × (Fin p → ℂ) => (Fin.cons q.1 q.2 : Fin (p + 1) → ℂ) := by
  refine continuous_pi fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply i).comp continuous_snd

lemma cont_tailPt {p m : ℕ} :
    Continuous (tailPt : (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ → Xp (p + 1) m) := by
  unfold tailPt
  exact continuous_fst.prodMk ((cont_cons.comp (continuous_const.prodMk
    (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd))

end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

def fS {p m : ℕ} (s : Fin (p + 2) → ℝ) (x : Xp (p + 1) m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-s l))

def rho (t : ℝ) : ℂ := (1 + t * Complex.I) ^ 2 / ((1 + t ^ 2 : ℝ) : ℂ)

def rot {p m : ℕ} (t : ℝ) (x : Xp p m) : Xp p m :=
  (fun j => rho t * x.1 j, fun j => rho t * x.2.1 j, fun i => rho t * x.2.2.1 i, x.2.2.2)

def scl {p m : ℕ} (τ : ℝ) (x : Xp (p + 1) m) : Xp (p + 1) m :=
  (Function.update x.1 0 (τ * x.1 0), Function.update x.2.1 0 (x.2.1 0 / τ), x.2.2.1, x.2.2.2)

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dot_star_self (y : ι → ℂ) : star y ⬝ᵥ y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma tW_sq (q : ι) (x : ι → ℂ) :
    tW q x ^ 2 = ∑ i, Complex.normSq (x i) - Complex.normSq (x q) := by
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg])]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ q)]

lemma tW_mulVec {h : Matrix ι ι ℂ} (hu : hᴴ * h = 1) {q : ι}
    (hrow : ∀ j, h q j = if j = q then 1 else 0) (x : ι → ℂ) :
    tW q (h *ᵥ x) = tW q x ∧ (h *ᵥ x) q = x q := by
  have hq : (h *ᵥ x) q = x q := by
    simp [mulVec, dotProduct, hrow]
  refine ⟨?_, hq⟩
  have hn : ∑ i, Complex.normSq ((h *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
    have e : star (h *ᵥ x) ⬝ᵥ (h *ᵥ x) = star x ⬝ᵥ x := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]
    rw [dot_star_self, dot_star_self] at e
    exact_mod_cast e
  have h1 := tW_sq q (h *ᵥ x)
  have h2 := tW_sq q x
  rw [hn, hq, ← h2] at h1
  have n1 : 0 ≤ tW q (h *ᵥ x) := Real.sqrt_nonneg _
  have n2 : 0 ≤ tW q x := Real.sqrt_nonneg _
  exact (pow_left_inj₀ n1 n2 two_ne_zero).mp h1

lemma volume_Bset_ne_zero {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) :
    volume (Bset q) ≠ 0 := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Continuous.sqrt (continuous_finsetSum _ fun i _ => ?_)
    by_cases hi : i = q
    · simp only [hi, ↓reduceIte]; exact continuous_const
    · simp only [hi, ↓reduceIte]; exact Complex.continuous_normSq.comp (continuous_apply i)
  have hU : IsOpen {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} :=
    (isOpen_lt continuous_const hc).inter
      ((isOpen_lt hc continuous_const).inter
        (isOpen_lt (continuous_norm.comp (continuous_apply q)) continuous_const))
  let x0 : ι → ℂ := fun i => if i = p then ((3 / 4 : ℝ) : ℂ) else 0
  have hs : (∑ i, if i = q then (0 : ℝ) else Complex.normSq (x0 i)) = 9 / 16 := by
    rw [Finset.sum_eq_single p]
    · simp only [hpq, ↓reduceIte, x0, Complex.normSq_ofReal]; norm_num
    · intro b _ hb; simp [x0, hb]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  have ht : tW q x0 = 3 / 4 := by
    unfold tW
    rw [hs, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx0 : x0 ∈ {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} := by
    refine ⟨by rw [ht]; norm_num, by rw [ht]; norm_num, ?_⟩
    simp [x0, Ne.symm hpq]
  have hsub : {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} ⊆ Bset q :=
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  intro h0
  exact (hU.measure_pos volume ⟨x0, hx0⟩).ne' (measure_mono_null hsub h0)

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end
