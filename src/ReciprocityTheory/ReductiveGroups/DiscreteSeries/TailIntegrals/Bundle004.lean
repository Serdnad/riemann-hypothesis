module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoSqInsSucc
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

namespace J2

lemma sum_Iic {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Iic l, g j = ∑ j, if j ≤ l then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma sum_Ioi {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Ioi l, g j = ∑ j, if l < j then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma iic_zero {n : ℕ} (g : Fin (n + 1) → ℝ) : ∑ j ∈ Finset.Iic 0, g j = g 0 := by
  rw [sum_Iic]
  simp [Fin.le_zero_iff]

lemma upd_eq {p : ℕ} (ν : Fin (p + 2) → ℝ) :
    Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0) = fun j => ν j.succ + if j = 0 then ν 0 else 0 := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Fin.tail, add_comm]
  · simp [Fin.tail]

lemma iic_succ {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Iic l.succ, ν j = ν 0 + ∑ j ∈ Finset.Iic l, ν j.succ := by
  rw [sum_Iic, sum_Iic (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_le_succ_iff]

lemma ioi_succ {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Ioi l.succ, ν j = ∑ j ∈ Finset.Ioi l, ν j.succ := by
  rw [sum_Ioi, sum_Ioi (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_lt_succ_iff]

lemma cond_step {p : ℕ} (ν : Fin (p + 2) → ℝ) (h : CHCond (p + 1) ν) :
    0 < ν 0 ∧ 0 < ν 0 + 2 * ∑ i, Fin.tail ν i ∧
      CHCond p (Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0)) := by
  obtain ⟨h1, h2⟩ := h
  have hI : ∑ j ∈ Finset.Ioi (0 : Fin (p + 2)), ν j = ∑ i, Fin.tail ν i := by
    rw [sum_Ioi, Fin.sum_univ_succ (n := p + 1)]
    simp [Fin.tail, Fin.succ_pos]
  have e0 := h1 0
  rw [iic_zero] at e0
  refine ⟨e0, ?_, ?_⟩
  · have := h2 0 (by simp)
    rw [iic_zero, hI] at this
    exact this
  · rw [upd_eq]
    have hA : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, (ν j.succ + if j = 0 then ν 0 else 0) =
        ∑ j ∈ Finset.Iic l.succ, ν j := by
      intro l
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_Iic.2 (Fin.zero_le l)),
        iic_succ]
      ring
    have hB : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Ioi l, (ν j.succ + if j = 0 then ν 0 else 0) =
        ∑ j ∈ Finset.Ioi l.succ, ν j := by
      intro l
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_neg (by simp), ioi_succ, add_zero]
    refine ⟨fun l => ?_, fun l hl => ?_⟩
    · beta_reduce
      rw [hA]
      exact h1 l.succ
    · beta_reduce
      rw [hA, hB]
      exact h2 l.succ (by rw [Fin.val_succ]; omega)

end J2

theorem c1 : C1 := by
  intro p m x
  rw [J2.de_sq, J2.de_sq, J2.lsq_zero, J2.rhoSq_zero, J2.bco_zero, J2.lsq_one]
  have hL : (0 : ℝ) < 1 + ((x.1 0).re * (x.1 0).re + (x.1 0).im * (x.1 0).im) := by
    nlinarith [mul_self_nonneg (x.1 0).re, mul_self_nonneg (x.1 0).im]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  field_simp
  ring

theorem tailFin_of (hCH : CH) : TailFin := by
  intro p m α ν hc hpos
  rw [J2.tail_eq]
  exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (hCH p m _ hc)

theorem ch_of (hC1 : C1) : CH := by
  intro p
  induction p with
  | zero =>
    intro m ν hν
    exact J2.ch_base m ν (by have := hν.1 0; rwa [J2.iic_zero] at this)
  | succ p ih =>
    intro m ν hν
    obtain ⟨h0, hs, hc⟩ := J2.cond_step ν hν
    rw [J2.ch_step, J2.tail_eq]
    exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith))
      (ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (ih m _ hc))

end ReciprocityTheory.ChartRestriction.DS.Xi
end

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private lemma rpow_sq_half {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : a ^ r = (a ^ 2) ^ (r / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

private lemma nnorm_ae (γ : ℝ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : ℂ, f z * (‖z‖₊ : ℝ≥0∞) ^ (-γ) = ∫⁻ z : ℂ, f z * ENNReal.ofReal (‖z‖ ^ (-γ)) := by
  apply lintegral_congr_ae
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))
  filter_upwards [h0] with z hz
  congr 1
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hz)]
  congr 1
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

private lemma core {e0 γ C : ℝ}
    (hC : ∀ (c : ℂ) (D : ℝ), 0 < D →
      (∫⁻ x : ℂ, ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e0 / 2)) *
        ENNReal.ofReal (‖x‖ ^ (-γ))) ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e0) / 2)))
    {L d1 d0 : ℝ} (c : ℂ) (f : ℂ → ℝ) (hL : 0 < L) (hd1 : 0 < d1) (hd0 : 0 ≤ d0)
    (h0 : d0 ^ 2 = L * ‖c‖ ^ 2 + d1 ^ 2 / L) (hf0 : ∀ z, 0 ≤ f z)
    (hf : ∀ z, f z ^ 2 = L * ‖z - c‖ ^ 2 + d1 ^ 2 / L) :
    ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) ≤
      ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
  have hD : 0 < d1 / L := div_pos hd1 hL
  have hsq : ∀ t : ℝ, L * t + d1 ^ 2 / L = L * (t + (d1 / L) ^ 2) := by
    intro t
    have := hL.ne'
    field_simp
  have he : -(2 - e0) / 2 = -1 + e0 / 2 := by ring
  have hpt : ∀ z, f z ^ (-(2 - e0)) =
      L ^ (-1 + e0 / 2) * (‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2) := by
    intro z
    rw [rpow_sq_half (hf0 z), hf z, hsq, he, Real.mul_rpow hL.le (by positivity)]
  have hX : ‖c‖ ^ 2 + (d1 / L) ^ 2 = d0 ^ 2 / L := by
    rw [h0, hsq]; field_simp
  have hLp : L ^ (-1 + γ / 2) = L ^ (-1 + e0 / 2) / L ^ (-(γ - e0) / 2) := by
    rw [← Real.rpow_sub hL]; congr 1; ring
  have hd0p : (d0 ^ 2) ^ (-(γ - e0) / 2) = d0 ^ (-(γ - e0)) := (rpow_sq_half hd0 _).symm
  calc ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ))
      = ∫⁻ z : ℂ, ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          (ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ))) := by
        refine lintegral_congr (fun z => ?_)
        rw [hpt z, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _), mul_assoc]
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ∫⁻ z : ℂ, ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (C * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact hC c _ hD
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2) *
          (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)).symm
    _ = ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
        congr 1
        rw [hX, Real.div_rpow (sq_nonneg _) hL.le, hd0p, hLp]
        ring

theorem lintegral_insertFiber_le (hC1 : C1) (hK : KER) {e0 γ : ℝ} (he0 : 0 < e0) (hγ : e0 < γ) (hγ2 : γ < 2) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ {p m : ℕ} (y : Yp p m),
      ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * (‖z‖₊ : ℝ≥0∞) ^ (-γ) ≤
        ENNReal.ofReal (CK * Lsq (tailPt y) 1 ^ (-1 + γ / 2) * de (tailPt y) 0 ^ (-(γ - e0))) := by
  obtain ⟨C, hC⟩ := hK e0 γ he0 hγ hγ2
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro p m y
  have hf : ∀ z : ℂ, de (ins y z) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖z - y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    intro z
    have hb : bco (ins y z) 1 = bco (tailPt y) 1 := by simpa using bco_ins_succ y z 0
    have hd : de (ins y z) 1 = de (tailPt y) 1 := by simpa using de_ins_succ y z 0
    have h := hC1 p m (ins y z)
    rw [hb, hd, Lsq_ins] at h
    simp only [ins, Fin.cons_zero] at h
    exact h
  have h0 : de (tailPt y) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    have := hf 0
    rw [zero_sub, norm_neg] at this
    exact this
  calc _ = ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) :=
        nnorm_ae γ _
    _ ≤ _ := core hC _ (fun z => de (ins y z) 0) (lt_of_lt_of_le one_pos (Lsq_ge_one _ _))
        (lt_of_lt_of_le one_pos (de_ge_one _ _)) (le_trans zero_le_one (de_ge_one _ _)) h0
        (fun z => le_trans zero_le_one (de_ge_one _ _)) hf

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
