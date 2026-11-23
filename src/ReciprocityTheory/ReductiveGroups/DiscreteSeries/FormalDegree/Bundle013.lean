module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CorePInvInUJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBaseA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle007

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by

  have hsq : ∀ y : PCoord ε → ℂ,
      ‖(((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2))) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
    intro y
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 1
    ring
  have htend : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    intro y
    rw [← hsq y]
    exact ENNReal.tendsto_ofReal (((hlim y).norm).pow 2)
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) := by
    intro t
    exact ENNReal.measurable_ofReal.comp
      ((((fdl_inner_continuous (lamT lam t) (T t) (T t).w (T t).w).comp
        (continuous_const_smul _)).norm.pow 2).measurable)
  have key : ∀ t : ℕ, 1 ≤ t →
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
        (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2) ≤
      ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
    have hs : (0 : ℝ) < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht0)
    have hpow : ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = ((t : ℝ) ^ (pOf ε * qOf ε))⁻¹ := by
      rw [pow_mul, inv_pow, Real.sq_sqrt ht0.le, inv_pow]
    conv_rhs => rw [lintegral_pcoord_smul _ hs]
    try rw [show 2 * pOf ε * qOf ε = 2 * (pOf ε * qOf ε) from mul_assoc _ _ _]
    rw [hpow, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one, one_mul]
    refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    exact le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)
  calc ENNReal.ofReal (PiW ε 0)
      = ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := (fdl_gauss ε).symm
    _ = ∫⁻ y : PCoord ε → ℂ, Filter.liminf (fun t : ℕ => ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := by
        congr 1
        funext y
        rw [(htend y).liminf_eq]
    _ ≤ Filter.liminf (fun t : ℕ => ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ _ := by
        refine Filter.liminf_le_liminf ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with t ht using key t ht

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_s_pos {t : ℕ} (ht : 1 ≤ t) : 0 < (Real.sqrt (t : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))

theorem fdU_s_sq {t : ℕ} (ht : 1 ≤ t) : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := by
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr (by omega)
  rw [inv_pow, Real.sq_sqrt ht'.le, inv_mul_cancel₀ ht'.ne']

theorem fdU_major {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ)
    (ht : 16 * n * q0 ε + 1 ≤ t) (y : PCoord ε → ℂ) :
    ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) ≤
      ENNReal.ofReal (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32) *
        ∏ ab : PCoord ε, Real.exp (-((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) := by
  have ht1 : 1 ≤ t := le_trans (by omega) ht
  have hs0 := fdU_s_pos ht1
  have hst := fdU_s_sq ht1
  have hfar := fdU_far hlam (t₀ := 16 * n * q0 ε + 1) (by omega) ht hs0 hst y
  apply ENNReal.ofReal_le_ofReal
  refine hfar.trans ?_
  rw [sub_eq_add_neg, Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rcases isEmpty_or_nonempty (PCoord ε) with hE | hN
  · have hp : pmat y = 0 := by
      ext a b
      simp only [pmat, Matrix.zero_apply]
      split_ifs with h1 h2
      · exact (hE.false ⟨(a, b), h1⟩).elim
      · exact (hE.false ⟨(b, a), h2⟩).elim
      · rfl
    have hh : hs (pmat y) = 0 := by rw [hp]; simp [hs]
    rw [hh, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero]
    simp
  · have ab : PCoord ε := Classical.choice hN
    have hc := fdU_c_pos ab
    have h2 := fdU_exp_le_prod hc.le y
    rw [← neg_mul]
    exact h2

theorem fdU_pointwise {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (T : ℕ) (hT : 1 ≤ T)
    (y : PCoord ε → ℂ) :
    limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop ≤
      ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
  set ρ := rhoP y
  set r := Real.sqrt (hs (pmat y))
  set C := ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ))
  set φ : ℝ → ℝ := fun v => Real.exp (-(1 - v * ρ) * Qf (0 : Fin n → ℝ) y + C * (v * r)) with hφdef
  have hφ : Continuous φ := by
    simp only [hφdef]; fun_prop
  have hu : Tendsto (fun t : ℕ => (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat T)))
  have hev : ∀ᶠ t : ℕ in atTop, (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * ρ < 1 := by
    have h := hu.mul_const ρ
    rw [zero_mul] at h
    exact h.eventually (gt_mem_nhds one_pos)
  have hle : ∀ᶠ t : ℕ in atTop, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y)) ≤
        ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) :=
    hev.mono fun t ht => ENNReal.ofReal_le_ofReal
      (fdU_near hlam (fdU_s_pos (by omega)) (fdU_s_sq (by omega)) y ht.le)
  have hlim : Tendsto (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop
      (𝓝 (ENNReal.ofReal (φ 0))) :=
    ENNReal.tendsto_ofReal ((hφ.tendsto 0).comp hu)
  have h0 : φ 0 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by simp [hφdef]
  calc _ ≤ limsup (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop :=
        limsup_le_limsup hle
    _ = ENNReal.ofReal (φ 0) := hlim.limsup_eq
    _ = _ := by rw [h0]

theorem formal_degree_limsup_upper_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) :
    Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) Filter.atTop ≤
      ENNReal.ofReal (PiW ε 0) := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [lintegral_pcoord_smul _ (fdU_s_pos ht), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt (t : ℝ)) 2, Real.sq_sqrt htpos.le, mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  set T : ℕ := 16 * n * q0 ε + 1 with hT
  rw [← Filter.limsup_nat_add _ T]
  refine le_trans (le_of_eq (Filter.limsup_congr (Filter.Eventually.of_forall fun i => hscale (i + T) (by omega)))) ?_
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
      (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hc : Continuous (fun y : PCoord ε → ℂ => (((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) :=
      continuous_const_smul _
    exact (Real.continuous_exp.comp (continuous_const.mul ((continuous_potential_pmat _).comp hc))).mul
      ((jac_continuous ε).comp hc)
  have hint := ((fdU_integrable_prod_exp (ε := ε)
    (c := (Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1))
    (fun ab => div_pos (fdU_c_pos ab) (by positivity))).const_mul
    (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32)))
  calc _ ≤ ∫⁻ y, limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop :=
        limsup_lintegral_le _ hmeas
          (fun t => Filter.Eventually.of_forall fun y => fdU_major hlam (t + T) (by omega) y)
          hint.lintegral_lt_top.ne
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) :=
        lintegral_mono fun y => fdU_pointwise hlam T (by omega) y
    _ = _ := fdU_lintegral_gauss ε

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def rmulPR (G : Matrix (Fin n) (Fin n) ℂ) (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) * G

def polarPR {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : Fin n → Fin n → ℂ := polarM kz

theorem continuous_rmulPR (G : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulPR G) := by
  unfold rmulPR
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * G)

theorem measurable_polarPR (ε : Fin n → Bool) : Measurable (polarPR (ε := ε)) := by
  have h : Continuous (polarPR (ε := ε)) := polarM_continuous ε
  exact h.measurable

theorem rmulPR_polarPR {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G)
    (z : PCoord ε → ℂ) : ∃ k' : KG ε, ∀ k : KG ε,
      rmulPR G (polarPR (k, z)) = polarPR (k * k', actR G z) := by
  have hE : inUJ ε (NormedSpace.exp (pmat z)) := exp_pmat_inUJ z
  have hEG : inUJ ε (NormedSpace.exp (pmat z) * G) := by
    unfold inUJ at hE hG ⊢
    rw [Matrix.conjTranspose_mul]
    calc Gᴴ * (NormedSpace.exp (pmat z))ᴴ * Jm ε * (NormedSpace.exp (pmat z) * G)
        = Gᴴ * ((NormedSpace.exp (pmat z))ᴴ * Jm ε * NormedSpace.exp (pmat z)) * G := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hE, hG]
  obtain ⟨⟨k', w⟩, hkw⟩ := polarM_surj _ hEG
  have hw : actR G z = w := by
    funext ab
    have h1 : plog (NormedSpace.exp (pmat z) * G) = pmat w := by
      rw [← hkw, plog_polarM]
    simp only [actR, h1, pmat, dif_pos ab.2]
  refine ⟨k', fun k => ?_⟩
  rw [hw]
  simp only [rmulPR, polarPR, polarM] at hkw ⊢
  have hm : toMK (k * k') = toMK k * toMK k' := rfl
  show toMK k * NormedSpace.exp (pmat z) * G = _
  rw [Matrix.mul_assoc, ← hkw, hm, Matrix.mul_assoc]

theorem muPolarMat_mul_right (ε : Fin n → Bool) {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G) :
    Measure.map (rmulPR G) (muPolarMat ε) = muPolarMat ε := by
  have hP : Measurable (polarPR (ε := ε)) := measurable_polarPR ε
  have hR : Measurable (rmulPR G) := (continuous_rmulPR G).measurable
  have hA : Measurable (actR (ε := ε) G) := (JacB.actR_continuous hG).measurable
  have hc := coreP hG
  have : IsFiniteMeasure (dk ε) := by
    rw [isFiniteMeasure_iff, (dk_props ε).1.measure_univ]
    exact ENNReal.one_lt_top

  have key : ∀ S : Set (Fin n → Fin n → ℂ), MeasurableSet S →
      muPolarMat ε S = ∫⁻ z, dk ε {k | polarPR (k, z) ∈ S}
        ∂(volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    intro S hS
    show (Measure.map (polarPR (ε := ε)) ((dk ε).prod
      (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))) S = _
    rw [Measure.map_apply hP hS, Measure.prod_apply_symm (hP hS)]
    rfl
  ext S hS
  rw [Measure.map_apply hR hS, key _ (hR hS), key _ hS]
  have step : ∀ z : PCoord ε → ℂ, dk ε {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
      dk ε {k | polarPR (k, actR G z) ∈ S} := by
    intro z
    obtain ⟨k', hk'⟩ := rmulPR_polarPR hG z
    have hset : {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
        (fun k => k * k') ⁻¹' {k | polarPR (k, actR G z) ∈ S} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hk']
    rw [hset, measure_preimage_mul_right]
  simp_rw [step]
  have hφ : Measurable fun w : PCoord ε → ℂ => dk ε {k | polarPR (k, w) ∈ S} :=
    measurable_measure_prodMk_right (hP hS)
  rw [← lintegral_map hφ hA, hc]

theorem muPolar_mul_right (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muPolar ε) = muPolar ε := by
  show Measure.map (fun x => x * g) (Measure.comap (intMuCD_eM ε) (muPolarMat ε)) =
    Measure.comap (intMuCD_eM ε) (muPolarMat ε)
  by_cases h : Function.Injective (intMuCD_eM ε) ∧
      ∀ s, MeasurableSet s → NullMeasurableSet (intMuCD_eM ε '' s) (muPolarMat ε)
  swap
  · simp only [Measure.comap, dif_neg h, Measure.map_zero]
  haveI : BorelSpace (UJ ε) := ⟨rfl⟩
  have hRm : Measurable (fun x : UJ ε => x * g) := (continuous_mul_const g).measurable
  have hG : inUJ ε (toM g) := g.2
  have h4 := muPolarMat_mul_right ε hG
  have hRM : Measurable (rmulPR (toM g)) := (continuous_rmulPR (toM g)).measurable
  ext S hS
  rw [Measure.map_apply hRm hS, Measure.comap_apply₀ _ _ h.1 h.2 (hRm hS).nullMeasurableSet,
    Measure.comap_apply₀ _ _ h.1 h.2 hS.nullMeasurableSet]
  have h1 : toM g * toM g⁻¹ = 1 := by
    rw [show toM g * toM g⁻¹ = toM (g * g⁻¹) from rfl, mul_inv_cancel]
    rfl
  have himg : intMuCD_eM ε '' ((fun x => x * g) ⁻¹' S) =
      rmulPR (toM g) ⁻¹' (intMuCD_eM ε '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * g, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y * g⁻¹, ?_, ?_⟩
      · show y * g⁻¹ * g ∈ S
        rw [inv_mul_cancel_right]
        exact hy
      · have hx : toM y = Matrix.of x * toM g := hxy
        show toM y * toM g⁻¹ = x
        rw [hx, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
  rw [himg, ← Measure.map_apply₀ hRM.aemeasurable (by rw [h4]; exact h.2 S hS), h4]

end ReciprocityTheory.ChartRestriction.DS
end
end
