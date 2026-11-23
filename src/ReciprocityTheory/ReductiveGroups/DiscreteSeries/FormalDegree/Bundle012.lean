module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBaseA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle011
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle005

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jall_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem jall_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

def adKL {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, jall_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, jall_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, Pi.smul_apply, Matrix.smul_apply,
      RingHom.id_apply, Complex.real_smul, smul_eq_mul]

theorem jall_adK_inv {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : adK k⁻¹ (adK k z) = z := by
  have hk := toMK_facts k
  have h : pmat (adK k⁻¹ (adK k z)) = pmat z := by
    rw [pmat_adK, pmat_adK, toMK_inv, Matrix.conjTranspose_conjTranspose]
    calc (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ) * toMK k
        = ((toMK k)ᴴ * toMK k) * pmat z * ((toMK k)ᴴ * toMK k) := by simp only [Matrix.mul_assoc]
      _ = pmat z := by rw [hk.1, Matrix.one_mul, Matrix.mul_one]
  rw [← pact_pmat_coords (adK k⁻¹ (adK k z)), h, pact_pmat_coords]

theorem jall_abs_det_adKL {ε : Fin n → Bool} (k : KG ε) : |LinearMap.det (adKL k)| = 1 := by
  have hinj : Function.Injective (adKL k) := fun x y hxy => by
    have := congrArg (adK k⁻¹) hxy
    simpa only [adKL, LinearMap.coe_mk, AddHom.coe_mk, jall_adK_inv] using this
  have hmp := adK_measurePreserving k
  have hcs : IsCompact ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    (isCompact_closedBall 0 1).image (LinearMap.continuous_of_finiteDimensional _)
  have h1 : volume ((adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1)) =
      volume ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    hmp.measure_preimage hcs.isClosed.measurableSet.nullMeasurableSet
  have hpre : (adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) =
      Metric.closedBall (0 : PCoord ε → ℂ) 1 := Set.preimage_image_eq _ hinj
  rw [hpre, MeasureTheory.Measure.addHaar_image_linearMap] at h1
  have hpos : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hfin : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : PCoord ε → ℂ) 1).measure_lt_top.ne
  have h2 : ENNReal.ofReal |LinearMap.det (adKL k)| = 1 := by
    have h3 : 1 * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) =
        ENNReal.ofReal |LinearMap.det (adKL k)| * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).mp h3).symm
  exact ENNReal.ofReal_eq_one.mp h2

def jdetA {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : ℝ :=
  LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
    (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))

theorem jall_diff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    DifferentiableAt ℝ (actR (ε := ε) g) z := by
  first
  | exact (JacB.actR_contDiff' hg).differentiable one_ne_zero z
  | exact (JacB.actR_contDiff' hg).differentiable le_rfl z

theorem jall_chain {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : jdetA (g * h) z = jdetA h (actR g z) * jdetA g z := by
  unfold jdetA
  have hfun : actR (ε := ε) (g * h) = actR h ∘ actR g := funext (actR_mul hg hh)
  rw [hfun, fderiv_comp z (jall_diff hh (actR g z)) (jall_diff hg z)]
  exact LinearMap.det_comp _ _

theorem jall_fderiv_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    fderiv ℝ (actR (ε := ε) (toMK k)) z = LinearMap.toContinuousLinearMap (adKL k⁻¹) := by
  have e : actR (ε := ε) (toMK k) = ⇑(LinearMap.toContinuousLinearMap (adKL k⁻¹)) := by
    funext w
    rw [actR_K]
    rfl
  rw [e]
  exact ContinuousLinearMap.fderiv _

theorem jall_abs_jdetA_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    |jdetA (toMK k) z| = 1 := by
  unfold jdetA
  rw [jall_fderiv_K]
  exact jall_abs_det_adKL k⁻¹

theorem jall_inUJ_K {ε : Fin n → Bool} (k : KG ε) : inUJ ε (toMK k) := by
  first
  | exact k.1.2
  | exact k.val.property
  | exact k.2.1

theorem jall_actR_K_zero {ε : Fin n → Bool} (k : KG ε) : actR (ε := ε) (toMK k) 0 = 0 := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  apply actR_of_eq_polarM (k := k)
  simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]

theorem jacAll {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac (actR g z) = Jac z := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  obtain ⟨k, hk⟩ := actR_spec hg z
  set w := actR g z with hw
  have hEz := exp_pmat_inUJ z
  have hEw := exp_pmat_inUJ w
  have hK := jall_inUJ_K k
  have h0z : actR (ε := ε) (NormedSpace.exp (pmat z)) 0 = z := by
    apply actR_of_eq_polarM (k := 1)
    simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul]
    first
    | rfl
    | (rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.one_mul])
    | simp
  have hc1 := jall_chain hEz hg 0
  rw [h0z] at hc1
  have hc2 := jall_chain hK hEw 0
  rw [jall_actR_K_zero] at hc2
  have hmul : NormedSpace.exp (pmat z) * g = toMK k * NormedSpace.exp (pmat w) := by
    rw [hk]; rfl
  rw [hmul, hc2] at hc1
  have hab : |jdetA g z| * |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| = |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| := by
    have := congrArg abs hc1
    rw [abs_mul, abs_mul, jall_abs_jdetA_K, mul_one] at this
    rw [this, mul_comm]
  have hbZ : |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| * Jac z = 1 := JacB.jacBase' z
  have hcW : |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| * Jac w = 1 := JacB.jacBase' w
  show |jdetA g z| * Jac w = Jac z
  linear_combination (-(|jdetA g z| * Jac w)) * hbZ + (Jac w * Jac z) * hab + Jac z * hcW

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

theorem pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

theorem hs_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    hs (pmat (c • z)) = c ^ 2 * hs (pmat z) := by
  rw [hs_pmat, hs_pmat, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem hs_half_le_quadratic {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    hs (pmat z) / 2 ≤ Qf (0 : Fin n → ℝ) z := by
  have e : hs (pmat z) / 2 = ∑ ab, ‖z ab‖ ^ 2 := by rw [hs_pmat]; ring
  rw [e, Qf]
  refine Finset.sum_le_sum fun ab _ => ?_
  have hv : ((ab.1.2 : ℕ) : ℝ) + 1 ≤ ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.mp ab.2.1
  have hw : 1 ≤ wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by simp only [wab, Pi.zero_apply]; linarith
  exact le_mul_of_one_le_left (by positivity) hw

theorem hs_eighth_le_of_small {ε : Fin n → Bool} (z : PCoord ε → ℂ) (h : rhoP z ≤ 1 / 2) :
    hs (pmat z) / 8 ≤ Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have h1 := ph_lower hA z h (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have h2 := hs_half_le_quadratic z
  linarith

theorem potential_lower_min {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    1 / 16 * min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) ≤
      Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have hH0 : 0 ≤ hs (pmat z) := by rw [hs_pmat]; positivity
  have hP0 := ph_nonneg hA z
  rcases Nat.eq_zero_or_pos (q0 ε) with hq | hq
  · have e : min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) = 0 := by
      rw [hq]; simp [hH0]
    rw [e]; linarith
  · set c := Real.sqrt (2 * (q0 ε : ℝ)) with hc
    have hq1 : (1 : ℝ) ≤ (q0 ε : ℝ) := by exact_mod_cast hq
    have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
    set r := Real.sqrt (hs (pmat z)) with hr
    have hrr : r ^ 2 = hs (pmat z) := Real.sq_sqrt hH0
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrho : rhoP z = c * r := rfl
    by_cases hsm : c * r ≤ 1 / 2
    · have := hs_eighth_le_of_small z (by rw [hrho]; exact hsm)
      have hm := min_le_left (hs (pmat z)) (r / c)
      nlinarith
    · replace hsm := lt_of_not_ge hsm
      have hrp : 0 < r := by
        by_contra h0
        have : r = 0 := le_antisymm (not_lt.mp h0) hr0
        rw [this, mul_zero] at hsm; linarith
      set t := 2 * c * r with ht
      have ht1 : 1 ≤ t := by rw [ht]; linarith
      have ht0 : 0 < t := by linarith
      set z' := (1 / t) • z with hz'
      have hpz : pmat z = (t : ℂ) • pmat z' := by
        rw [hz', pmat_smul, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel ht0.ne',
          Complex.ofReal_one, one_smul]
      have hhs : hs (pmat z') = (1 / t) ^ 2 * r ^ 2 := by rw [hz', hs_pmat_smul, hrr]
      have hsq : Real.sqrt (hs (pmat z')) = 1 / t * r := by
        rw [hhs, ← mul_pow, Real.sqrt_sq (by positivity)]
      have hrho' : rhoP z' ≤ 1 / 2 := by
        have e2 : rhoP z' = c * Real.sqrt (hs (pmat z')) := rfl
        rw [e2, hsq, ht]
        field_simp
        linarith
      have hsm' := hs_eighth_le_of_small z' hrho'
      have hsc := ph_scale hA z' ht1
      rw [← hpz] at hsc
      have hm := min_le_right (hs (pmat z)) (r / c)
      have key : 1 / 16 * (r / c) ≤ t * (hs (pmat z') / 8) := by
        rw [hhs, ht]
        field_simp
        nlinarith
      have := mul_le_mul_of_nonneg_left hsm' ht0.le
      nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end
