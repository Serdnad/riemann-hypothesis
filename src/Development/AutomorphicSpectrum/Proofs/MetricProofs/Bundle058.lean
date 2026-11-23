module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Continuous
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartA
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

lemma near_small (a c K' : ℝ) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, 0 < t → t ≤ t₁ →
      c * (Real.log (1 / t) + K') ^ a * t ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 3) / 2 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (1 / 6 : ℝ) (by norm_num)
  have h2 : Tendsto (fun y : ℝ => (c * Real.exp (K' / 6)) * (y ^ a * Real.exp (-(1 / 6) * y)))
      atTop (nhds 0) := by
    simpa [neg_mul] using h.const_mul (c * Real.exp (K' / 6))
  have h3 := h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Y, hY⟩ := eventually_atTop.1 h3
  refine ⟨Real.exp (K' - Y), Real.exp_pos _, fun t ht htle => ?_⟩
  set y := Real.log (1 / t) + K' with hy
  have hlog : Real.log t = K' - y := by
    rw [hy, one_div, Real.log_inv]; ring
  have hYy : Y ≤ y := by
    have := Real.log_le_log ht htle
    rw [Real.log_exp, hlog] at this
    linarith
  have hs := (hY y hYy).le
  have e1 : t ^ ((1 : ℝ) / 2) =
      t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)) := by
    have : Real.exp (K' / 6) * Real.exp (-(1 / 6) * y) = t ^ ((1 : ℝ) / 6) := by
      rw [← Real.exp_add, Real.rpow_def_of_pos ht, hlog]; congr 1; ring
    rw [this, ← Real.rpow_add ht]; norm_num
  have hp : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
  rw [e1]
  calc c * y ^ a * (t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)))
      = t ^ ((1 : ℝ) / 3) * (c * Real.exp (K' / 6) * (y ^ a * Real.exp (-(1 / 6) * y))) := by ring
    _ ≤ t ^ ((1 : ℝ) / 3) * (1 / 2) := mul_le_mul_of_nonneg_left hs hp.le
    _ = t ^ ((1 : ℝ) / 3) / 2 := by ring

theorem polyMaxOff_le_of_rLoc_le :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → DifferentiableOn ℝ u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ u z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, rLoc S m z ≤ Real.log (1 / t) + K → polyMaxOff S u z t ≤ u z + t ^ ((1 : ℝ) / 3) / 2 := by
  intro D S m u C₅ K hm hd hg
  have hclosed : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
    have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
      ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
    rw [this]
    exact S.finite_toSet.isClosed_biUnion
      (fun i _ => isClosed_eq (continuous_apply i) continuous_const)
  have hopen : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hclosed
  set a := |C₅| with ha
  set K' := K + RegularChartScaling.mTot S m * Real.log 4 with hK'
  obtain ⟨t₁, ht₁, hsm⟩ := near_small a (a * Real.exp (K' / 2)) K'
  refine ⟨min (min (1 / 4) (Real.exp (-K))) t₁, by positivity, fun t ht htle z hz hr => ?_⟩
  have ht4 : t ≤ 1 / 4 := htle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htK : t ≤ Real.exp (-K) := htle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht1 : t ≤ t₁ := htle.trans (min_le_right _ _)
  obtain ⟨hzB, hzD⟩ := hz
  have hzn : ∀ i, ‖z i‖ ≤ 2 :=
    RegularChartScaling.norm_coord_le_of_ball (by norm_num : (5 / 4 : ℝ) ≤ 2) hzB
  have hzi : ∀ i ∈ S, z i ≠ 0 := fun i hi h0 => hzD ⟨i, hi, h0⟩
  have hcoord : ∀ i ∈ S, 2 * t ≤ ‖z i‖ := by
    intro i hi
    have hpos : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
    have hterm : Real.log (4 / ‖z i‖ ^ 2) ≤ Real.log (1 / t) + K := by
      have h1 : (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) ≤
          ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2) :=
        Finset.single_le_sum (f := fun j => (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2))
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (RegularChartScaling.log_term_nonneg (hzn j))) hi
      have h2 : Real.log (4 / ‖z i‖ ^ 2) ≤ (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) :=
        le_mul_of_one_le_left (RegularChartScaling.log_term_nonneg (hzn i)) (by exact_mod_cast hm i hi)
      have h3 := Real.exp_pos 1
      unfold rLoc at hr
      linarith
    have hEK : Real.exp K ≤ 1 / t := by
      rw [Real.exp_neg] at htK
      rw [le_div_iff₀ ht]
      have := mul_le_mul_of_nonneg_left htK (Real.exp_pos K).le
      rwa [mul_inv_cancel₀ (Real.exp_pos K).ne'] at this
    have hE : Real.exp (Real.log (1 / t) + K) ≤ 1 / t ^ 2 := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
      calc 1 / t * Real.exp K ≤ 1 / t * (1 / t) :=
            mul_le_mul_of_nonneg_left hEK (by positivity)
        _ = 1 / t ^ 2 := by field_simp
    have h4 : 4 / ‖z i‖ ^ 2 ≤ 1 / t ^ 2 :=
      ((Real.log_le_iff_le_exp (by positivity)).1 hterm).trans hE
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
    by_contra hlt
    push_neg at hlt
    nlinarith
  set y := Real.log (1 / t) + K' with hy
  have hfar : ∀ x ∈ closedBall z t, ∀ i ∈ S, ‖z i‖ / 2 ≤ ‖x i‖ ∧ 0 < ‖x i‖ := by
    intro x hx i hi
    have h1 : ‖x i - z i‖ ≤ t :=
      (norm_le_pi_norm (x - z) i).trans (mem_closedBall_iff_norm.1 hx)
    have h2 := norm_sub_norm_le (z i) (x i)
    rw [norm_sub_rev] at h2
    have h3 := hcoord i hi
    constructor <;> linarith
  have hmem : ∀ x ∈ closedBall z t,
      x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S := by
    intro x hx
    refine ⟨RegularChartScaling.closedBall_sub_of hzB (by linarith) hx, ?_⟩
    rintro ⟨i, hi, h0⟩
    have := (hfar x hx i hi).2
    rw [h0, norm_zero] at this
    exact lt_irrefl _ this
  have hrx : ∀ x ∈ closedBall z t, rLoc S m x ≤ y := by
    intro x hx
    have key : ∀ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤
        (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) + (m i : ℝ) * Real.log 4 := by
      intro i hi
      obtain ⟨h1, h2⟩ := hfar x hx i hi
      have hzp : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [← Real.log_mul (by positivity) (by norm_num)]
      refine Real.log_le_log (by positivity) ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_self_le_mul_self (by positivity) h1]
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    unfold rLoc at hr ⊢
    simp only [hy, hK', RegularChartScaling.mTot]
    linarith
  set B := a * y ^ a * Real.exp (y / 2) with hB
  have hfd : ∀ x ∈ closedBall z t, ‖fderiv ℝ u x‖ ≤ B := by
    intro x hx
    have hxm := hmem x hx
    have hxn : ∀ i, ‖x i‖ ≤ 2 :=
      RegularChartScaling.norm_coord_le_of_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hxm.1
    have hr1 : 1 ≤ rLoc S m x := by
      have := RegularChartScaling.rLoc_ge S m hxn
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hry := hrx x hx
    have hy0 : 0 ≤ y := by linarith
    have hp : rLoc S m x ^ C₅ ≤ y ^ a :=
      (Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self C₅)).trans
        (Real.rpow_le_rpow (by linarith) hry (abs_nonneg _))
    refine (hg x hxm).trans ?_
    refine mul_le_mul (mul_le_mul (le_abs_self C₅) hp (Real.rpow_nonneg (by linarith) _)
      (abs_nonneg _)) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hy0 _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfd z (mem_closedBall_self ht.le))
  have hBt : B * t ≤ t ^ ((1 : ℝ) / 3) / 2 := by
    have hlog : Real.log t = K' - y := by
      rw [hy, one_div, Real.log_inv]; ring
    have e : Real.exp (y / 2) * t = Real.exp (K' / 2) * t ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos ht, hlog]
      nth_rewrite 1 [← Real.exp_log ht]
      rw [hlog, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc B * t = a * y ^ a * (Real.exp (y / 2) * t) := by rw [hB]; ring
      _ = a * Real.exp (K' / 2) * y ^ a * t ^ ((1 : ℝ) / 2) := by rw [e]; ring
      _ ≤ t ^ ((1 : ℝ) / 3) / 2 := hsm t ht ht1
  unfold polyMaxOff
  refine csSup_le ⟨u z, z, ⟨mem_closedBall_self ht.le, hzD⟩, rfl⟩ ?_
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u) (s := closedBall z t)
    (x := z) (y := x) (C := B)
    (fun w hw => (hd w (hmem w hw)).differentiableAt (hopen.mem_nhds (hmem w hw)))
    hfd (convex_closedBall z t) (mem_closedBall_self ht.le) hx
  have h1 : ‖x - z‖ ≤ t := mem_closedBall_iff_norm.1 hx
  have h2 : u x - u z ≤ ‖u x - u z‖ := Real.le_norm_self _
  have h3 : B * ‖x - z‖ ≤ B * t := mul_le_mul_of_nonneg_left h1 hB0
  linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

lemma mollifier_bdd {D : ℕ} (ρ : ReciprocityTheory.AnForm.A.Mollifier D) : ∃ b : ℝ, ∀ w, ρ.toFun w ≤ b := by
  have hcs : HasCompactSupport ρ.toFun := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin D → ℂ) 1) ?_
    exact ρ.support_subset.trans ball_subset_closedBall
  obtain ⟨b, hb⟩ := ρ.contDiff.continuous.bounded_above_of_compact_support hcs
  exact ⟨b, fun w => (le_abs_self _).trans (hb w)⟩

lemma polyMax_le_pmoff_same {D : ℕ} {S : Finset (Fin D)} {u w : (Fin D → ℂ) → ℝ} {R B κ : ℝ}
    (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ B)
    (hW1 : ReciprocityTheory.AnForm.A.IsPsh (ball 0 R) w)
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0,
      ∃ y ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s R' : ℝ} (hs : 0 < s) (hsR : s < R') (hR' : closedBall z R' ⊆ ball 0 R) :
    ReciprocityTheory.AnForm.A.polyMax w z s ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
  have hR'0 : 0 < R' := hs.trans hsR
  have hconv := (ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm D (ball 0 R) w z R' isOpen_ball hW1 hR'0 hR').1
  set g : ℝ → ℝ := fun σ => ReciprocityTheory.AnForm.A.polyMax w z (Real.exp σ) with hg
  have hconv' : ConvexOn ℝ (Set.Iio (Real.log R')) g :=
    hconv.subset Set.Iio_subset_Iic_self (convex_Iio _)
  have hcont : ContinuousOn g (Set.Iio (Real.log R')) := hconv'.continuousOn isOpen_Iio
  have hlog : Real.log s < Real.log R' := Real.log_lt_log hs hsR
  have hca : ContinuousAt g (Real.log s) := hcont.continuousAt (Iio_mem_nhds hlog)
  have hsub : closedBall z s ⊆ ball 0 R := (closedBall_subset_closedBall hsR.le).trans hR'
  have hle : ∀ σ ∈ Set.Iio (Real.log s), g σ ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
    intro σ hσ
    have hlt : Real.exp σ < s := by
      have := Real.exp_lt_exp.2 (Set.mem_Iio.1 hσ)
      rwa [Real.exp_log hs] at this
    exact RegularChartScaling.polyMax_le_pmo hub hW3 (Real.exp_pos σ).le hlt hsub
  have hfin : g (Real.log s) ≤ max (RegularChartScaling.pmoff S u z s) (-κ) :=
    le_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.log s))))
      (by filter_upwards [self_mem_nhdsWithin] with σ hσ using hle σ hσ)
  simpa only [hg, Real.exp_log hs] using hfin

theorem molli_trunc_near_polyMax :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D), ContinuousOn u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) u → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) → ∃ (C t₀ : ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ t₀ ≤ 1 / 8 ∧ ∀ t, 0 < t → t ≤ t₀ → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, w t z = max (u z) (-C * Real.log (Real.log (1 / t)))) ∧ ContDiffOn ℝ ∞ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (ReciprocityTheory.AnForm.A.molli ρ t (w t)) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, u z ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z) ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z t ∧ polyMaxOff S u z t - epsT C t ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ∧ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ≤ polyMaxOff S u z t := by
  intro D S m u C₅ ρ hc hp hb
  have hC₅ : 0 ≤ C₅ := RegularChartScaling.fifth_volume_constant_nonneg m (by norm_num) (by norm_num) hb
  have hub : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ C₅ :=
    fun x hx => (hb x hx).2
  obtain ⟨C₀, ℓ₀, hC₀, hosc⟩ := RegularChartScaling.oscGen m (R := 3 / 2) (by norm_num) (by norm_num)
    hc hp hb (C₁ := 2) (by norm_num)
  obtain ⟨b, hbρ⟩ := mollifier_bdd ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hbρ 0)
  set K : ℝ := Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b with hK
  have hK0 : 0 ≤ K := by positivity
  set C : ℝ := C₀ * (K + 1) with hC
  have hCC₀ : C₀ ≤ C := by rw [hC]; nlinarith
  have hKC : K * C₀ ≤ C := by rw [hC]; nlinarith
  have hC1 : 1 ≤ C := hC₀.trans hCC₀
  refine ⟨C, min (min (Real.exp (-ℓ₀)) (Real.exp (-Real.exp 1))) (1 / 8),
    fun t => RegularChartScaling.extT S (3 / 2) u (C * Real.log (Real.log (1 / t))), hC1,
    lt_min (lt_min (Real.exp_pos _) (Real.exp_pos _)) (by norm_num),
    (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _, fun t ht htt => ?_⟩
  beta_reduce
  have ht₁ : t ≤ Real.exp (-ℓ₀) := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hℓ₀ : ℓ₀ ≤ Real.log (1 / t) := by
    have h1 : Real.log t ≤ -ℓ₀ := by
      have := Real.log_le_log ht ht₁
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]; linarith
  obtain ⟨he, hCt, hz⟩ := hosc t ht hℓ₀
  set ℓ := Real.log (1 / t) with hℓ
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le he
  set κ : ℝ := C * Real.log ℓ with hκ
  obtain ⟨w, hwe, hW1, hW2, hW3⟩ := RegularChartScaling.ext_exists S (R := 3 / 2) (by norm_num) hC₅ hc hp hub κ
  rw [← hwe]
  have hwu : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ w x :=
    fun x hx => by rw [hW2 x hx]; exact le_max_left _ _
  have ht2 : 2 * t ≤ 1 / 8 := by linarith
  obtain ⟨-, hsm, hps, hbd⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ w isOpen_ball hW1).1 t ht
  have hsh : ball (0 : Fin D → ℂ) (5 / 4) ⊆ ReciprocityTheory.AnForm.A.shrink (ball (0 : Fin D → ℂ) (3 / 2)) t :=
    fun z hz' => RegularChartScaling.closedBall_sub_of hz' (by linarith)
  have hsm' := hsm.mono hsh
  refine ⟨fun z hz' => by rw [neg_mul]; exact hW2 z hz', hsm', ?_, ?_, ?_⟩
  · exact (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ isOpen_ball
      (hsm'.of_le (by norm_cast))).1 (RegularChartScaling.isPsh_mono hps hsh)
  · intro z hz'
    have hzB : z ∈ ball (0 : Fin D → ℂ) (3 / 2) :=
      ball_subset_ball (by norm_num) hz'.1
    exact (hwu z ⟨hzB, hz'.2⟩).trans (hbd z (hsh hz'.1)).1
  · intro z hzB
    obtain ⟨h16, hgap⟩ := hz z hzB
    have hsubR : ∀ s, s ≤ 1 / 4 → closedBall z s ⊆ ball 0 (3 / 2) := fun s hs =>
      RegularChartScaling.closedBall_sub_of hzB (by linarith)
    have hs16 : 0 < t / (8 * 2) := by positivity
    have hmono : ∀ s s', 0 < s → s ≤ s' → s' ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ RegularChartScaling.pmoff S u z s' := fun s s' h0 h1 h2 =>
      RegularChartScaling.pmo_mono hub h0 h1 (hsubR s' h2)
    have hκ' : -κ ≤ RegularChartScaling.pmoff S u z (t / (8 * 2)) := by
      have : C₀ * Real.log ℓ ≤ κ :=
        mul_le_mul_of_nonneg_right hCC₀ (by linarith)
      linarith
    have hlow : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 4 → -κ ≤ RegularChartScaling.pmoff S u z s :=
      fun s h1 h2 => hκ'.trans (hmono _ _ hs16 h1 h2)
    have hPM : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 8 →
        ReciprocityTheory.AnForm.A.polyMax w z s ≤ RegularChartScaling.pmoff S u z s := fun s h1 h2 => by
      have := polyMax_le_pmoff_same hub hW1 hW3 (hs16.trans_le h1)
        (by linarith : s < 1 / 4) (hsubR _ le_rfl)
      rwa [max_eq_left (hlow s h1 (by linarith))] at this
    have hMP : ∀ s, 0 < s → s ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ ReciprocityTheory.AnForm.A.polyMax w z s := fun s h0 h1 =>
      RegularChartScaling.pmo_le_polyMax hW1.1 hwu h0 (hsubR s h1)
    obtain ⟨-, hmp⟩ := hbd z (hsh hzB)
    have hlb := GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed D ρ b _ w z t isOpen_ball hW1 ht
      (hsubR _ (by linarith)) hbρ
    have ht16 : t ≤ 1 / 16 := by linarith
    have hA := hPM (2 * t) (by rw [div_le_iff₀ (by norm_num)]; linarith) ht2
    have hB : RegularChartScaling.pmoff S u z (t / (4 * 2)) ≤ ReciprocityTheory.AnForm.A.polyMax w z (t / 4) :=
      (hmono _ _ (by positivity) (by linarith) (by linarith)).trans
        (hMP _ (by positivity) (by linarith))
    have hPA : RegularChartScaling.pmoff S u z t ≤ ReciprocityTheory.AnForm.A.polyMax w z (2 * t) :=
      (hmono _ _ ht (by linarith) (by linarith)).trans (hMP _ (by positivity) (by linarith))
    have hP2 := hMP (2 * t) (by positivity) (by linarith)
    have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
    have heps : K * epsT C₀ t ≤ epsT C t := by
      simp only [epsT, ← hℓ, mul_div_assoc]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hq
    have hgap' : ReciprocityTheory.AnForm.A.polyMax w z (2 * t) - ReciprocityTheory.AnForm.A.polyMax w z (t / 4) ≤
        epsT C₀ t := by linarith
    have hKg := mul_le_mul_of_nonneg_left hgap' hK0
    have hup := hPM t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    show -C * Real.log ℓ ≤ RegularChartScaling.pmoff S u z t ∧
      RegularChartScaling.pmoff S u z t - epsT C t ≤ _ ∧ _ ≤ RegularChartScaling.pmoff S u z t
    refine ⟨?_, ?_, hmp.trans hup⟩
    · rw [neg_mul]
      exact hlow t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    · linarith

end

end GlobalTheory.CompanionTheory.Ar.Giv
end
