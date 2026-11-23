module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

namespace LogCoverDescent

variable {n a : ℕ} (h : a ≤ n)

lemma add_mem_logCover_iff {v : Fin n → ℂ} (hre : ∀ k : Fin n, (v k).re = 0)
    (hz : ∀ k : Fin n, a ≤ k.val → v k = 0) (w : Fin n → ℂ) :
    w + v ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_ofPred_eq, Pi.add_apply, Complex.add_re, hre, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk

def periods (φ : (Fin n → ℂ) → ℂ) : AddSubgroup (Fin n → ℂ) where
  carrier := {v | ∀ w, (w + v ∈ logCover h ↔ w ∈ logCover h) ∧ (w ∈ logCover h → φ (w + v) = φ w)}
  zero_mem' := fun w => by simp
  add_mem' := by
    intro u v hu hv w
    simp only [Set.mem_ofPred_eq] at hu hv
    have e : w + (u + v) = (w + u) + v := (add_assoc _ _ _).symm
    refine ⟨?_, fun hw => ?_⟩
    · rw [e, (hv _).1, (hu _).1]
    · rw [e, (hv _).2 ((hu w).1.2 hw), (hu w).2 hw]
  neg_mem' := by
    intro v hv w
    simp only [Set.mem_ofPred_eq] at hv
    have e : (w + -v) + v = w := by abel
    have key : w + -v ∈ logCover h ↔ w ∈ logCover h := by
      rw [← (hv (w + -v)).1, e]
    refine ⟨key, fun hw => ?_⟩
    have := (hv (w + -v)).2 (key.2 hw)
    rw [e] at this
    exact this.symm

variable {h}

lemma single_mem_periods {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w)
    (k : Fin n) (hk : k.val < a) : Pi.single k (2 * Real.pi * Complex.I) ∈ periods h φ := by
  have hkk : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
  intro w
  refine ⟨add_mem_logCover_iff h (fun j => ?_) (fun j hj => ?_) w, fun hw => ?_⟩
  · by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  · have : j ≠ k := fun e => by subst e; omega
    simp [this]
  · have := hφ ⟨k.val, hk⟩ w hw
    rwa [hkk] at this

lemma mem_periods_of {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {v : Fin n → ℂ}
    (hv : ∀ k : Fin n, (k.val < a → ∃ m : ℤ, v k = m * (2 * Real.pi * Complex.I)) ∧
      (a ≤ k.val → v k = 0)) :
    v ∈ periods h φ := by
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  by_cases hk : k.val < a
  · obtain ⟨m, hm⟩ := (hv k).1 hk
    have e : Pi.single k (v k) = m • (Pi.single k (2 * Real.pi * Complex.I) : Fin n → ℂ) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp [hm, zsmul_eq_mul]
      · simp [hj]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (single_mem_periods hφ k hk) m
  · rw [(hv k).2 (by omega), Pi.single_zero]
    exact AddSubgroup.zero_mem _

lemma eq_of_exp_eq {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {w w' : Fin n → ℂ}
    (hw : w ∈ logCover h)
    (hd : ∀ k : Fin n, (k.val < a → Complex.exp (w' k) = Complex.exp (w k)) ∧
      (a ≤ k.val → w' k = w k)) :
    φ w' = φ w := by
  have hv : w' - w ∈ periods h φ := mem_periods_of hφ fun k => by
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hd k).1 hk)
      exact ⟨m, by simp [hm]⟩
    · simp [(hd k).2 hk]
  have := (hv w).2 hw
  have e : w + (w' - w) = w' := by abel
  rwa [e] at this

def branchLift (a : ℕ) (z0 z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val < a then Complex.log (z k / z0 k) + Complex.log (z0 k) else z k

omit h in
lemma analyticAt_eval (k : Fin n) (z : Fin n → ℂ) : AnalyticAt ℂ (fun z : Fin n → ℂ => z k) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt z

lemma ne_zero_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n)
    (hk : k.val < a) : z k ≠ 0 := by
  have := hz.2 ⟨k.val, hk⟩
  unfold cuspCoord at this
  rwa [show Fin.castLE h ⟨k.val, hk⟩ = k from Fin.ext rfl] at this

lemma norm_lt_one_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n) :
    ‖z k‖ < 1 :=
  (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)

omit h in
lemma exp_branchLift {z0 z : Fin n → ℂ} {k : Fin n} (hk : k.val < a) (h0 : z0 k ≠ 0)
    (hz : z k ≠ 0) : Complex.exp (branchLift a z0 z k) = z k := by
  simp only [branchLift, if_pos hk]
  rw [Complex.exp_add, Complex.exp_log (div_ne_zero hz h0), Complex.exp_log h0,
    div_mul_cancel₀ _ h0]

lemma branchLift_mem {z0 z : Fin n → ℂ} (h0 : z0 ∈ puncturedChart h (ball 0 1))
    (hz : z ∈ puncturedChart h (ball 0 1)) : branchLift a z0 z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    have e := exp_branchLift hi (ne_zero_of_mem h0 _ hi) (ne_zero_of_mem hz _ hi)
    have hn := norm_lt_one_of_mem hz (Fin.castLE h i)
    rw [← e, Complex.norm_exp] at hn
    exact Real.exp_lt_one_iff.1 hn
  · simp only [branchLift, if_neg (by omega : ¬ k.val < a)]
    exact norm_lt_one_of_mem hz k

omit h in
lemma analyticAt_branchLift {z0 : Fin n → ℂ} (h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0) :
    AnalyticAt ℂ (branchLift a z0) z0 := by
  refine AnalyticAt.pi (f := fun k z => branchLift a z0 z k) fun k => ?_
  by_cases hk : k.val < a
  · simp only [branchLift, if_pos hk]
    refine AnalyticAt.add (AnalyticAt.clog ?_ ?_) analyticAt_const
    · exact (analyticAt_eval k z0).div analyticAt_const (h0 k hk)
    · rw [div_self (h0 k hk)]
      exact Complex.one_mem_slitPlane
  · simp only [branchLift, if_neg hk]
    exact analyticAt_eval k z0

lemma isOpen_puncturedChart : IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z | z (Fin.castLE h j) ≠ 0} := by
    ext z; simp [puncturedChart, cuspCoord]
  rw [this]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)

end LogCoverDescent


open LogCoverDescent in
theorem LogCoverDescent.proof : LogCoverDescent.Statement := by
  intro n a h φ hφa hφ
  refine ⟨fun z0 hz0 => ?_, fun w hw => ?_⟩
  · have h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0 := ne_zero_of_mem hz0
    have hc : AnalyticAt ℂ (fun z => φ (branchLift a z0 z)) z0 :=
      (hφa _ (branchLift_mem hz0 hz0)).comp (analyticAt_branchLift h0)
    refine hc.congr ?_
    filter_upwards [(isOpen_puncturedChart (h := h)).mem_nhds hz0] with z hz
    symm
    refine eq_of_exp_eq hφ (branchLift_mem hz0 hz) fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [exp_branchLift hk (h0 k hk) (ne_zero_of_mem hz k hk)]
      simp only [logLift, if_pos hk]
      exact Complex.exp_log (ne_zero_of_mem hz k hk)
    · simp only [logLift, branchLift, if_neg (by omega : ¬ k.val < a)]
  · refine eq_of_exp_eq hφ hw fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · simp only [logLift, expCover, if_pos hk]
      exact Complex.exp_log (Complex.exp_ne_zero _)
    · simp only [logLift, expCover, if_neg (by omega : ¬ k.val < a)]

end

end GroundTheory.Heights₂.Heights.Regular
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)

noncomputable section

theorem continuous_of_atlasSmooth {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    simpa using (hf j).continuousOn
  have h2 := (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
    ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem regMax_bounds {ι : Type} [Fintype ι] [Nonempty ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2 := by
  classical
  exact ((ReciprocityTheory.AnForm.A.regMax_thm ι).1 η hη).2.2.2.1 t

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

theorem isCompact_image_closure_mid [CompactSpace X] (j : Fin P.N) :
    IsCompact ((P.chart j) '' closure (P.mid j)) :=
  isClosed_closure.isCompact.image_of_continuousOn
    ((P.chart j).continuousOn.mono (P.closure_mid j))

theorem exists_margin [CompactSpace X] :
    ∃ δ > 0, ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target := by
  have h : ∀ j, ∃ δ, 0 < δ ∧
      cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target :=
    fun j => (P.isCompact_image_closure_mid j).exists_cthickening_subset_open
      (P.chart j).open_target
      (image_subset_iff.2 fun x hx => (P.chart j).map_source (P.closure_mid j hx))
  choose δ hδ hsub using h
  by_cases hN : Nonempty (Fin P.N)
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min δ
    exact ⟨δ j₀, hδ j₀, fun j => (cthickening_mono (hj₀ j) _).trans (hsub j)⟩
  · exact ⟨1, one_pos, fun j => (hN ⟨j⟩).elim⟩

theorem exists_bound_q [CompactSpace X] {δ : ℝ}
    (hδ : ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target) :
    ∃ Q : ℝ, ∀ j, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), |P.q j y| ≤ Q := by
  have h : ∀ j, ∃ Q : ℝ, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), ‖P.q j y‖ ≤ Q :=
    fun j => (P.isCompact_image_closure_mid j).cthickening.exists_bound_of_continuousOn
      ((P.q_smooth j).continuousOn.mono (hδ j))
  choose Q hQ using h
  refine ⟨∑ j, |Q j|, fun j y hy => ?_⟩
  calc |P.q j y| = ‖P.q j y‖ := (Real.norm_eq_abs _).symm
    _ ≤ Q j := hQ j y hy
    _ ≤ |Q j| := le_abs_self _
    _ ≤ ∑ j, |Q j| := Finset.single_le_sum (fun i _ => abs_nonneg (Q i)) (Finset.mem_univ j)

end PotentialCharts

end

end GroundTheory.Heights₂.Heights.Regular
end
