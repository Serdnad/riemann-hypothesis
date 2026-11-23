module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfA
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivB

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  calc ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖x i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

def stp {p : ℕ} (α : Fin p → ℕ) (k : Fin p) : Fin p → ℕ := fun i => α i + if i = k then 1 else 0

theorem mem_step {p N : ℕ} {α : Fin p → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple p N) (k : Fin p) :
    stp α k ∈ Finset.Nat.antidiagonalTuple p (N + 1) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at hα ⊢
  simp [stp, Finset.sum_add_distrib, hα]

theorem pow_step {p : ℕ} (g : Fin p → ℂ) (α : Fin p → ℕ) (k : Fin p) :
    ∏ i, g i ^ stp α k i = (∏ i, g i ^ α i) * g k := by
  simp only [stp, pow_add, Finset.prod_mul_distrib]
  congr 1
  have h : ∀ i, g i ^ (if i = k then 1 else 0) = if i = k then g i else 1 := by
    intro i; split_ifs <;> simp
  simp only [h, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem iter_div (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (τ0 : ℝ) : ∀ (N : ℕ), (p : ℝ) - 1 < τ0 - N - 1 + 1 →
    ∀ F : V n → ℂ, DifferentiableOn ℂ F U →
    ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-τ0) * Real.exp (-ph0 y)) < ⊤ →
    ∃ H : (Fin p → ℕ) → V n → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple p N, DifferentiableOn ℂ (H α) U ∧
        ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - N)) *
          Real.exp (-ph0 y)) < ⊤) ∧
      ∀ y ∈ U, F y = ∑ α ∈ Finset.Nat.antidiagonalTuple p N, (∏ i, g i y ^ α i) * H α y := by
  have hSpos : ∀ y ∈ U, 0 < ∑ i, ‖g i y‖ ^ 2 := by
    intro y hy
    obtain ⟨i, hi⟩ := hnz y hy
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hScont : ContinuousOn (fun y => ∑ i, ‖g i y‖ ^ 2) U :=
    continuousOn_finsetSum _ fun i _ => ((hg i).continuousOn.norm).pow 2
  intro N
  induction N with
  | zero =>
    intro _ F hF hI
    refine ⟨fun _ => F, fun α hα => ⟨hF, by simpa using hI⟩, fun y _ => ?_⟩
    rw [Finset.Nat.antidiagonalTuple_zero_right]
    simp
  | succ N ih =>
    intro hN F hF hI
    have hN' : (p : ℝ) - 1 < τ0 - N - 1 + 1 := by push_cast at hN; linarith
    obtain ⟨H, hH, hid⟩ := ih hN' F hF hI
    set t : ℝ := τ0 - N - 1 with htdef
    have ht : (p : ℝ) - 1 < t := by rw [htdef]; push_cast at hN; linarith
    have hstep : ∀ α ∈ Finset.Nat.antidiagonalTuple p N, ∃ hh : Fin p → V n → ℂ,
        (∀ i, DifferentiableOn ℂ (hh i) U) ∧ (∀ y ∈ U, H α y = ∑ i, g i y * hh i y) ∧
        ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 y)) < ⊤ := by
      intro α hα
      have hIα : ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) *
          Real.exp (-ph0 y)) < ⊤ := by
        have e : -(t + 1) = -(τ0 - N) := by rw [htdef]; ring
        rw [e]; exact (hH α hα).2
      obtain ⟨hh, hhd, hhid, hhest⟩ := UpDivA.skoda_open hU S hz g ph0 t (H α) hp hg hnz hph hl ht
        (hH α hα).1 hIα
      exact ⟨hh, hhd, hhid, lt_of_le_of_lt hhest (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIα)⟩
    choose! hh hhd hhid hhI using hstep
    set A := Finset.Nat.antidiagonalTuple p N with hA
    obtain ⟨w, hw⟩ : ∃ w : V n → ℝ, w = fun y => (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y) :=
      ⟨_, rfl⟩
    have hw0 : ∀ y, 0 ≤ w y := fun y => by
      rw [hw]; exact mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _)
        (Real.exp_pos _).le
    have hwc : ContinuousOn w U := by
      rw [hw]
      exact (hScont.rpow_const fun y hy => Or.inl (hSpos y hy).ne').mul
        (Real.continuous_exp.comp_continuousOn hph.continuousOn.neg)
    refine ⟨fun β y => ∑ α ∈ A, ∑ k, if stp α k = β then hh α k y else 0,
      fun β _ => ⟨?_, ?_⟩, ?_⟩
    · have hk : ∀ α ∈ A, ∀ k ∈ (Finset.univ : Finset (Fin p)),
          DifferentiableOn ℂ (fun y => if stp α k = β then hh α k y else 0) U := by
        intro α hα k _
        by_cases hk : stp α k = β
        · simp only [hk, if_true]; exact hhd α hα k
        · simp only [hk, if_false]; exact differentiableOn_const (c := (0 : ℂ))
      have hα : ∀ α ∈ A, DifferentiableOn ℂ
          (fun y => ∑ k, if stp α k = β then hh α k y else 0) U := fun α hα =>
        (DifferentiableOn.sum (u := Finset.univ) (A := fun k y => if stp α k = β then hh α k y else 0)
          (hk α hα)).congr fun y _ => by simp [Finset.sum_apply]
      exact (DifferentiableOn.sum (u := A)
        (A := fun α y => ∑ k, if stp α k = β then hh α k y else 0) hα).congr fun y _ => by
          simp [Finset.sum_apply]
    · set C : ℝ := ((A ×ˢ (Finset.univ : Finset (Fin p))).card : ℝ) with hC
      have hpt : ∀ y, ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          ≤ C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2 := by
        intro y
        rw [← Finset.sum_product']
        refine (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact le_rfl
        · simp
      have hbound : ∀ y, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          * w y) ≤ ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y) := by
        intro y
        rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
          by positivity) (hw0 y)), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y
            ≤ (C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2) * w y := mul_le_mul_of_nonneg_right (hpt y) (hw0 y)
          _ = C * ∑ α ∈ A, (∑ k, ‖hh α k y‖ ^ 2) * w y := by rw [mul_assoc, Finset.sum_mul]
      have hfin : ∫⁻ y in U, ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y)
          < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [lintegral_finsetSum']
        · refine ENNReal.sum_lt_top.mpr fun α hα => ?_
          have := hhI α hα
          rw [hw]
          simpa [mul_assoc] using this
        · intro α hα
          have hc : ContinuousOn (fun y => (∑ k, ‖hh α k y‖ ^ 2) * w y) U :=
            (continuousOn_finsetSum _ fun k _ => ((hhd α hα k).continuousOn.norm).pow 2).mul hwc
          exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hU.measurableSet
      have e2 : (fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y))) =
          fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y) := by
        funext y
        rw [hw, mul_assoc]
        congr 4
        rw [htdef]; push_cast; ring
      show ∫⁻ y in U, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y)) < ⊤
      rw [e2]
      exact lt_of_le_of_lt (lintegral_mono hbound) hfin
    · intro y hy
      rw [hid y hy]
      have h1 : ∀ α ∈ A, (∏ i, g i y ^ α i) * H α y =
          ∑ k, (∏ i, g i y ^ stp α k i) * hh α k y := by
        intro α hα
        rw [hhid α hα y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_step]; ring
      rw [Finset.sum_congr rfl h1]
      symm
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (mem_step hα k)]

end UpDivB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF

open NumberField Complex Matrix Topology Filter MeasureTheory Set Metric ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem sq_sub_le (a b : ℂ) : ‖b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h := norm_sub_le a (a - b)
  rw [sub_sub_cancel] at h
  nlinarith [sq_nonneg (‖a‖ - ‖a - b‖), norm_nonneg b, norm_nonneg a, norm_nonneg (a - b)]

theorem ball_diff_eq {g1 : V (nd X) → ℂ} {z : V (nd X)} {ρ : ℝ} (hB : ball z ρ ⊆ OmF X x0) :
    ball z ρ \ {y | g1 y = 0} = ball z ρ ∩ Om1 X x0 g1 := by
  ext y
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, Om1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hB h1, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

theorem localRepresentationL2 {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (hWL : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) {bb : ℝ}
    {g1 : V (nd X) → ℂ} (hg1 : DifferentiableOn ℂ g1 (OmF X x0)) {F0 F' : V (nd X) → ℂ}
    (hF0 : ContinuousOn F0 (OmF X x0))
    (hJ : ∫⁻ z in Om1 X x0 g1, ENNReal.ofReal (‖F0 z - F' z‖ ^ 2 / kaF X x0 bb z) *
      W (cpt X x0 z) ∂muF X x0 < ⊤) :
    ∀ z ∈ OmF X x0, ∃ ρ > 0, ball z ρ ⊆ OmF X x0 ∧
      ∫⁻ y in ball z ρ \ {y | g1 y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤ := by
  intro z hz
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 (isOpen_OmF (X := X) (x0 := x0)) z hz
  set ρ := ε / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hKsub : closedBall z ρ ⊆ OmF X x0 := (closedBall_subset_ball (by linarith)).trans hεB
  have hBsub : ball z ρ ⊆ OmF X x0 := ball_subset_closedBall.trans hKsub
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall z ρ
  have hzK : z ∈ closedBall z ρ := mem_closedBall_self hρ0.le
  refine ⟨ρ, hρ0, hBsub, ?_⟩
  rw [ball_diff_eq X x0 hBsub]

  obtain ⟨M0, hM0⟩ := hKc.exists_bound_of_continuousOn (hF0.mono hKsub)
  have hgc : ContinuousOn (fun y => c * Real.exp (-phla X la (cpt X x0 y))) (closedBall z ρ) :=
    (continuousOn_const.mul (expPhla_cont (X := X) (x0 := x0) la)).mono hKsub
  obtain ⟨y1, -, hy1⟩ := hKc.exists_isMinOn ⟨z, hzK⟩ hgc
  set w0 := c * Real.exp (-phla X la (cpt X x0 y1)) with hw0
  have hw0p : 0 < w0 := by positivity
  have hdc : ContinuousOn (densF X x0) (closedBall z ρ) := (densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  obtain ⟨y2, hy2K, hy2⟩ := hKc.exists_isMinOn ⟨z, hzK⟩ hdc
  set d0 := densF X x0 y2 with hd0
  have hd0p : 0 < d0 := densF_pos (X := X) (x0 := x0) (hKsub hy2K)
  have hkc : ContinuousOn (kaF X x0 bb) (closedBall z ρ) := fun y hy =>
    (ka_contDiffAt (X := X) (x0 := x0) bb (hKsub hy)).continuousAt.continuousWithinAt
  obtain ⟨k1, hk1⟩ := hKc.exists_bound_of_continuousOn hkc
  set kmax := max k1 1 with hkmax
  have hka : ∀ y ∈ closedBall z ρ, 0 < kaF X x0 bb y ∧ kaF X x0 bb y ≤ kmax := fun y hy => by
    have hp : 0 < kaF X x0 bb y := Real.exp_pos _
    refine ⟨hp, ?_⟩
    have := hk1 y hy
    rw [Real.norm_eq_abs, abs_of_pos hp] at this
    exact this.trans (le_max_left _ _)

  have hOm1o : IsOpen (Om1 X x0 g1) :=
    hg1.continuousOn.isOpen_inter_preimage (isOpen_OmF (X := X) (x0 := x0)) isOpen_compl_singleton
  have hOm1m : MeasurableSet (Om1 X x0 g1) := hOm1o.measurableSet
  have hOm1s : Om1 X x0 g1 ⊆ OmF X x0 := fun y hy => hy.1
  set dd : V (nd X) → ℝ≥0∞ := fun y => ENNReal.ofReal (densF X x0 y) with hdd
  set h : V (nd X) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * W (cpt X x0 y) with hh
  have hJ' : ∫⁻ y in Om1 X x0 g1, dd y * h y < ⊤ := by
    have e : ∫⁻ y in Om1 X x0 g1, h y ∂muF X x0 = ∫⁻ y in Om1 X x0 g1, dd y * h y := by
      rw [muF, restrict_withDensity hOm1m, Measure.restrict_restrict hOm1m, Set.inter_eq_left.2 hOm1s]
      exact lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
        (((densF_continuousOn (X := X) (x0 := x0)).mono hOm1s).aemeasurable hOm1m).ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h
    rw [← e]
    exact hJ
  set Cst : ℝ := 2 * kmax / (w0 * d0) with hCst
  have hpt : ∀ y ∈ ball z ρ ∩ Om1 X x0 g1, ENNReal.ofReal (‖F' y‖ ^ 2) ≤
      ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y) := by
    rintro y ⟨hyB, -⟩
    have hyK : y ∈ closedBall z ρ := ball_subset_closedBall hyB
    have hyF : y ∈ OmF X x0 := hKsub hyK
    obtain ⟨hk0, hkle⟩ := hka y hyK
    have hdy : d0 ≤ densF X x0 y := hy2 hyK
    have hwy : w0 ≤ c * Real.exp (-phla X la (cpt X x0 y)) := hy1 hyK
    have hW : ENNReal.ofReal w0 ≤ W (cpt X x0 y) := (ENNReal.ofReal_le_ofReal hwy).trans (hWL _ hyF)
    have hq : 0 ≤ ‖F0 y - F' y‖ ^ 2 := by positivity
    have hM2 : ‖F0 y‖ ^ 2 ≤ M0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM0 y hyK) 2
    have hsq := sq_sub_le (F0 y) (F' y)
    have f1 : 1 ≤ kmax / kaF X x0 bb y := (one_le_div hk0).2 hkle
    have f2 : 1 ≤ densF X x0 y / d0 := (one_le_div hd0p).2 hdy
    have hdens : 0 ≤ densF X x0 y := hd0p.le.trans hdy
    have hCst0 : 0 ≤ Cst := by positivity
    have hreal : 2 * ‖F0 y - F' y‖ ^ 2 ≤
        Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0 := by
      have e : Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0 =
          2 * ‖F0 y - F' y‖ ^ 2 * ((kmax / kaF X x0 bb y) * (densF X x0 y / d0)) := by
        rw [hCst]
        field_simp
      rw [e]
      have f3 : 1 ≤ (kmax / kaF X x0 bb y) * (densF X x0 y / d0) := by nlinarith
      nlinarith
    calc ENNReal.ofReal (‖F' y‖ ^ 2)
        ≤ ENNReal.ofReal (2 * M0 ^ 2 + 2 * ‖F0 y - F' y‖ ^ 2) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal (2 * ‖F0 y - F' y‖ ^ 2) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y) := by
          gcongr ENNReal.ofReal (2 * M0 ^ 2) + ?_
          calc ENNReal.ofReal (2 * ‖F0 y - F' y‖ ^ 2)
              ≤ ENNReal.ofReal (Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0) :=
                ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal Cst * (ENNReal.ofReal (densF X x0 y) *
                  (ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * ENNReal.ofReal w0)) := by
                rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCst0 hdens) (div_nonneg hq hk0.le)),
                  ENNReal.ofReal_mul (mul_nonneg hCst0 hdens), ENNReal.ofReal_mul hCst0]
                ring
            _ ≤ ENNReal.ofReal Cst * (dd y * h y) := by
                show _ ≤ ENNReal.ofReal Cst * (ENNReal.ofReal (densF X x0 y) *
                  (ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * W (cpt X x0 y)))
                gcongr
  calc ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, ENNReal.ofReal (‖F' y‖ ^ 2)
      ≤ ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, (ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y)) :=
        setLIntegral_mono' (measurableSet_ball.inter hOm1m) hpt
    _ = ENNReal.ofReal (2 * M0 ^ 2) * volume (ball z ρ ∩ Om1 X x0 g1) +
          ENNReal.ofReal Cst * ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, dd y * h y := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.restrict_apply_univ]
    _ < ⊤ := by
        apply ENNReal.add_lt_top.2 ⟨?_, ?_⟩
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top)
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((lintegral_mono_set Set.inter_subset_right).trans_lt hJ')

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF
end
