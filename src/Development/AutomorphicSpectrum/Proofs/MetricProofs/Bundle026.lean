module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalModel

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {E : Type} [TopologicalSpace E] (A : FinHolAtlas e X) (j : Fin A.n) {p : X}
    (hp : p ∈ (A.chart j).source) (f : X → E)
    (h : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p)) : ContinuousAt f p := by
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp (f := A.chart j) h ((A.chart j).continuousAt hp)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hp] with z hz
  simp [(A.chart j).left_inv hz]

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {p : X} (hp : p ∈ U) : ContinuousAt g p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj g ?_
  refine (hg j _ ⟨(A.chart j).map_source hj, ?_⟩).continuousAt
  simpa [(A.chart j).left_inv hj] using hp

theorem continuousAt_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) {p : X} (hp : p ∈ U) : ContinuousAt f p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj f ?_
  have hmem : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hp⟩
  exact (hf j).continuousOn.continuousAt
    (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)

theorem zero_set_and_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  intro e X _ A L s hL hs x φ S μ v hφ hball hsrc hμ hv hv0 hsv

  have glue : ∀ y ∈ φ.target, ‖s x (φ.symm y)‖ * Real.exp (-L.φ x (φ.symm y)) =
      ‖s (φ.symm y) (φ.symm y)‖ * Real.exp (-L.φ (φ.symm y) (φ.symm y)) := fun y hy =>
    hs.2 x (φ.symm y) (φ.symm y) ⟨hsrc (φ.map_target hy), L.mem_U _⟩
  have hform : ∀ y ∈ φ.target, s x (φ.symm y) = v (φ.symm y) * ∏ i ∈ S, y i ^ μ i := by
    intro y hy
    rw [hsv _ (φ.map_target hy)]
    simp only [φ.right_inv hy]
  have hzero : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
    intro y hy
    have h1 : s (φ.symm y) (φ.symm y) = 0 ↔ s x (φ.symm y) = 0 := by
      have hg := glue y hy
      constructor
      · intro h0
        rw [h0] at hg
        simpa [Real.exp_ne_zero] using hg
      · intro h0
        rw [h0, norm_zero, zero_mul] at hg
        rcases mul_eq_zero.1 hg.symm with h | h
        · exact norm_eq_zero.1 h
        · exact absurd h (Real.exp_ne_zero _)
    change s (φ.symm y) (φ.symm y) = 0 ↔ _
    rw [h1, hform y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact absurd h (hv0 _ (φ.map_target hy))
      · exact ⟨i, hi, (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi))).1 h⟩
    · rintro ⟨i, hi, h⟩
      refine Or.inr ⟨i, hi, ?_⟩
      rw [h]
      exact zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))
  refine ⟨hzero, ?_⟩

  have hcont : ContinuousOn (fun y => -2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) φ.target := by
    intro y hy
    have hp := φ.map_target hy
    have cs : ContinuousAt φ.symm y := φ.continuousAt_symm hy
    have c1 : ContinuousAt (fun y => v (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm) (continuousAt_of_holoOn A hv hp) cs
    have c2 : ContinuousAt (fun y => L.φ x (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm)
        (continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (hsrc hp)) cs
    have c3 : ContinuousAt (fun y => Real.log ‖v (φ.symm y)‖) y :=
      c1.norm.log (norm_ne_zero_iff.2 (hv0 _ hp))
    exact ((continuousAt_const.mul c3).add (continuousAt_const.mul c2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin e → ℂ) 2).exists_bound_of_continuousOn
    (hcont.mono hball)
  refine ⟨C + |(∑ i ∈ S, (μ i : ℝ)) * Real.log 4|, fun y hy hnb => ?_⟩
  have hyt := hball hy
  have hnz : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 => hnb ((hzero y hyt).2 ⟨i, hi, h0⟩)
  have hs0 : s (φ.symm y) (φ.symm y) ≠ 0 := hnb
  have hvn : ‖v (φ.symm y)‖ ≠ 0 := norm_ne_zero_iff.2 (hv0 _ (φ.map_target hyt))
  have hlogS : Real.log (∏ i ∈ S, ‖y i‖ ^ μ i) = ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    rw [Real.log_prod (fun i hi => pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))]
    exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
  have hlog : logNormSec L s (φ.symm y) = Real.log ‖v (φ.symm y)‖ +
      ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x (φ.symm y) := by
    unfold logNormSec
    rw [← glue y hyt, hform y hyt, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (mul_ne_zero hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))) (Real.exp_ne_zero _),
      Real.log_mul hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi))), hlogS, Real.log_exp]
    ring
  have hloc : rLoc S μ y = Real.exp 1 + (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 -
      2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    unfold rLoc
    rw [Finset.sum_mul, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : ‖y i‖ ≠ 0 := norm_ne_zero_iff.2 (hnz i hi)
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hn), Real.log_pow]
    push_cast
    ring
  have hdiff : rW L s (φ.symm y) - rLoc S μ y =
      (-2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) -
        (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 := by
    unfold rW
    rw [hlog, hloc]
    ring
  rw [hdiff]
  have hb := hC y hy
  rw [Real.norm_eq_abs] at hb
  exact (abs_sub _ _).trans (add_le_add hb le_rfl)

end GlobalTheory.CompanionTheory.Ar.PB.LocalModel
end
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem continuous_normSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) :
    Continuous (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hS.1 x) (L.mem_U x)
  have hφ := LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (L.mem_U x)
  have hF : ContinuousAt (fun z => ‖s x z‖ * Real.exp (-L.φ x z)) x :=
    hc.norm.mul (Real.continuous_exp.continuousAt.comp hφ.neg)
  refine hF.congr ?_
  filter_upwards [(L.isOpen_U x).mem_nhds (L.mem_U x)] with z hz
  exact hS.2 x z z ⟨hz, L.mem_U z⟩

theorem isCompact_rW_sublevel : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ R : ℝ, IsCompact {y | y ∉ bdry s ∧ rW L s y ≤ R} := by
  intro e X _ _ _ A L s hL hS R
  have hset : {y | y ∉ bdry s ∧ rW L s y ≤ R} =
      {y | Real.exp ((Real.exp 1 - R) / 2) ≤ ‖s y y‖ * Real.exp (-L.φ y y)} := by
    ext y
    simp only [Set.mem_setOf_eq, bdry, rW, logNormSec]
    constructor
    · rintro ⟨h0, h1⟩
      have hpos : 0 < ‖s y y‖ * Real.exp (-L.φ y y) :=
        mul_pos (norm_pos_iff.2 h0) (Real.exp_pos _)
      exact (Real.le_log_iff_exp_le hpos).1 (by linarith)
    · intro h
      have hpos : 0 < ‖s y y‖ * Real.exp (-L.φ y y) := lt_of_lt_of_le (Real.exp_pos _) h
      have h0 : s y y ≠ 0 := by
        intro h0
        simp [h0] at hpos
      have h1 := (Real.le_log_iff_exp_le hpos).2 h
      exact ⟨h0, by linarith⟩
  rw [hset]
  exact (isClosed_le continuous_const (continuous_normSec A L s hL hS)).isCompact

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem bdry_isAnalyticSubset_interior_empty : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsSection A L s → IsSNC A L s m W → A.IsAnalyticSubset (bdry s) ∧ interior (bdry s) = ∅ := by
  intro e X _ A L s n m W hS hSNC
  refine ⟨?_, LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC⟩
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
  · rintro ⟨hzU, hz⟩
    exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

theorem isClosed_bdry_of_isSection : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  intro e X _ A L s hS
  exact ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry hS

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem levi_const_zero {D : ℕ} (y w : Fin D → ℂ) : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0 := by
  simp [levi]

theorem zeroMember_isRegFamily : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (C₅ C t₁ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₅ → 0 ≤ C → 0 < t₁ → t₁ ≤ Real.exp (-Real.exp 1) → IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧ IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) := by
  intro e X _ A Θ L s C₅ C t₁ hΘ hpos hL hC₅ hC ht₁ hte
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := fun y => by
    have := hL y; unfold rW; linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogr : ∀ y, 0 ≤ Real.log (rW L s y) := fun y => Real.log_nonneg (he1.trans (hr y))
  have hε : ∀ t, 0 < t → t ≤ t₁ → 0 ≤ epsT C t := by
    intro t ht htt
    rw [epsT_eq_mul]
    exact mul_nonneg hC (loglog_quot_nonneg ht (htt.trans hte))
  have hll : ∀ t, 0 < t → t ≤ t₁ → 1 ≤ Real.log (Real.log (1 / t)) :=
    fun t ht htt => (log_inv_bounds ht (htt.trans hte)).2
  have h0 : A.Smooth (0 : X → ℝ) := fun j => contDiffOn_const
  have ht1 : t₁ < 1 := by
    exact hte.trans_lt (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.exp_pos 1)))
  refine ⟨⟨isPotential_ofFun A 0 h0, fun j => contDiffOn_const, ?_, fun y _ => ⟨?_, hC₅⟩⟩,
    ⟨ht₁, ht1, fun t ht htt => ?_⟩, fun j K _ _ => ⟨fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
      fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
      fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩⟩
  · intro x j y _ w
    show 0 ≤ levi (fun z => (0 : X → ℝ) ((A.chart j).symm z) + (0 : X → ℝ) ((A.chart j).symm z)) y w
    simp only [Pi.zero_apply, add_zero]
    rw [levi_const_zero]
  · have := mul_nonneg hC₅ (hlogr y)
    show -C₅ * Real.log (rW L s y) ≤ 0
    linarith
  · have hεt := hε t ht htt
    have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨h0, fun _ => hC, fun _ _ => le_refl _, fun _ => ?_, ?_, fun _ _ _ => ?_, fun y _ => ?_,
      fun t' htt' ht' _ => ?_⟩
    · have := mul_nonneg hC (le_trans zero_le_one (hll t ht htt))
      show -C * Real.log (Real.log (1 / t)) ≤ 0
      linarith
    · intro x j y hy w
      obtain ⟨hyt, hyU⟩ := hy
      have hU : (A.chart j).symm y ∈ (Set.univ ∩ Set.univ) ∩ Θ.U x := hyU
      have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
      have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
        ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
      have hΘl : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
        by_cases hw : w = 0
        · rw [hw, levi_zero]
        · exact (hpos x j y ⟨hyt, hU.2⟩ w hw).le
      have hfun : (LocPot.ofFun 0 + LocPot.ofFun 0 + Θ.rsmul (epsT C t)).φ x ∘ (A.chart j).symm =
          fun z => (fun _ : Fin e → ℂ => (0 : ℝ)) z + epsT C t * (Θ.φ x ∘ (A.chart j).symm) z := by
        funext z
        show (0 : X → ℝ) _ + (0 : X → ℝ) _ + epsT C t * Θ.φ x _ = 0 + epsT C t * Θ.φ x _
        simp
      rw [hfun, levi_add_smul (epsT C t) contDiffAt_const hΘ2 w, levi_const_zero]
      exact add_nonneg le_rfl (mul_nonneg hεt hΘl)
    · show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t
      linarith
    · have := mul_nonneg hεt (le_trans (Real.exp_pos 1).le (hr y))
      show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t * rW L s y
      linarith
    · have := mul_nonneg hC (hε t' (ht.trans_le htt') ht')
      show (0 : ℝ) ≤ 0 + C * epsT C t'
      linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.EvPsh

theorem tendsto_epsT_zero (C : ℝ) :
    Tendsto (fun t => epsT C t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have hℓ : Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
    have h := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine h.congr (fun t => ?_)
    simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 := (hq.comp hℓ).const_mul C
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply, epsT]
  ring

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem eventually_isPsh_add_pot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  obtain ⟨ht₀, -, hF⟩ := hF
  have hε : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), epsT C t < 1 :=
    (tendsto_epsT_zero C).eventually (gt_mem_nhds one_pos)
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo 0 t₀ :=
    Ioo_mem_nhdsGT ht₀
  filter_upwards [hε, hsmall] with t hεt ht
  obtain ⟨h1, -, -, -, h5, -⟩ := hF t ht.1 ht.2.le
  refine ⟨h1, ?_⟩
  have h := GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ (isPsh_of_isPosPot A Θ hΘp) hth h1 hεt.le h5
  have e1 : Θ.rsmul 1 = Θ := by
    cases Θ
    simp [LocPot.rsmul]
  rwa [e1] at h

end GlobalTheory.CompanionTheory.Ar.Giv.EvPsh
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.levi_nonneg_in_chart_of_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B → IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) → (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  first | exact @GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase | exact GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase | (intros; apply GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.psh_add_psh_potential_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) (f : X → ℝ) (Θ : LocPot X), IsOpen U → IsPotential A P → IsPotential A Θ → A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) → IsPsh A Θ → IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | exact GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | (intros; apply GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh <;> assumption)
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.psh_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | exact GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | (intros; apply GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl <;> assumption)
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.snc_boundary_coordinate_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ x, ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.bdry_snc_chart | exact GlobalTheory.CompanionTheory.Metric.bdry_snc_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.bdry_snc_chart <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.psh_double_positive_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add <;> assumption)
end
