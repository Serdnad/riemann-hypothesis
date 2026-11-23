module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.OfListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.SignedConv

theorem zero_member {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (C₅ C t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hC₅ : 0 ≤ C₅) (hC : 0 ≤ C) (ht₁ : 0 < t₁)
    (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧
      IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) :=
  GlobalTheory.T.zero_weight_regular_family A Θ L s C₅ C t₁ hΘ hΘp hs hC₅ hC ht₁ hte

theorem eventually_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) :=
  GlobalTheory.T.regular_family_eventually_smooth_psh A Θ L s th ph phT C t₀ hΘ hΘp hth hF

theorem isPshOn_add_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X)
    (P : LocPot X) (f : X → ℝ) (Θ : LocPot X) (hU : IsOpen U) (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hf : A.SmoothOn U f) (hPf : IsPshOn A U (P + LocPot.ofFun f))
    (hΘp : IsPsh A Θ) : IsPshOn A U (P + LocPot.ofFun f + Θ) :=
  GlobalTheory.T.psh_add_psh_potential_on_open A U P f Θ hU hP hΘ hf hPf hΘp

theorem expand_mInt {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X)
    (g : X → ℝ) (hU : IsOpen U) (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0)
    (hP : ∀ i, IsPotential A (P i)) (hΘ : IsPotential A Θ) (hf : ∀ i, A.SmoothOn U (f i))
    (hT : ∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
      LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) :
    MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧
      mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g :=
  GlobalTheory.T.mixed_integral_inclusion_exclusion_alt A U P f Θ g hU hnull hP hΘ hf hT

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem isPshOn_of_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (P : LocPot X) (h : IsPsh A P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1⟩ w

theorem smoothOn_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (h : A.Smooth f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ U)))

theorem isSingWeight_abs {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (h : IsSingWeight A L s th ph C₅) :
    IsSingWeight A L s th ph |C₅| := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨a, b⟩ := h4 y hy
  have hr : 1 ≤ Real.log (rW L s y) := by
    have h5 := rW_ge L s hs y
    have h6 := Real.log_le_log (Real.exp_pos 1) h5
    rwa [Real.log_exp] at h6
  have h7 := mul_nonneg (sub_nonneg.2 (le_abs_self C₅)) (le_trans zero_le_one hr)
  exact ⟨by nlinarith, b.trans (le_abs_self _)⟩

theorem chart_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s)
    (hSNC : IsSNC A L s m W) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜᶜ) = 0 := by
  rw [compl_compl]
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have := analyticNull A (bdry s) hAn (LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC) j
  rwa [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this

theorem convergenceSigned : ConvergenceSignedStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hS hSNC hs th ph phT C₅ C t₀ hSW hRF hC2 g gT C₆
    hgc hgb hlim
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  have hUo : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  have hnull := chart_null A L s m W hS hSNC
  have hmem : ∀ T : Finset (Fin e),
      (∀ i, IsSingWeight A L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) |C₅|) ∧
      (∀ i, IsRegFamily A Θ L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0) |C|
        (min t₀ (Real.exp (-Real.exp 1)))) ∧
      (∀ i, IsRegFamilyC2 A s (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0)) := by
    intro T
    have hz : ∀ i : Fin e, IsSingWeight A L s (LocPot.ofFun 0) 0 |C₅| ∧
        IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) |C| (min t₀ (Real.exp (-Real.exp 1))) ∧
        IsRegFamilyC2 A s 0 (fun _ => 0) := fun i =>
      zero_member A Θ L s |C₅| |C| _ hΘ hΘp hs (abs_nonneg _) (abs_nonneg _)
        (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_right _ _)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ T <;>
      simp only [hi, ↓reduceIte]
    · exact isSingWeight_abs A L s _ _ _ hs (hSW i)
    · exact (hz i).1
    · exact isRegFamily_mono A Θ L s (th i) (ph i) (phT i) C t₀ |C| _ hΘ hΘpsh (hSW i).1 hs (hRF i)
        le_rfl (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_left _ _) (min_le_right _ _)
    · exact (hz i).2.1
    · exact hC2 i
    · exact (hz i).2.2
  have hconv := fun T : Finset (Fin e) => GlobalTheory.T.convergence_statement_holds A Θ L s m W hΘ hΘp hL hS hSNC hs
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
    (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    g gT C₆ hgc hgb hlim
  have hgcont : ContinuousOn g (bdry s)ᶜ := hlim.continuousOn (Eventually.of_forall hgc).frequently
  have hlimT := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A (bdry s)ᶜ
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ ((hmem T).1 i).2.1
      ((hmem T).1 i).2.2.1 hΘpsh) g hgcont (hconv T).2.2.1
  have hexpL := expand_mInt A (bdry s)ᶜ th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => (hSW i).2.1) (fun T => (hlimT T).1)
  refine ⟨hexpL.1, ?_⟩
  rw [hexpL.2]
  have htend : Tendsto (fun t => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
      ∫ y, gT t y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        mInt A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ) g)) := by
    refine tendsto_finsetSum _ fun T _ => ?_
    rw [(hlimT T).2]
    exact ((hconv T).2.2.2.2).const_mul _
  refine htend.congr' ?_
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable (gT t) (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.2.2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  filter_upwards [hev] with t ht
  have hmt := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A (bdry s)ᶜ
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
    (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) (gT t) (hgc t) (ht.2 T).2
  rw [(expand_mInt A (bdry s)ᶜ th (fun i => phT i t) Θ (gT t) hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)).2]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [(hmt T).2]

end GlobalTheory.CompanionTheory.Ar.Giv.SignedConv
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_bdry_null_any {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hS : IsSection A L s) (hSNC : IsSNC A L s m W) (Φ : Fin e → LocPot X) :
    maMeasure A Φ (bdry s) = 0 := by
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have hInt : interior (bdry s) = ∅ := LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC
  unfold maMeasure
  split_ifs with h
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hT]
    have := analyticNull A (bdry s) hAn hInt j
    rw [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this
    rwa [Set.inter_comm]
  · simp

theorem unifInt_holds : UnifIntStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘpos hL hs hsnc hsle L' v Dg hL' hv hvsnc hsvsnc hvle
    th ph phT C₅ C t₀ hsing hreg hC2
  dsimp only
  have hconv := GlobalTheory.T.convergence_statement_holds A Θ L s m W hΘ hΘpos hL hs hsnc hsle th ph phT C₅ C t₀ hsing hreg hC2
  have hlog1 : ∀ y, 1 ≤ Real.log (rW L s y) := by
    intro y
    have h := rW_ge L s hsle y
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (rW L s y) := Real.log_le_log (Real.exp_pos 1) h
  have hunif : ∀ g : X → ℝ,
      TendstoLocallyUniformlyOn (fun (_ : ℝ) => g) g (𝓝[>] (0 : ℝ)) (bdry s)ᶜ := by
    intro g u hu x _
    exact ⟨Set.univ, Filter.univ_mem,
      Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hweak : ∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) →
      Tendsto (fun t => ∫ y, g y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))
        (𝓝[>] 0) (𝓝 (∫ y, g y ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ))) := by
    intro g B hg hB
    have hb : ∀ (t : ℝ) (y : X), y ∉ bdry s →
        |(fun (_ : ℝ) => g) t y| ≤ B * Real.log (rW L s y) := by
      intro t y _
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB y)
      calc |g y| ≤ B := hB y
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * Real.log (rW L s y) := mul_le_mul_of_nonneg_left (hlog1 y) hB0
    have h := hconv g (fun _ => g) B (fun _ => hg.continuousOn) hb (hunif g)
    dsimp only at h
    exact h.2.2.2.2
  have hone : ∀ (t : ℝ) (y : X), y ∉ bdry s →
      |(fun (_ : ℝ) (_ : X) => (1 : ℝ)) t y| ≤ 1 * Real.log (rW L s y) := by
    intro t y _
    simpa using hlog1 y
  have h1 := hconv (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const) hone (hunif _)
  dsimp only at h1
  have hμfin : IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) := h1.1
  have hμTfin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) := by
    filter_upwards [h1.2.2.2.1] with t ht
    exact (integrable_const_iff.1 ht).resolve_left one_ne_zero
  have hzero : {y | GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y = 0} = bdry v := by
    ext y
    simp [GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm, bdry, Real.exp_ne_zero]
  have hnull : ∀ Φ : Fin e → LocPot X,
      maMeasure A Φ {y | GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y = 0} = 0 := by
    intro Φ
    rw [hzero]
    exact maMeasure_bdry_null_any A L' v ![1] ![Dg] hv hvsnc Φ
  have hbd : ∀ y, 0 ≤ GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y ∧
      GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y ≤ 1 := by
    intro y
    have h0 : 0 ≤ GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y :=
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    refine ⟨h0, ?_⟩
    by_contra hlt
    have hpos := Real.log_pos (not_le.1 hlt)
    have h2 : logNormSec L' v y = Real.log (GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y) := rfl
    linarith [hvle y]
  cases e with
  | zero =>
    have hfin : Finite X := by
      have hsub : ∀ j, (A.chart j).source.Subsingleton := fun j x hx y hy =>
        (A.chart j).injOn hx hy (Subsingleton.elim _ _)
      have hU : (⋃ j, (A.chart j).source).Finite := Set.finite_iUnion fun j => (hsub j).finite
      have hcov : (Set.univ : Set X) ⊆ ⋃ j, (A.chart j).source := fun x _ =>
        Set.mem_iUnion.2 (A.cover x)
      exact Set.finite_univ_iff.1 (hU.subset hcov)
    have hμeq : ∀ t, maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) =
        maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) := fun t =>
      congrArg _ (Subsingleton.elim _ _)
    have hint : Integrable (fun y => -logNormSec L' v y)
        (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) := Integrable.of_finite
    simp only [hμeq]
    exact ⟨hint, Filter.Eventually.of_forall fun _ => hint, tendsto_const_nhds⟩
  | succ e =>
    have hsmall := GlobalTheory.T.mixed_measure_convergence_snc GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.full
      GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds A Θ L s m W hΘ hΘpos hL hs hsnc hsle L' v Dg hL' hv hvsnc
      hsvsnc th ph phT C₅ C t₀ hsing hreg
    exact GlobalTheory.T.weak_convergence_off_zero_set (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ))
      (fun t => maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))
      (GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v) hμfin hμTfin
      (GroundTheory.Heights₂.Heights.AnalyticLimit.continuous_secNorm A L' v hL' hv) hbd (hnull _)
      (Filter.Eventually.of_forall fun t => hnull _) hweak hsmall

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Inverse

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem notMem_mcPts_top_inv (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have h1 := h.2 1 trivial
  simp at h1

theorem minors_of_sameOrbit_inv {a z : (Σ k, ι k) → ℂ} (h : SameOrbit a z) (k : K) (i i' : ι k) :
    a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  show c k * z ⟨k, i⟩ * z ⟨k, i'⟩ = c k * z ⟨k, i'⟩ * z ⟨k, i⟩
  ring

theorem sameOrbit_of_minors_inv {a z : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (i i' : ι k), a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩) : SameOrbit a z := by
  choose q hq using hz
  refine ⟨fun k => a ⟨k, q k⟩ / z ⟨k, q k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := ha k
    refine div_ne_zero (fun h0 => hi ?_) (hq k)
    have h1 := h k i (q k)
    rw [h0, zero_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hq k)
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, q k⟩ / z ⟨k, q k⟩ * z ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hq k)]
    exact h k i (q k)

end Inverse

theorem exists_continuousOn_inv_pts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X →
    ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧
      ContinuousOn r (mcPts P) := by
  intro K _ ι _ P e R hX
  have hs : ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (notMem_mcPts_top_inv z)
  choose! r hr using hs
  refine ⟨r, hr, fun z₀ hz₀ => ?_⟩
  refine isCompact_univ.le_nhds_of_unique_clusterPt (by simp) fun x' _ hx' => ?_
  obtain ⟨G, hG, hGr⟩ := mapClusterPt_iff_ultrafilter.mp hx'
  have hUx : R.U x' ∈ 𝓝 x' := (R.isOpen_U x').mem_nhds (R.mem_U x')
  have hGS : ∀ᶠ z in (G : Filter _), z ∈ mcPts P := hG self_mem_nhdsWithin
  have hGU : ∀ᶠ z in (G : Filter _), r z ∈ R.U x' := hGr hUx
  have hGz : (G : Filter _) ≤ 𝓝 z₀ := hG.trans nhdsWithin_le_nhds
  have hmin : ∀ᶠ z in (G : Filter _), SameOrbit (R.lift x' (r z)) z := by
    filter_upwards [hGS, hGU] with z h1 h2
    exact orbit_trans (R.compat x' (r z) (r z) ⟨h2, R.mem_U _⟩) (hr z h1)
  have ha : ∀ p, Tendsto (fun z => R.lift x' (r z) p) (G : Filter _) (𝓝 (R.lift x' x' p)) :=
    fun p => (((continuousOn_lift R x' p).continuousAt hUx).tendsto).comp hGr
  have hzc : ∀ p, Tendsto (fun z : (Σ k, ι k) → ℂ => z p) (G : Filter _) (𝓝 (z₀ p)) :=
    fun p => ((continuous_apply p).tendsto z₀).comp hGz
  have hsame : SameOrbit (R.lift x' x') z₀ :=
    sameOrbit_of_minors_inv (R.mem x' x' (R.mem_U x')).1 hz₀.1 fun k i i' =>
      tendsto_nhds_unique_of_eventuallyEq ((ha _).mul (hzc _)) ((ha _).mul (hzc _))
        (hmin.mono fun z hz => minors_of_sameOrbit_inv hz k i i')
  exact R.inj x' (r z₀) (notMem_mcPts_top_inv _) (orbit_trans hsame (orbit_symm (hr z₀ hz₀)))

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end
