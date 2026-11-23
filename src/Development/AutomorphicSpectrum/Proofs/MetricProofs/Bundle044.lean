module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle040
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeFullRankSubmoduleBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem locExt_two_le : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

theorem locExt_isOpen_punct {n : ℕ} (R : ℝ) : IsOpen (punct (n := n) R) := by
  have h : punct (n := n) R = ⋂ i, ({z | z i ≠ 0} ∩ {z | ‖z i‖ < R}) := by
    ext z; simp [punct]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_ne_fun (continuous_apply i) continuous_const).inter
      (isOpen_lt (continuous_apply i).norm continuous_const)

theorem locExt_isOpen_nz {n : ℕ} (S : Finset (Fin n)) :
    IsOpen {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} := by
  have h : {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z | z i ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const

theorem locExt_core {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (hr : 0 < r) (Q : Set (Fin n → ℂ))
    (hQ : IsOpen Q) (hcov : ∀ z ∈ Metric.ball c r, (∀ i, z i ≠ c i) → z ∈ Q)
    (F : (Fin n → ℂ) → ℝ) (hsm : ∀ z ∈ Metric.ball c r ∩ Q, ContDiffAt ℝ ∞ F z)
    (hlevi : ∀ z ∈ Metric.ball c r ∩ Q, ∀ w, levi F z w = 0)
    (B : ℝ) (hB : ∀ z ∈ Metric.ball c r ∩ Q, |F z| ≤ B) :
    ∃ G : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ G (Metric.ball c (r / 2)) ∧
      ∀ z ∈ Metric.ball c (r / 2) ∩ Q, G z = F z := by
  set f : (Fin n → ℂ) → ℝ := fun w => F (c + w) with hf
  have hmem : ∀ w ∈ punct (n := n) r, c + w ∈ Metric.ball c r ∩ Q := by
    intro w hw
    have hb : c + w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (pi_norm_lt_iff hr).2 fun i => (hw i).2
    refine ⟨hb, hcov _ hb fun i => ?_⟩
    simpa using (hw i).1
  have hτ : ∀ w : Fin n → ℂ, ContDiffAt ℝ ∞ (fun w : Fin n → ℂ => c + w) w :=
    fun w => contDiffAt_const.add contDiffAt_id
  have hfsm : ∀ w ∈ punct (n := n) r, ContDiffAt ℝ ∞ f w :=
    fun w hw => ContDiffAt.comp w (hsm _ (hmem w hw)) (hτ w)
  have hharm : SepHarm r f := by
    refine GlobalTheory.T.levi_flat_separately_harmonic n f (punct r) (locExt_isOpen_punct r)
      (fun w hw => (hfsm w hw).contDiffWithinAt) ?_
    intro w hw v
    have hA : AnalyticAt ℂ (fun w : Fin n → ℂ => c + w) w := analyticAt_const.add analyticAt_id
    have h2 : ContDiffAt ℝ 2 F (c + w) := (hsm _ (hmem w hw)).of_le locExt_two_le
    have := levi_comp (φ := F) (τ := fun w : Fin n → ℂ => c + w) (z := w) v hA h2
    calc levi f w v = levi (F ∘ fun w : Fin n → ℂ => c + w) w v := rfl
      _ = 0 := by rw [this]; exact hlevi _ (hmem w hw) _
  have hfc : ContinuousOn f (punct r) :=
    fun w hw => (hfsm w hw).continuousAt.continuousWithinAt
  have hpo := GlobalTheory.T.polydisc_poisson_reproduces_harmonic n f (r / 2) r B (half_pos hr) (half_lt_self hr) hfc hharm
    (fun w hw => hB _ (hmem w hw))
  have htor : ∀ θ : Fin n → ℝ, torusPt (r / 2) θ ∈ punct (n := n) r := by
    intro θ i
    have hn : ‖torusPt (r / 2) θ i‖ = r / 2 := by
      simp only [torusPt]
      rw [norm_circleMap_zero, abs_of_pos (half_pos hr)]
    refine ⟨fun h0 => ?_, by rw [hn]; exact half_lt_self hr⟩
    rw [h0, norm_zero] at hn
    linarith
  have hcont : Continuous fun θ : Fin n → ℝ => f (torusPt (r / 2) θ) :=
    hfc.comp_continuous
      (continuous_pi fun i => (continuous_circleMap 0 _).comp (continuous_apply i)) htor
  have hG := GlobalTheory.T.polydisc_poisson_smooth n (r / 2) f (half_pos hr) hcont
  have hGc : ContDiffOn ℝ ∞ (fun z => polyPoisson (r / 2) f (z - c)) (Metric.ball c (r / 2)) := by
    refine ContDiffOn.comp (g := polyPoisson (r / 2) f) (f := fun z : Fin n → ℂ => z - c)
      (t := Metric.ball 0 (r / 2)) hG (contDiff_id.sub contDiff_const).contDiffOn ?_
    intro z hz
    simpa [dist_eq_norm] using hz
  refine ⟨fun z => polyPoisson (r / 2) f (z - c), hGc, ?_⟩
  have hT : Dense {z : Fin n → ℂ | ∀ i, z i ≠ c i} := by
    have h := (GlobalTheory.T.dense_coordinate_torus n).preimage (Homeomorph.subRight c).isOpenMap
    convert h using 1
    ext z
    simp [sub_ne_zero]
  have hD : IsOpen (Metric.ball c (r / 2) ∩ Q) := Metric.isOpen_ball.inter hQ
  have hsub : Metric.ball c (r / 2) ∩ Q ⊆ Metric.ball c r ∩ Q :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball (half_le_self hr.le))
  have heq : Set.EqOn (fun z => polyPoisson (r / 2) f (z - c)) F
      ((Metric.ball c (r / 2) ∩ Q) ∩ {z : Fin n → ℂ | ∀ i, z i ≠ c i}) := by
    intro z hz
    have hw : z - c ∈ punct (n := n) (r / 2) := by
      intro i
      refine ⟨sub_ne_zero.2 (hz.2 i), ?_⟩
      have h1 : ‖z - c‖ < r / 2 := by simpa [dist_eq_norm] using hz.1.1
      exact (norm_le_pi_norm (z - c) i).trans_lt h1
    simp only
    rw [hpo _ hw, hf]
    simp
  exact Set.EqOn.of_subset_closure heq
    (hGc.mono Set.inter_subset_left).continuousOn
    (fun z hz => (hsm z (hsub hz)).continuousAt.continuousWithinAt)
    Set.inter_subset_left (hT.open_subset_closure_inter hD)

theorem locExt : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  intro e X _ A L s nb m W hs hsnc th u M hth hu hP hPn hM x
  obtain ⟨ψ, hψ, hxψ, S, hbd⟩ := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hsnc x
  obtain ⟨hcl, -⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  let g₀ : X → ℝ := fun y => th.φ x y + u y
  let U' : Set X := th.U x ∩ (bdry s)ᶜ
  have hU' : IsOpen U' := (th.isOpen_U x).inter hcl.isOpen_compl
  have hsm0 : A.SmoothOn U' g₀ := fun j =>
    ((hth.1 x j).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  have hlz : ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U', ∀ w,
      levi (g₀ ∘ (A.chart j).symm) y w = 0 := by
    intro j y hy w
    have hmemP : y ∈ (A.chart j).target ∩
        (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u).U x ∩ (bdry s)ᶜ) :=
      ⟨hy.1, ⟨hy.2.1, trivial⟩, hy.2.2⟩
    have h1 : 0 ≤ levi (g₀ ∘ (A.chart j).symm) y w := hP x j y hmemP w
    have h2 : 0 ≤ levi (fun z => (-1 : ℝ) * (g₀ ∘ (A.chart j).symm) z) y w :=
      hPn x j y hmemP w
    have hc2 : ContDiffAt ℝ 2 (g₀ ∘ (A.chart j).symm) y :=
      ((hsm0 j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU').mem_nhds hy)).of_le
        locExt_two_le
    have h3 := levi_add_smul (f := fun _ => (0 : ℝ)) (-1) contDiffAt_const hc2 w
    simp only [zero_add] at h3
    rw [h3] at h2
    have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
    linarith
  have hO₁ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' th.U x) :=
    ψ.isOpen_inter_preimage_symm (th.isOpen_U x)
  have hcO₁ : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' th.U x :=
    ⟨ψ.map_source hxψ, by rw [Set.mem_preimage, ψ.left_inv hxψ]; exact th.mem_U x⟩
  let Q : Set (Fin e → ℂ) := {z | ∀ i ∈ S, z i ≠ 0}
  have hQ : IsOpen Q := locExt_isOpen_nz S
  let S' : Finset (Fin e) := S.filter fun i => ψ x i ≠ 0
  have hQ₂ : IsOpen {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} := locExt_isOpen_nz S'
  have hcQ₂ : ψ x ∈ {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} :=
    fun i hi => (Finset.mem_filter.1 hi).2
  obtain ⟨r, hr, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 ((hO₁.inter hQ₂).mem_nhds ⟨hcO₁, hcQ₂⟩)
  have hcov : ∀ z ∈ Metric.ball (ψ x) r, (∀ i, z i ≠ ψ x i) → z ∈ Q := by
    intro z hz hne i hi
    by_cases h0 : ψ x i = 0
    · rw [← h0]; exact hne i
    · exact (hball (Metric.ball_subset_closedBall hz)).2 i (Finset.mem_filter.2 ⟨hi, h0⟩)
  have hoff : ∀ z ∈ Metric.ball (ψ x) r ∩ Q, z ∈ ψ.target ∧ ψ.symm z ∈ U' := by
    intro z hz
    have hz1 := (hball (Metric.ball_subset_closedBall hz.1)).1
    refine ⟨hz1.1, hz1.2, fun hb => ?_⟩
    obtain ⟨i, hi, h0⟩ := (hbd _ (ψ.map_target hz1.1)).1 hb
    rw [ψ.right_inv hz1.1] at h0
    exact hz.2 i hi h0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (ψ x) r).exists_bound_of_continuousOn
    (f := th.φ x ∘ ψ.symm) fun z hz =>
      (GlobalTheory.T.smooth_in_compatible_chart e X A ψ (th.U x) (th.φ x) hψ (th.isOpen_U x) (hth.1 x) z (hball hz).1.1
        (hball hz).1.2).continuousAt.continuousWithinAt
  obtain ⟨G, hGs, hGe⟩ := locExt_core (ψ x) r hr Q hQ hcov (g₀ ∘ ψ.symm)
    (fun z hz => GlobalTheory.T.smooth_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 z (hoff z hz).1 (hoff z hz).2)
    (fun z hz => GlobalTheory.T.levi_zero_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 hlz z (hoff z hz).1 (hoff z hz).2)
    (C + M) (fun z hz => by
      have h1 := hC z (Metric.ball_subset_closedBall hz.1)
      have h2 := hM _ (hoff z hz).2.2
      rw [Real.norm_eq_abs] at h1
      exact (abs_add_le _ _).trans (add_le_add h1 h2))
  have hhalf : Metric.ball (ψ x) (r / 2) ⊆ Metric.closedBall (ψ x) r :=
    (Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall
  have hNU : ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2) ⊆ th.U x := by
    intro y hy
    have h := (hball (hhalf hy.2)).1.2
    rwa [Set.mem_preimage, ψ.left_inv hy.1] at h
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2), fun y => (G ∘ ψ) y - th.φ x y,
    ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hxψ, Metric.mem_ball_self (half_pos hr)⟩, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.smoothOn_of_chart_composition e X A ψ (Metric.ball (ψ x) (r / 2)) G hψ Metric.isOpen_ball
      (fun z hz => (hball (hhalf hz)).1.1) hGs
    exact (h1 j).sub ((hth.1 x j).mono fun y hy => ⟨hy.1, hNU hy.2⟩)
  · intro y hy hyb
    have hz : ψ y ∈ Metric.ball (ψ x) (r / 2) ∩ Q :=
      ⟨hy.2, fun i hi h0 => hyb ((hbd y hy.1).2 ⟨i, hi, h0⟩)⟩
    have h := hGe _ hz
    simp only [Function.comp_apply] at h ⊢
    rw [h, ψ.left_inv hy.1]
    simp [g₀]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem genFam_degree_over_subfield : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_degree

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem isGenFam_revInv_ite : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_revgen

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

section

noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

theorem le_of_mul_pow_mem_span_pow {O : Type*} [CommRing O] [IsDomain O] {p a : O} (hp : Prime p)
    (ha : ¬ p ∣ a) {k n : ℕ} (h : a * p ^ k ∈ Ideal.span {p} ^ n) : n ≤ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  by_contra hlt
  have hlt' : k + 1 ≤ n := by omega
  have h1 : p ^ (k + 1) ∣ a * p ^ k := (pow_dvd_pow p hlt').trans h
  rw [pow_succ, mul_comm a, mul_comm (p ^ k) p, mul_comm p] at h1
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).mp (by simpa [mul_comm] using h1))

theorem map_ptIdeal_eq_maximalIdeal_ordAff {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu x]
    exact not_not.mpr (RingHom.mem_ker.mp hx)
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have ha : eval t a = 0 := by
      by_contra ha
      have h1 := (hu a).mpr ha
      rw [← hab] at h1
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_mul_isUnit_left h1)
    obtain ⟨v, hv⟩ := (hu b).mpr hb
    have hx' : x = algebraMap _ (locRing I t) a * ((v⁻¹ : (locRing I t)ˣ) : locRing I t) := by
      rw [← hab, ← hv]
      simp
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exponent_eq_order_polynomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  intro m e I t r Jf g u mm hI hreg hdim hspan hg i hi n
  haveI := hreg
  haveI hdom : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  have hmax := map_ptIdeal_eq_maximalIdeal_ordAff I t hI
  have hspan' := hspan.trans hmax
  have hprime := prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnon := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hp : Prime (algebraMap _ (locRing I t) (r i)) := hprime i
  have hkill : ∀ h ∈ I, algebraMap _ (locRing I t) h = 0 := fun h hh =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
  constructor
  · rintro ⟨s, hs, hsg⟩
    have hs' : ¬ algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) s := fun h =>
      hs (Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr h))
    have hle : SncRes.Par.chPrime I t (r i) ^ n ⊔ I ≤
        (Ideal.span {algebraMap _ (locRing I t) (r i)} ^ n).comap (algebraMap _ (locRing I t)) := by
      refine sup_le ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono Ideal.map_comap_le n
      · intro h hh
        rw [Ideal.mem_comap, hkill h hh]
        exact zero_mem _
    have hmap := Ideal.mem_comap.mp (hle hsg)
    have hprod := Finset.mul_prod_erase Jf (fun j => algebraMap _ (locRing I t) (r j) ^ mm j) hi
    refine le_of_mul_pow_mem_span_pow hp (a := algebraMap _ (locRing I t) s *
      (u * ∏ j ∈ Jf.erase i, algebraMap _ (locRing I t) (r j) ^ mm j)) ?_ ?_
    · intro hd
      rcases hp.dvd_or_dvd hd with h | h
      · exact hs' h
      rcases hp.dvd_or_dvd h with h | h
      · exact hp.not_unit (isUnit_of_dvd_unit h u.isUnit)
      · obtain ⟨j, hj, hd'⟩ := (Prime.dvd_finsetProd_iff hp _).mp h
        have hd'' := hp.dvd_of_dvd_pow hd'
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        exact hnon i j hji.symm (hp.associated_of_dvd (hprime j) hd'')
    · rw [map_mul, hg, ← hprod] at hmap
      convert hmap using 1
      ring
  · intro hn
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t (u : locRing I t)
    have hz : algebraMap _ (locRing I t) (b * g - a * ∏ j ∈ Jf, r j ^ mm j) = 0 := by
      simp only [map_sub, map_mul, map_prod, map_pow]
      rw [hg, ← hab]
      ring
    obtain ⟨c, hc, hcI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
    refine ⟨c * b, ?_, ?_⟩
    · intro hmem
      have h1 : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (c * b) :=
        Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hmem)
      have h2 := (hu (c * b)).mpr (by rw [map_mul]; exact mul_ne_zero hc hb)
      exact hp.not_unit (isUnit_of_dvd_unit h1 h2)
    · have hri : r i ∈ SncRes.Par.chPrime I t (r i) :=
        Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
      have hpow : c * a * ∏ j ∈ Jf, r j ^ mm j ∈ SncRes.Par.chPrime I t (r i) ^ n := by
        apply Ideal.pow_le_pow_right hn
        obtain ⟨d, hd⟩ : r i ^ mm i ∣ ∏ j ∈ Jf, r j ^ mm j :=
          Finset.dvd_prod_of_mem (fun j => r j ^ mm j) hi
        rw [hd]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hri _))
      have hsplit : c * b * g = c * (b * g - a * ∏ j ∈ Jf, r j ^ mm j) +
          c * a * ∏ j ∈ Jf, r j ^ mm j := by ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hcI) (Ideal.mem_sup_left hpow)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem conePts_subset_mcPts_of_minimal {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) : conePts Q ⊆ mcPts P := fun _ hz =>
  ⟨hz.1, fun f hf => hz.2 _ (hQ.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem exists_minimal_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ∃ Q ∈ (cxIdeal P).minimalPrimes, z ∈ conePts Q := by
  have hz' : z ∈ conePts (cxIdeal P) := by rw [← mcPts_eq_conePts]; exact hz
  have hle : cxIdeal P ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) :=
    fun f hf => RingHom.mem_ker.2 (hz'.2 f hf)
  have : (RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, hQ, hz'.1, fun f hf => RingHom.mem_ker.1 (hQle hf)⟩

theorem mem_conePts_of_segre_eq {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (hs : segre z = segre z') : z' ∈ conePts Q := by
  classical
  choose i0 hi0 using hz.1
  obtain ⟨-, h4⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
  have hJ := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge.isMultiHomogIdeal_of_mem_minimalPrimes hP hQ
  have h5 := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z hz.2
  refine ⟨hz', fun f hf => ?_⟩
  rw [h4]
  exact h5 f hf

theorem isSheet_of_isSetSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet P Ψ y w γ :=
  ⟨h.1, h.2.mono fun _ h' => ⟨h'.1, conePts_subset_mcPts_of_minimal hQ h'.2.1, h'.2.2⟩⟩

theorem isSetSheet_of_isSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hone : ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q → z ∈ conePts Q' →
      Ψ (segre z) = Fin.cons 1 y → Q' = Q)
    (hw : w ∈ setFibre (conePts Q) Ψ y) (h : IsSheet P Ψ y w γ) :
    IsSetSheet (conePts Q) Ψ y w γ := by
  obtain ⟨z, hz, hzw, -⟩ := hw
  obtain ⟨hd, hm, hΨγ⟩ := h.2.self_of_nhds
  have hγQ : γ y ∈ conePts Q := mem_conePts_of_segre_eq hP hQ hz hm.1 (hzw.trans h.1.symm)
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hev : ∀ᶠ y' in 𝓝 y, ∀ Q' ∈ (cxIdeal P).minimalPrimes, Q' ≠ Q → γ y' ∉ conePts Q' := by
    refine (Filter.eventually_all_finite hfin).2 fun Q' hQ' => ?_
    by_cases hne : Q' = Q
    · exact Eventually.of_forall fun _ h' => absurd hne h'
    have hnot : γ y ∉ conePts Q' := fun hc => hne (hone Q' hQ' _ hγQ hc hΨγ)
    obtain ⟨f, hf, hf0⟩ : ∃ f ∈ Q', eval (γ y) f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨hm.1, hcon⟩
    have hc : ContinuousAt (fun y' => eval (γ y') f) y :=
      (MvPolynomial.continuous_eval f).continuousAt.comp hd.continuousAt
    filter_upwards [hc.eventually_ne hf0] with y' hy' _ hmem
    exact hy' (hmem.2 f hf)
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hev] with y' h1 h2
  obtain ⟨Q', hQ', hz'⟩ := exists_minimal_of_mem_mcPts h1.2.1
  by_cases hne : Q' = Q
  · subst hne
    exact ⟨h1.1, hz', h1.2.2⟩
  · exact absurd hz' (h2 Q' hQ' hne)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.IndexBound

theorem full_sublattice_normDegree_bounds : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  exact @CoverDenseAlt.normDegree_full_rank_submodule_bounds

end GlobalTheory.CompanionTheory.Ar.IndexBound
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.local_bruhat_cell_analytic_coordinates : ∀ (e N : ℕ) (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (x₀ : Fin e → ℂ), (∀ a b, AnalyticAt ℂ (fun x => g x a b) x₀) → (g x₀).BlockTriangular id → IsUnit (g x₀).det → ∃ (z : (Fin e → ℂ) → Pairs N → ℂ) (b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), AnalyticAt ℂ z x₀ ∧ (∀ p q, AnalyticAt ℂ (fun x => b x p q) x₀) ∧ z x₀ = 0 ∧ (∀ᶠ x in 𝓝 x₀, (b x).BlockTriangular id ∧ IsUnit (b x).det ∧ g x = cellMat N (z x) * b x) ∧ ∀ v, fderiv ℂ z x₀ v = 0 ↔ ((g x₀)⁻¹ * Matrix.of fun p q => fderiv ℂ (fun x => g x p q) x₀ v).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell | exact GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell <;> assumption)
end
