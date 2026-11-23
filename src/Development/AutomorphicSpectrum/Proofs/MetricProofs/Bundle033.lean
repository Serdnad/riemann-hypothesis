module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ExpandMInt

theorem expand_mInt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (g : X → ℝ), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g := by
  intro e X _ _ _ A U P f Θ g hU hnull hP hΘ hf hT

  have hae : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ (A.chart j).target →
      locDens A (fun i => P i + LocPot.ofFun (f i)) j y =
        ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
          locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
    intro j
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) (hnull j)
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    refine ⟨hy.1, fun hyU => hy.2 ?_⟩
    exact GlobalTheory.T.local_density_inclusion_exclusion A U P f Θ hU hP hΘ hf j y ⟨hy.1, hyU⟩
  refine ⟨?_, ?_⟩
  · intro j K hK hKc
    have hsum : IntegrableOn (fun y => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        (g ((A.chart j).symm y) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y)) K :=
      integrable_finsetSum _ fun T _ => (hT T j K hK hKc).const_mul _
    refine hsum.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (hae j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  · unfold mInt
    split_ifs with h
    · unfold integralWith
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun T _ => (integrableOn_weight A h.some _ g (hT T) j).const_mul _]
      refine setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      rw [hy hyt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      ring
    · simp

end GlobalTheory.CompanionTheory.Metric.ExpandMInt
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.compatible_chart_product_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap | exact GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.exists_snc_adapted_chart_at_point : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form | exact GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {D e : ℕ} (R : AnLogRes P ⊤ D) {Y : Type*} [TopologicalSpace Y]
  (B : FinHolAtlas e Y) {V : Y → Set Y} {μ : Y → Y → (Σ k, ι k) → ℂ} {h : Y → R.X}

theorem continuous_of_orbit_of_ne (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro F hF
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (F.map h) (by simp)
  have hth : Tendsto h F (𝓝 x) := hx
  have hUx : ∀ᶠ y' in (F : Filter Y), h y' ∈ R.U x := hth ((R.isOpen_U x).mem_nhds (R.mem_U x))
  have hVy : ∀ᶠ y' in (F : Filter Y), y' ∈ V y := hF ((hVo y).mem_nhds (hVm y))
  have hcr : ∀ k (i i' : ι k), R.lift x x ⟨k, i⟩ * μ y y ⟨k, i'⟩ =
      R.lift x x ⟨k, i'⟩ * μ y y ⟨k, i⟩ := by
    intro k i i'
    have t1 : ∀ q, Tendsto (fun y' => R.lift x (h y') q) F (𝓝 (R.lift x x q)) := fun q =>
      (Proj.continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hth
    have t2 : ∀ q, Tendsto (fun y' => μ y y' q) F (𝓝 (μ y y q)) := fun q =>
      (Proj.continuousAt_of_holoOn B (hμ y q) (hVm y)).tendsto.mono_left hF
    refine tendsto_nhds_unique ((t1 ⟨k, i⟩).mul (t2 ⟨k, i'⟩))
      (((t1 ⟨k, i'⟩).mul (t2 ⟨k, i⟩)).congr' ?_)
    filter_upwards [hUx, hVy] with y' h1 h2
    exact Proj.orbit_cross (Proj.local_orbit R hVm hc hh h1 h2) k i' i
  have hxy : SameOrbit (R.lift x x) (μ y y) :=
    Proj.orbit_of_cross (R.mem x x (R.mem_U x)).1 (hne y) hcr
  have hxe : x = h y :=
    R.inj x (h y) (Proj.not_mem_mcPts_top _) (Proj.orbit_trans hxy (Proj.orbit_symm (hh y)))
  rw [← hxe]
  exact hx

end Orbit

theorem holoMap_of_local_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  intro K _ ι _ K' _ ι' _ P J P' J' D D' R R' g hJ hg
  subst hJ
  choose Vs f hVs hxV hf hcomp using hg
  have hcl : ∀ y, ContinuousOn (R'.lift y) (R'.U y) := fun y =>
    continuousOn_pi.2 fun p x hx =>
      (Proj.continuousAt_of_holoOn R'.A (R'.holo y p) hx).continuousWithinAt
  let V : R'.X → Set R'.X := fun y => R'.U y ∩ R'.lift y ⁻¹' Vs y
  let μ : R'.X → R'.X → (Σ k, ι k) → ℂ := fun y u => f y (R'.lift y u)
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (hcl y).isOpen_inter_preimage (R'.isOpen_U y) (hVs y)
  have hVm : ∀ y, y ∈ V y := fun y => ⟨R'.mem_U y, hxV y⟩
  have hμ : ∀ y q, R'.A.HoloOn (V y) fun u => μ y u q := by
    rintro y q j w ⟨hw, hwV⟩
    have h1 : AnalyticAt ℂ (fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.pi fun p => R'.holo y p j w ⟨hw, hwV.1⟩
    have h2 : AnalyticAt ℂ (f y ∘ fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.comp (hf y _ hwV.2) h1
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt _ |>.comp h2
  have hor : ∀ y, ∀ u ∈ V y, SameOrbit (μ y u) (R.lift (g u) (g u)) := fun y u hu =>
    hcomp y _ ⟨hu.2, R'.mem y u hu.1⟩ u (R'.compat y u u ⟨hu.1, R'.mem_U u⟩)
  have hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u) := fun y y' u hu =>
    Proj.orbit_trans (hor y u hu.1) (Proj.orbit_symm (hor y' u hu.2))
  have hh : ∀ y, SameOrbit (R.lift (g y) (g y)) (μ y y) := fun y =>
    Proj.orbit_symm (hor y y (hVm y))
  have hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (g y) (g y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous g := continuous_of_orbit_of_ne R R'.A hVo hVm hμ hne hc hh
  exact ⟨hcont, Proj.analytic_of_orbit R R'.A hVo hVm hμ hc hh hcont⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

end

section

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.mixed_integral_inclusion_exclusion_alt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (g : X → ℝ), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g := by
  first | exact @GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt | exact GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt | (intros; apply GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt <;> assumption)

end
end
