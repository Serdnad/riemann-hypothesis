module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle028
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
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle001
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holo_in_charts (e n : ℕ) (X : Type) [TopologicalSpace X]
    (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → X) (w₀ : Fin e → ℂ)
    (W : Set X) (f : X → ℂ) (hUn : IsOpen Un) (hw₀ : w₀ ∈ Un) (hc : ContinuousOn bp Un)
    (hb : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source))
    (_hW : IsOpen W) (hwW : bp w₀ ∈ W) (hf : A.HoloOn W f) : AnalyticAt ℂ (f ∘ bp) w₀ := by
  obtain ⟨k, hk⟩ := A.cover (bp w₀)
  have hca : ContinuousAt bp w₀ := hc.continuousAt (hUn.mem_nhds hw₀)
  have h1 : AnalyticAt ℂ (A.chart k ∘ bp) w₀ := hb k w₀ ⟨hw₀, hk⟩
  have h2 : AnalyticAt ℂ (f ∘ (A.chart k).symm) ((A.chart k ∘ bp) w₀) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (bp w₀)) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hwW
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hev : ∀ᶠ w in 𝓝 w₀, bp w ∈ (A.chart k).source :=
    hca ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart k).left_inv hw]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_comp_of_analytic_in_charts :
    ∀ (e n : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ))
      (bp : (Fin e → ℂ) → X) (W : Set X) (f : X → ℝ), IsOpen Un → ContinuousOn bp Un →
      (∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source)) →
      (∀ w ∈ Un, bp w ∈ W) → A.SmoothOn W f →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) Un := by
  intro e n X _ A Un bp W f hUn hbp hana hW hf w hw
  obtain ⟨k, hk⟩ := A.cover (bp w)
  have hV : IsOpen (Un ∩ bp ⁻¹' (A.chart k).source) :=
    hbp.isOpen_inter_preimage hUn (A.chart k).open_source
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) :=
    ((hana k).contDiffOn hV.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf k
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ bp))
      (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h2.comp h1 ?_
    intro x hx
    refine ⟨(A.chart k).map_source hx.2, ?_⟩
    show (A.chart k).symm (A.chart k (bp x)) ∈ W
    rw [(A.chart k).left_inv hx.2]
    exact hW x hx.1
  have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h3.congr ?_
    intro x hx
    simp only [Function.comp_apply, (A.chart k).left_inv hx.2]
  exact (h4.contDiffAt (hV.mem_nhds ⟨hw, hk⟩)).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord

theorem holoMap_of_coord : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  intro e n X Y _ _ A B pr hloc
  have key : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧
        pr x' = (B.chart kb).symm (fun i => ψ x' (σ i)) ∧ (fun i => ψ x' (σ i)) ∈ (B.chart kb).target := by
    intro x
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := hloc x
    refine ⟨ψ, kb, σ, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨hs, hc⟩ := h x' hx'
    have hfun : (fun i => ψ x' (σ i)) = B.chart kb (pr x') := funext fun i => (hc i).symm
    refine ⟨hs, ?_, ?_⟩
    · rw [hfun, (B.chart kb).left_inv hs]
    · rw [hfun]
      exact (B.chart kb).map_source hs
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ψ, kb, σ, -, hx, h⟩ := key x
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have hcont : ContinuousOn ((B.chart kb).symm ∘ L ∘ ψ) ψ.source :=
      (B.chart kb).continuousOn_symm.comp (L.continuous.comp_continuousOn ψ.continuousOn)
        (fun x' hx' => (h x' hx').2.2)
    have heq : ((B.chart kb).symm ∘ L ∘ ψ) =ᶠ[𝓝 x] pr :=
      Filter.eventually_of_mem (ψ.open_source.mem_nhds hx) fun x' hx' => ((h x' hx').2.1).symm
    exact (hcont.continuousAt (ψ.open_source.mem_nhds hx)).congr heq
  · intro j k y hy
    obtain ⟨hyt, hys⟩ := hy
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := key ((A.chart j).symm y)
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hx⟩
    have h2 : AnalyticAt ℂ (B.chart k ∘ (B.chart kb).symm) (L (ψ ((A.chart j).symm y))) := by
      apply B.holo kb k
      refine ⟨(h _ hx).2.2, ?_⟩
      show (B.chart kb).symm (fun i => ψ ((A.chart j).symm y) (σ i)) ∈ (B.chart k).source
      rw [← (h _ hx).2.1]
      exact hys
    have h3 : AnalyticAt ℂ ((B.chart k ∘ (B.chart kb).symm) ∘ L ∘ (ψ ∘ (A.chart j).symm)) y :=
      AnalyticAt.comp (f := L ∘ (ψ ∘ (A.chart j).symm)) h2
        (AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) (L.analyticAt _) h1)
    apply h3.congr
    have hnb : ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ ψ.source :=
      (A.chart j).continuousAt_symm hyt (ψ.open_source.mem_nhds hx)
    filter_upwards [hnb] with y' hy'
    simp only [Function.comp_apply]
    rw [(h _ hy').2.1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

theorem chart_swap_keep :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ (∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i) ∧ ∀ y ∈ ψ'.source, ∀ i, (∀ l, σ l ≠ i) → ψ' y i = ψ y i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]
  · intro y _ i hi
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) i = ψ y i
    exact Function.extend_apply' _ _ _ (fun ⟨l, hl⟩ => hi l hl)

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end
