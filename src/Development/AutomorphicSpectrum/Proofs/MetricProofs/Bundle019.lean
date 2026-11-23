module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001

@[expose] public section

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem contDiffAt_comp_compatChart_symm :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
      (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ),
      IsCompatChart A ψ → IsOpen U → A.SmoothOn U g →
        ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  intro e X _ A ψ U g hψ hU hg z hz hzU
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hτ : ContDiffAt ℝ ∞ (⇑(A.chart j) ∘ ⇑ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt).restrict_scalars ℝ
  have hy : (A.chart j) (ψ.symm z) ∈ (A.chart j).target ∩ ⇑(A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ.symm z)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hzU
  have hgc : ContDiffAt ℝ ∞ (g ∘ ⇑(A.chart j).symm) ((A.chart j) (ψ.symm z)) :=
    (hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hcomp := hgc.comp z hτ
  apply hcomp.congr_of_eventuallyEq
  have hev : ∀ᶠ w in 𝓝 z, ψ.symm w ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]

end GlobalTheory.CompanionTheory.Metric
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothGlue

theorem continuousAt_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {N : Set X} {E : X → ℝ} (hN : IsOpen N) (hS : A.SmoothOn N E) {p : X} (hp : p ∈ N) :
    ContinuousAt E p := by
  obtain ⟨j, hj⟩ := A.cover p
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) :=
    (A.chart j).isOpen_inter_preimage_symm hN
  have hz : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hp
  have h1 : ContinuousAt (E ∘ (A.chart j).symm) (A.chart j p) :=
    ((hS j).continuousOn).continuousAt (hopen.mem_nhds hz)
  have h2 : ContinuousAt (A.chart j) p := (A.chart j).continuousAt hj
  have h1' : ContinuousAt (E ∘ (A.chart j).symm) ((A.chart j) p) := h1
  have h3 : ContinuousAt ((E ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp h1' h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem eq_of_dense_compl {X : Type} [TopologicalSpace X] {B W : Set X} {f g : X → ℝ}
    (hD : Dense Bᶜ) (hW : IsOpen W) (hf : ∀ p ∈ W, ContinuousAt f p)
    (hg : ∀ p ∈ W, ContinuousAt g p) (hfg : ∀ y ∈ W, y ∉ B → f y = g y) :
    ∀ y ∈ W, f y = g y := by
  intro y hy
  by_contra hne
  have hc : ContinuousAt (fun w => f w - g w) y := (hf y hy).sub (hg y hy)
  have hev : ∀ᶠ w in 𝓝 y, f w - g w ≠ 0 := hc.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨w, hwB, hw1, hw2⟩ := hD.inter_nhds_nonempty (hev.and (hW.mem_nhds hy))
  exact hw1 (sub_eq_zero.mpr (hfg w hw2 hwB))

theorem glue : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  intro e X _ A B u _ hD h
  classical
  choose N E hN hx hS hE using h
  have hagree : ∀ x y, ∀ w ∈ N x ∩ N y, E x w = E y w := by
    intro x y
    refine eq_of_dense_compl hD ((hN x).inter (hN y))
      (fun p hp => continuousAt_of_smoothOn A (hN x) (hS x) hp.1)
      (fun p hp => continuousAt_of_smoothOn A (hN y) (hS y) hp.2) ?_
    intro w hw hwB
    rw [hE x w hw.1 hwB, hE y w hw.2 hwB]
  refine ⟨fun y => if y ∈ B then E y y else u y, ?_, ?_⟩
  · have hu' : ∀ x, ∀ y ∈ N x, (if y ∈ B then E y y else u y) = E x y := by
      intro x y hy
      by_cases hB : y ∈ B
      · rw [if_pos hB]
        exact hagree y x y ⟨hx y, hy⟩
      · rw [if_neg hB]
        exact (hE x y hy hB).symm
    intro j z hz
    have hzt : z ∈ (A.chart j).target := hz.1
    set x := (A.chart j).symm z with hxdef
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N x) :=
      (A.chart j).isOpen_inter_preimage_symm (hN x)
    have hzm : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N x := ⟨hzt, hx x⟩
    have hc : ContDiffAt ℝ ∞ (E x ∘ (A.chart j).symm) z :=
      (hS x j).contDiffAt (hopen.mem_nhds hzm)
    refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hopen.mem_nhds hzm] with w hw
    exact hu' x _ hw.2
  · intro y hy
    simp [hy]

end GlobalTheory.CompanionTheory.SmoothGlue
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem smoothOn_comp_compatChart (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ)
    (hψ : IsCompatChart A ψ) (hO : IsOpen O) (_hOt : O ⊆ ψ.target)
    (hG : ContDiffOn ℝ ∞ G O) : A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  intro j y hy
  obtain ⟨hyt, hys, hyO⟩ := hy
  have han : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hys⟩
  have hτ : ContDiffAt ℝ ∞ (ψ ∘ (A.chart j).symm) y :=
    (han.restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
  have hGat : ContDiffAt ℝ ∞ G ((ψ ∘ (A.chart j).symm) y) :=
    hG.contDiffAt (hO.mem_nhds hyO)
  exact (hGat.comp y hτ).contDiffWithinAt

theorem smoothOn_comp_compatChart' : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) :=
  fun e X _ A ψ O G h1 h2 h3 h4 => smoothOn_comp_compatChart e X A ψ O G h1 h2 h3 h4

end GlobalTheory.CompanionTheory.Metric
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_eq_zero_of_compatChart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ →
    IsOpen U → A.SmoothOn U g →
    (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w,
      levi (g ∘ (A.chart j).symm) y w = 0) →
    ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  intro e X _ A ψ U g hψ hU hg hA z hz hzU w
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hzs : z ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := ⟨hz, hj⟩
  have hopen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart j).open_source
  have hτ : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) z := (hψ j).2 z hzs
  have hEq : g ∘ ⇑ψ.symm =ᶠ[𝓝 z] (g ∘ ⇑(A.chart j).symm) ∘ (⇑(A.chart j) ∘ ⇑ψ.symm) := by
    filter_upwards [hopen.mem_nhds hzs] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy.2]
  have hcz : (⇑(A.chart j) ∘ ⇑ψ.symm) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, Function.comp_apply, (A.chart j).left_inv hj]
    exact hzU
  have hopen2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  have hsm : ContDiffAt ℝ 2 (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) z) :=
    ((hg j).contDiffAt (hopen2.mem_nhds hcz)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  rw [levi_congr hEq w, levi_comp w hτ hsm]
  exact hA j _ hcz _

end GlobalTheory.CompanionTheory.LeviChart
end
