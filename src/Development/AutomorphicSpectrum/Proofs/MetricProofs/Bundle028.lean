module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusion
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
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalForm

theorem holoOn_coord {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := by
  intro j z hz
  exact (analyticAt_pi_iff.1 ((hψ j).1 z hz)) i

theorem exists_local_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  intro e X _ A L s nb m W hsnc x
  obtain ⟨ψ, hψ, hxψ, hψU, σ, hinj, -, u, hu, hu0, hs⟩ := hsnc x
  obtain ⟨c, hc⟩ : ∃ c, c = ψ x := ⟨_, rfl⟩
  have hev : ∀ᶠ z in 𝓝 c, z ∈ ψ.target ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ ψ.target := ψ.open_target.mem_nhds (hc ▸ ψ.map_source hxψ)
    refine h1.and ?_
    rw [eventually_all]
    intro i
    by_cases h : c i = 0
    · simp [h]
    · filter_upwards [((continuous_apply i).continuousAt (x := c)).eventually_ne h] with z hz _
      exact hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hV : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (3 / r : ℂ) ≠ 0 := by simpa using hrC
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ.restrOpen _ hV).transHomeomorph (pa_aff (3 / r : ℂ) ha c) := ⟨_, rfl⟩
  have hφc : IsCompatChart A φ := hφ ▸ pa_compat_aff A _ (pa_compat_restr A _ hψ _ hV) _ ha _
  have hsrc : ∀ y ∈ φ.source, y ∈ ψ.source ∧ ψ y ∈ Metric.ball c r := by
    intro y hy
    subst hφ
    exact ⟨hy.1, hy.2.2⟩
  have hφapp : ∀ y, φ y = (3 / r : ℂ) • (ψ y - c) := by
    intro y
    subst hφ
    rfl
  have hxφ : x ∈ φ.source := by
    subst hφ
    refine ⟨hxψ, hxψ, ?_⟩
    show ψ x ∈ Metric.ball c r
    rw [← hc]
    exact Metric.mem_ball_self hr
  have htarget : Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target := by
    intro z hz
    subst hφ
    set w : Fin e → ℂ := (3 / r : ℂ)⁻¹ • z + c with hw
    have hwb : w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_right, norm_smul]
      have hz' : ‖z‖ ≤ 2 := by simpa using hz
      have : ‖(3 / r : ℂ)⁻¹‖ = r / 3 := by
        rw [norm_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
        norm_num
      rw [this]
      nlinarith
    have hwT : w ∈ ψ.target := (hball _ hwb).1
    have hmem : w ∈ (ψ.restrOpen _ hV).target :=
      ⟨hwT, ψ.map_target hwT, by simpa [ψ.right_inv hwT] using hwb⟩
    exact hmem

  let g : Fin nb → X → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i ^ m k)
  have hg : ∀ k y, (match σ k with
      | some i => ψ y i ^ m k
      | none => 1) = g k y := by
    intro k y
    simp only [g]
    cases σ k <;> rfl
  have hgholo : ∀ k, A.HoloOn ψ.source (g k) := by
    intro k j z hz
    simp only [g]
    cases σ k with
    | none => exact analyticAt_const
    | some i => exact (holoOn_coord A ψ hψ i j z hz).pow (m k)
  let K : Finset (Fin nb) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let S : Finset (Fin e) := Finset.univ.filter (fun i => c i = 0 ∧ ∃ k, σ k = some i ∧ 1 ≤ m k)
  let μ : Fin e → ℕ := fun i => ∑ k, if σ k = some i then m k else 0
  have hμ : ∀ k i, σ k = some i → μ i = m k := by
    intro k i hk
    refine (Finset.sum_eq_single k (fun b _ hb => if_neg fun h => hb (hinj _ _ i h hk))
      (by simp)).trans (if_pos hk)
  have hKS : ∀ y, ∏ k ∈ K, g k y = ∏ i ∈ S, ψ y i ^ μ i := by
    intro y
    refine Finset.prod_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, k, h1, h3⟩
    · intro k hk k' hk' hkk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      obtain ⟨h1', -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk').2
      exact hinj k k' _ h1 (hkk ▸ h1')
    · intro i hi
      obtain ⟨-, h0, k, hk, hm⟩ := Finset.mem_filter.1 hi
      have hkK : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, h0, hm⟩
      refine ⟨k, hkK, ?_⟩
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hkK).2
      exact Option.some.inj (h1.symm.trans hk)
    · intro k hk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      have key : ∀ i, σ k = some i → g k y = ψ y i ^ μ i := by
        intro i hi
        simp only [g]
        rw [hi, hμ k i hi]
        rfl
      exact key _ h1
  let T : Finset (Fin nb) := Finset.univ.filter
    (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let C : ℂ := ((r : ℂ) / 3) ^ (∑ i ∈ S, μ i)
  have hC : C ≠ 0 := pow_ne_zero _ (div_ne_zero hrC (by norm_num))
  refine ⟨φ, S, μ, fun y => u y * C * ∏ k ∈ T, g k y, hφc, hxφ, htarget, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφapp, ← hc, sub_self, smul_zero]
  · exact fun y hy => hψU (hsrc y hy).1
  · intro i hi
    obtain ⟨-, -, k, hk, hm⟩ := Finset.mem_filter.1 hi
    rw [hμ k i hk]
    exact hm
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, (hsrc _ hz.2).1⟩
    exact ((hu j z hz').mul analyticAt_const).mul
      (Finset.analyticAt_fun_prod _ fun k _ => hgholo k j z hz')
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hsrc y hy
    refine mul_ne_zero (mul_ne_zero (hu0 y hy1) hC) (Finset.prod_ne_zero_iff.2 ?_)
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    simp only [g]
    cases hσ : σ k with
    | none => exact one_ne_zero
    | some i =>
      by_cases hm : m k = 0
      · simp [hm]
      · have hci : c i ≠ 0 := fun h0 => hk' ⟨i, hσ, h0, Nat.one_le_iff_ne_zero.2 hm⟩
        exact pow_ne_zero _ ((hball _ hy2).2 i hci)
  · intro y hy
    obtain ⟨hy1, -⟩ := hsrc y hy
    have hcoord : ∀ i ∈ S, ψ y i = ((r : ℂ) / 3) * φ y i := by
      intro i hi
      obtain ⟨-, h0, -⟩ := Finset.mem_filter.1 hi
      rw [hφapp]
      simp only [Pi.smul_apply, Pi.sub_apply, h0, sub_zero, smul_eq_mul]
      field_simp
    have hsplit : ∏ k, g k y = (∏ k ∈ K, g k y) * ∏ k ∈ T, g k y :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hmono : ∏ i ∈ S, ψ y i ^ μ i = C * ∏ i ∈ S, φ y i ^ μ i := by
      rw [Finset.prod_congr rfl (fun i hi => by rw [hcoord i hi, mul_pow]),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : s x y = u y * ∏ k, g k y := by
      rw [hs y hy1]
      congr 1
      exact Finset.prod_congr rfl (fun k _ => hg k y)
    show s x y = u y * C * (∏ k ∈ T, g k y) * ∏ i ∈ S, φ y i ^ μ i
    rw [h2, hsplit, hKS, hmono]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.LocalForm
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

variable {e n : ℕ}

theorem continuous_comp_emb (σ : Fin n ↪ Fin e) :
    Continuous (fun w : Fin e → ℂ => w ∘ σ) :=
  continuous_pi fun j => continuous_apply (σ j)

theorem analyticAt_comp_emb (σ : Fin n ↪ Fin e) (w : Fin e → ℂ) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => v ∘ σ) w := by
  rw [analyticAt_pi_iff]
  intro j
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (σ j)).analyticAt w

theorem extend_comp_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ g w ∘ σ = g :=
  funext fun j => σ.injective.extend_apply g w j

theorem extend_extend_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ (w ∘ σ) (Function.extend σ g w) = w := by
  funext i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    exact σ.injective.extend_apply _ _ j
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]

theorem analyticAt_extend_emb (σ : Fin n ↪ Fin e) {f : (Fin n → ℂ) → Fin n → ℂ} {w : Fin e → ℂ}
    (hf : AnalyticAt ℂ f (w ∘ σ)) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v) w := by
  rw [analyticAt_pi_iff]
  intro i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v (σ j)) =
        (fun y : Fin n → ℂ => f y j) ∘ (fun v : Fin e → ℂ => v ∘ σ) := by
      funext v
      exact σ.injective.extend_apply _ _ j
    rw [hfun]
    exact AnalyticAt.comp (analyticAt_pi_iff.1 hf j) (analyticAt_comp_emb σ w)
  · have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v i) = fun v => v i := by
      funext v
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt w

noncomputable def extendHomeo (σ : Fin n ↪ Fin e)
    (τ : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (h₁ : AnalyticOnNhd ℂ τ τ.source) (h₂ : AnalyticOnNhd ℂ τ.symm τ.target) :
    OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) where
  toFun w := Function.extend σ (τ (w ∘ σ)) w
  invFun w := Function.extend σ (τ.symm (w ∘ σ)) w
  source := {w | w ∘ σ ∈ τ.source}
  target := {w | w ∘ σ ∈ τ.target}
  map_source' w hw := by
    show Function.extend σ (τ (w ∘ σ)) w ∘ σ ∈ τ.target
    rw [extend_comp_emb]
    exact τ.map_source hw
  map_target' w hw := by
    show Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ ∈ τ.source
    rw [extend_comp_emb]
    exact τ.map_target hw
  left_inv' w hw := by
    show Function.extend σ (τ.symm (Function.extend σ (τ (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.left_inv hw, extend_extend_emb]
  right_inv' w hw := by
    show Function.extend σ (τ (Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ.symm (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.right_inv hw, extend_extend_emb]
  open_source := τ.open_source.preimage (continuous_comp_emb σ)
  open_target := τ.open_target.preimage (continuous_comp_emb σ)
  continuousOn_toFun := fun w hw =>
    (analyticAt_extend_emb σ (h₁ _ hw)).continuousAt.continuousWithinAt
  continuousOn_invFun := fun w hw =>
    (analyticAt_extend_emb σ (h₂ _ hw)).continuousAt.continuousWithinAt

theorem chart_swap :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
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
  refine ⟨ψ.trans T, ?_, hsrc, ?_⟩
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

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.levi_zero_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w, levi (g ∘ (A.chart j).symm) y w = 0) → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart | exact GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart | (intros; apply GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart <;> assumption)
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  first | exact @GlobalTheory.CompanionTheory.SmoothGlue.glue | exact GlobalTheory.CompanionTheory.SmoothGlue.glue | (intros; apply GlobalTheory.CompanionTheory.SmoothGlue.glue <;> assumption)
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  first | exact @GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | exact GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | (intros; apply GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm <;> assumption)
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.smoothOn_of_chart_composition : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | exact GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | (intros; apply GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.local_density_inclusion_exclusion : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | exact GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun <;> assumption)
end
