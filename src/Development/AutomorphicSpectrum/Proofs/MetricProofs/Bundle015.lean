module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.MeasureTheory.Function.Jacobian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.DegSlope

private lemma degreeWith_bot {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    {r : ℕ} (f : Fin r → ↥(⊥ : Submodule (𝓞 K) E.carrier)) : E.degreeWith ⊥ f = 0 := by
  unfold HermitianBundle.degreeWith
  have h0 : ∀ i, ((f i : E.carrier)) = 0 := fun i => (Submodule.mem_bot _).1 (f i).2
  have hcard : Nat.card (↥(⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range f)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Quotient.inductionOn₂' a b (fun x y => congrArg _ (Subsingleton.elim x y))⟩, ⟨0⟩⟩
  have hdet : ∀ σ : K →+* ℂ, Real.log ‖E.gramDet σ (fun i => ((f i : E.carrier)))‖ = 0 := by
    intro σ
    unfold HermitianBundle.gramDet
    simp only [h0, TensorProduct.tmul_zero, inner_zero_left]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
      have hc : (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier)) = 0 := by
        have h : @inner ℂ _ (E.metric.form σ).toInner ((0 : Fibre σ E.carrier) + 0) 0 =
            @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 +
              @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 :=
          (E.metric.form σ).add_left 0 0 0
        rw [add_zero] at h
        linear_combination -h
      have hdet0 : (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det = 0 := by
        rw [show (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
            (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))) = 0 from
          Matrix.ext fun _ _ => hc]
        exact Matrix.det_zero
      have hgoal : Real.log ‖(Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det‖ = 0 := by
        rw [hdet0, norm_zero, Real.log_zero]
      exact hgoal
  rw [hcard]
  simp [hdet]

theorem normDegree_le_rank_mul_of_slopeMax_le : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  intro K _ _ E μ hμ F
  by_cases hF : F = ⊥
  · subst hF
    have hr : E.rank ⊥ = 0 := by
      simp [HermitianBundle.rank]
    rw [hr, Nat.cast_zero, zero_mul]
    unfold HermitianBundle.normDegree HermitianBundle.degree
    rw [degreeWith_bot, zero_div]
  · have hpos : 0 < E.rank F := by
      unfold HermitianBundle.rank
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
      exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hx⟩, by simpa using hx0⟩
    have h1 : (E.slope F : EReal) ≤ E.slopeMax :=
      le_iSup₂ (f := fun G (_ : G ≠ ⊥) => (E.slope G : EReal)) F hF
    have h2 : E.slope F ≤ μ := EReal.coe_le_coe_iff.1 (h1.trans hμ)
    unfold HermitianBundle.slope at h2
    rw [div_le_iff₀ (by exact_mod_cast hpos)] at h2
    linarith

end GlobalTheory.CompanionTheory.Ar.DegSlope
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem isClosed_coordDiv (S : Finset (Fin e)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, {z : Fin e → ℂ | z i = 0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

theorem volume_coordDiv_eq_zero (S : Finset (Fin e)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ (S : Set (Fin e)),
      ((LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin e → ℂ)) : Set (Fin e → ℂ)) := by
    ext z
    simp [coordDiv]
  rw [h, measure_biUnion_null_iff S.countable_toSet]
  intro i _
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single i (1 : ℂ) : Fin e → ℂ) ∈ LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  simp at hmem

theorem exists_mem_source (R : RegChartData A) (x : X) : ∃ j, x ∈ (R.chart j).source := by
  obtain ⟨j, hj⟩ := R.cover x
  exact ⟨j, R.closure_mid j (subset_closure (R.closure_inner j (subset_closure hj)))⟩

theorem isOpen_Yo (R : RegChartData A) : IsOpen R.Yo := by
  have h : R.Yo = ⋃ j, (R.chart j).source ∩ (R.chart j) ⁻¹' (coordDiv (R.S j))ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := exists_mem_source R x
      exact ⟨j, hj, (R.mem_Yo j x hj).1 hx⟩
    · rintro ⟨j, hj, hc⟩
      exact (R.mem_Yo j x hj).2 hc
  rw [h]
  exact isOpen_iUnion fun j => (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl

theorem volume_compl_Yo (R : RegChartData A) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0 := by
  have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ ⊆
      ⋃ k, ((A.chart j) ∘ (R.chart k).symm) ''
        (((R.chart k).target ∩ (R.chart k).symm ⁻¹' (A.chart j).source) ∩ coordDiv (R.S k)) := by
    rintro y ⟨hyT, hyY⟩
    have hxs : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyT
    obtain ⟨k, hk⟩ := exists_mem_source R ((A.chart j).symm y)
    have hxc : R.chart k ((A.chart j).symm y) ∈ coordDiv (R.S k) := by
      by_contra h
      exact hyY ((R.mem_Yo k _ hk).2 h)
    refine Set.mem_iUnion.mpr ⟨k, R.chart k ((A.chart j).symm y), ⟨⟨(R.chart k).map_source hk, ?_⟩, hxc⟩, ?_⟩
    · show (R.chart k).symm (R.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
      rw [(R.chart k).left_inv hk]
      exact hxs
    · show (A.chart j) ((R.chart k).symm (R.chart k ((A.chart j).symm y))) = y
      rw [(R.chart k).left_inv hk, (A.chart j).right_inv hyT]
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · exact (((R.compat k j).2.differentiableOn).restrictScalars ℝ).mono Set.inter_subset_left
  · exact measure_mono_null Set.inter_subset_right (volume_coordDiv_eq_zero _)

theorem continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∉ coordDiv (R.S k) := (R.mem_Yo k x hk).1 hx
  have hUo : IsOpen ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) :=
    (R.chart k).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl
  have hxU : x ∈ (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ := ⟨hk, hxc⟩
  have hg : ContinuousOn (fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹)
      ((R.chart k).target \ coordDiv (R.S k)) := by
    refine ContinuousOn.add (continuousOn_const.add ((R.f_smooth k).continuousOn.mono Set.sdiff_subset)) ?_
    refine continuousOn_finsetSum _ fun i hi => ?_
    have hne : ∀ y ∈ (R.chart k).target \ coordDiv (R.S k), ‖y i‖ ^ 2 ≠ 0 := by
      intro y hy
      have hyi : y i ≠ 0 := fun h0 => hy.2 (show ∃ i' ∈ R.S k, y i' = 0 from ⟨i, hi, h0⟩)
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hyi)
    exact (((continuous_apply i).norm.pow 2).continuousOn.inv₀ hne).log fun y hy => inv_ne_zero (hne y hy)
  have heq : Set.EqOn R.r ((fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹) ∘ R.chart k)
      ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) := by
    intro z hz
    have h1 := R.r_chart k (R.chart k z) ⟨(R.chart k).map_source hz.1, hz.2⟩
    rw [(R.chart k).left_inv hz.1] at h1
    exact h1
  have hcont := hg.comp (s := (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ)
    ((R.chart k).continuousOn.mono Set.inter_subset_left)
    (fun _ hz => ⟨(R.chart k).map_source hz.1, hz.2⟩)
  exact ((hcont.congr heq).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt

theorem eventually_not_le_of_not_mem_Yo (R : RegChartData A) {x : X} (hx : x ∉ R.Yo) (l : ℝ) :
    ∀ᶠ z in 𝓝 x, ¬ (z ∈ R.Yo ∧ R.r z ≤ l) := by
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∈ coordDiv (R.S k) := by
    by_contra h
    exact hx ((R.mem_Yo k x hk).2 h)
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ R.S k, R.chart k x i = 0 := hxc
  obtain ⟨B, hB⟩ := R.f_bdd
  have hca : ContinuousAt (fun z => ‖R.chart k z i‖ ^ 2) x :=
    ((continuous_apply i).continuousAt.comp ((R.chart k).continuousAt hk)).norm.pow 2
  have h0 : ‖R.chart k x i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) := by
    rw [hi0, norm_zero]
    simp [Real.exp_pos]
  have h1 : ∀ᶠ z in 𝓝 x, ‖R.chart k z i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) :=
    Filter.Tendsto.eventually hca (gt_mem_nhds h0)
  have h2 : ∀ᶠ z in 𝓝 x, z ∈ (R.chart k).source := (R.chart k).open_source.mem_nhds hk
  filter_upwards [h1, h2] with z hz1 hz2
  rintro ⟨hzY, hzr⟩
  have hzc : R.chart k z ∉ coordDiv (R.S k) := (R.mem_Yo k z hz2).1 hzY
  have hyT : R.chart k z ∈ (R.chart k).target := (R.chart k).map_source hz2
  have hr := R.r_chart k (R.chart k z) ⟨hyT, hzc⟩
  rw [(R.chart k).left_inv hz2] at hr
  have hball : ‖R.chart k z‖ < 1 := by simpa using R.target_subset k hyT
  have hne : ∀ i' ∈ R.S k, R.chart k z i' ≠ 0 := fun i' hi' h0 =>
    hzc (show ∃ i'' ∈ R.S k, R.chart k z i'' = 0 from ⟨i', hi', h0⟩)
  have hterm : ∀ i' ∈ R.S k, 0 ≤ Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ := by
    intro i' hi'
    apply Real.log_nonneg
    have hp : 0 < ‖R.chart k z i'‖ := norm_pos_iff.mpr (hne i' hi')
    have hlt : ‖R.chart k z i'‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm _ i') hball
    exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)
  have hsum : Real.log (‖R.chart k z i‖ ^ 2)⁻¹ ≤ ∑ i' ∈ R.S k, Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ :=
    Finset.single_le_sum hterm hi
  have hp : 0 < ‖R.chart k z i‖ ^ 2 := by
    have := norm_pos_iff.mpr (hne i hi)
    positivity
  have hlog : Real.log (‖R.chart k z i‖ ^ 2) < -(l - Real.exp 1 + B) := (Real.log_lt_iff_lt_exp hp).mpr hz1
  rw [Real.log_inv] at hsum
  have hf := (abs_le.mp (hB k _ hyT)).1
  linarith

theorem isCompact_sublevel [CompactSpace X] (R : RegChartData A) (l : ℝ) :
    IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ l} := by
  refine IsClosed.isCompact (isOpen_compl_iff.mp (isOpen_iff_eventually.mpr fun x hx => ?_))
  by_cases hY : x ∈ R.Yo
  · have hlt : l < R.r x := not_le.mp fun h => hx ⟨hY, h⟩
    have hcont : ContinuousAt R.r x := (continuousOn_r R).continuousAt ((isOpen_Yo R).mem_nhds hY)
    filter_upwards [Filter.Tendsto.eventually hcont (lt_mem_nhds hlt)] with z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le]
    exact fun _ => hz
  · exact eventually_not_le_of_not_mem_Yo R hY l

theorem regData_open_part : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A),
    IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧
      ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  intro e X _ _ _ A R
  exact ⟨isOpen_Yo R, volume_compl_Yo R, continuousOn_r R, isCompact_sublevel R⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.MaDiag

theorem matrix_eq_of_form {e : ℕ} (A B : Matrix (Fin e) (Fin e) ℂ)
    (h : ∀ w : Fin e → ℂ, w ⬝ᵥ (A *ᵥ star w) = w ⬝ᵥ (B *ᵥ star w)) : A = B := by
  set C := A - B with hC
  have hΦ : ∀ w : Fin e → ℂ, w ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro w
    rw [hC, Matrix.sub_mulVec, dotProduct_sub, h w, sub_self]
  have expand : ∀ (u w : Fin e → ℂ) (c : ℂ), (u + c • w) ⬝ᵥ (C *ᵥ star (u + c • w)) =
      u ⬝ᵥ (C *ᵥ star u) + star c * (u ⬝ᵥ (C *ᵥ star w)) + c * (w ⬝ᵥ (C *ᵥ star u)) +
        c * star c * (w ⬝ᵥ (C *ᵥ star w)) := by
    intro u w c
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hsI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hpair : ∀ u w : Fin e → ℂ, u ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro u w
    have h1 := expand u w 1
    have h2 := expand u w Complex.I
    rw [hΦ (u + (1 : ℂ) • w), hΦ u, hΦ w, star_one] at h1
    rw [hΦ (u + Complex.I • w), hΦ u, hΦ w, hsI] at h2
    linear_combination (-1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2 +
      ((u ⬝ᵥ (C *ᵥ star w) - w ⬝ᵥ (C *ᵥ star u)) / 2) * Complex.I_sq
  ext i j
  have hs : star (Pi.single j (1 : ℂ) : Fin e → ℂ) = Pi.single j 1 := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := hpair (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [C, sub_eq_zero] using this

private theorem pair_inv_mul_eq_of_mul_self_eq_one (c d : ℂ) (a b p q : ℝ) :
    c * ((((a + q : ℝ) : ℂ) + Complex.I * ((b - p : ℝ) : ℂ)) / 4 * star d) =
      ((((c.re * d.re * a + c.re * d.im * b + c.im * d.re * p + c.im * d.im * q) +
        ((Complex.I * c).re * (Complex.I * d).re * a + (Complex.I * c).re * (Complex.I * d).im * b +
          (Complex.I * c).im * (Complex.I * d).re * p +
            (Complex.I * c).im * (Complex.I * d).im * q)) / 4 : ℝ) : ℂ) +
      Complex.I * ((((c.re * (Complex.I * d).re * a + c.re * (Complex.I * d).im * b +
          c.im * (Complex.I * d).re * p + c.im * (Complex.I * d).im * q) -
        ((Complex.I * c).re * d.re * a + (Complex.I * c).re * d.im * b +
          (Complex.I * c).im * d.re * p + (Complex.I * c).im * d.im * q)) / 4 : ℝ) : ℂ) := by
  have h4 : ∀ X : ℂ, X / 4 = ((1 / 4 : ℝ) : ℂ) * X := fun X => by push_cast; ring
  rw [h4]
  apply Complex.ext <;> simp <;> ring

theorem dot_hessC_star {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (w : Fin e → ℂ) :
    w ⬝ᵥ (hessC f z *ᵥ star w) = (levi f z w : ℂ) := by
  set H := fderiv ℝ (fderiv ℝ f) z with hH
  have hsymm : ∀ x y, H x y = H y x := fun x y =>
    hf.isSymmSndFDerivAt minSmoothness_of_isRCLikeNormedField.le x y
  have hsmul : ∀ (c : ℂ) (u : Fin e → ℂ), c • u = c.re • u + c.im • (Complex.I • u) := by
    intro c u
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hHs : ∀ (c d : ℂ) (u v : Fin e → ℂ), H (c • u) (d • v) =
      c.re * d.re * H u v + c.re * d.im * H u (Complex.I • v) +
        c.im * d.re * H (Complex.I • u) v + c.im * d.im * H (Complex.I • u) (Complex.I • v) := by
    intro c d u v
    rw [hsmul c u, hsmul d v]
    simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    ring
  set E := fun i : Fin e => (Pi.single i (1 : ℂ) : Fin e → ℂ) with hE
  have hw : ∀ x : Fin e → ℂ, x = ∑ i, x i • E i := by
    intro x
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply]
  have hHsum : ∀ x y : Fin e → ℂ, H x y = ∑ i, ∑ j, H (x i • E i) (y j • E j) := by
    intro x y
    conv_lhs => rw [hw x, hw y]

    simp only [map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_comm
  have hpair : ∀ i j, w i * (hessC f z i j * star (w j)) =
      (((H (w i • E i) (w j • E j) + H ((Complex.I * w i) • E i) ((Complex.I * w j) • E j)) / 4 : ℝ) : ℂ) +
        Complex.I * (((H (w i • E i) ((Complex.I * w j) • E j) -
          H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) : ℂ) := by
    intro i j
    have hx : hessC f z i j = (((H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j) : ℝ) : ℂ) +
        Complex.I * ((H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j) : ℝ) : ℂ)) / 4 := rfl
    rw [hx, hHs (w i) (w j), hHs (Complex.I * w i) (Complex.I * w j), hHs (w i) (Complex.I * w j),
      hHs (Complex.I * w i) (w j)]
    exact pair_inv_mul_eq_of_mul_self_eq_one (w i) (w j) _ _ _ _
  have hanti : ∀ F : Fin e → Fin e → ℝ, (∀ i j, F i j = -F j i) → ∑ i, ∑ j, F i j = 0 := by
    intro F hF
    have h1 : ∑ i, ∑ j, F i j = ∑ j, ∑ i, F i j := Finset.sum_comm
    have h2 : ∑ j, ∑ i, F i j = -∑ j, ∑ i, F j i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hF i j)
    linarith
  have hQ0 : ∑ i, ∑ j, ((H (w i • E i) ((Complex.I * w j) • E j) -
      H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) = 0 := by
    apply hanti
    intro i j
    rw [hsymm (w i • E i), hsymm ((Complex.I * w i) • E i)]
    ring
  have hLHS : w ⬝ᵥ (hessC f z *ᵥ star w) = ∑ i, ∑ j, w i * (hessC f z i j * star (w j)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  have hlevi : levi f z w = (H w w + H (Complex.I • w) (Complex.I • w)) / 4 := rfl
  rw [hLHS]
  simp_rw [hpair]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [hQ0, Complex.ofReal_zero, mul_zero, add_zero, hlevi, hHsum w w,
    hHsum (Complex.I • w) (Complex.I • w)]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

theorem dot_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) (w : Fin e → ℂ) :
    w ⬝ᵥ ((Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)) *ᵥ star w) =
      ((∑ q, dd q * ‖(M *ᵥ w) q‖ ^ 2 : ℝ) : ℂ) := by
  have hs : M.map (starRingEnd ℂ) *ᵥ star w = star (M *ᵥ w) := by
    ext q
    simp [Matrix.mulVec, dotProduct, star_sum]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [← Complex.mul_conj']
  simp only [Complex.star_def]
  ring

theorem det_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) :
    (Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)).det =
      (((∏ q, dd q) * ‖M.det‖ ^ 2 : ℝ) : ℂ) := by
  have hc : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hc]
  push_cast
  rw [← Complex.mul_conj']
  ring

theorem maDens_diag_levi (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ)
    (M : Matrix (Fin e) (Fin e) ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hl : ∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) :
    maDens (fun _ => φ) z =
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  have hH : hessC φ z = Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ) := by
    apply matrix_eq_of_form
    intro w
    rw [dot_hessC_star φ z hφ w, dot_congr_diag, hl w]
  simp only [maDens]
  rw [hH, ReciprocityTheory.AnForm.A.mdisc_const, det_congr_diag, Complex.ofReal_re]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.MaDiag
end
