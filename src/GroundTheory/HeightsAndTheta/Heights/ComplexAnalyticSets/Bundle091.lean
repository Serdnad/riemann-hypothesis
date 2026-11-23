module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.JacobianAtCurvePoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle078
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNormalisationModelLocalizationX
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Nullstellensatz
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Metric Filter Topology Set Complex MeasureTheory

open scoped Real

noncomputable section

namespace ParametricCircleIntegralAnalytic

theorem analyticOnNhd_of_differentiableOn_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {O : Set E} {f : E → ℂ} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    AnalyticOnNhd ℂ f O := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hO' : IsOpen (e.symm ⁻¹' O) := hO.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' O) :=
    hf.comp e.symm.differentiableOn (fun y hy => hy)
  have ha := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hO' hg
  intro x hx
  have h1 : AnalyticAt ℂ (f ∘ e.symm) (e x) := ha (e x) (by simpa using hx)
  have h2 := h1.comp (ContinuousLinearMap.analyticAt (e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) x)
  simpa [Function.comp_def] using h2

end ParametricCircleIntegralAnalytic


open ParametricCircleIntegralAnalytic in
theorem ParametricCircleIntegralAnalytic.proof : ParametricCircleIntegralAnalytic.Statement := by
  intro ι _ Φ O U c r hr hO hU hΦ hUO x₀ hx₀
  have hcd : ContinuousOn (fderiv ℂ Φ) O :=
    ((analyticOnNhd_of_differentiableOn_fd hO hΦ).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  obtain ⟨u, v, hu, -, hx₀u, hsv, huv⟩ := generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hO
    (by rintro ⟨x, s⟩ ⟨hx, hs⟩; obtain rfl : x = x₀ := hx; exact hUO x hx₀ s hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds (hx₀u rfl))
  have hK : closedBall x₀ ε ×ˢ sphere c r ⊆ O := fun p hp => huv ⟨hεu hp.1, hsv hp.2⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn
    (hcd.mono hK)
  have hmem : ∀ x ∈ closedBall x₀ ε, ∀ θ : ℝ, (x, circleMap c r θ) ∈ O := fun x hx θ =>
    hK ⟨hx, circleMap_mem_sphere c hr θ⟩
  have hcont : ∀ x ∈ closedBall x₀ ε,
      Continuous fun θ : ℝ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ) := fun x hx =>
    (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
      (hΦ.continuousOn.comp_continuous (by fun_prop) (hmem x hx))
  have hdiff : DifferentiableOn ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) (ball x₀ ε) := by
    intro x₁ hx₁
    have hs : ball x₀ ε ∈ 𝓝 x₁ := isOpen_ball.mem_nhds hx₁
    have hx₁c : x₁ ∈ closedBall x₀ ε := ball_subset_closedBall hx₁
    simp only [circleIntegral, deriv_circleMap]
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
      (b := 2 * π) (F := fun x θ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ))
      (F' := fun x θ => (circleMap 0 r θ * I) •
        (fderiv ℂ Φ (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ))
      (bound := fun _ => |r| * (M * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖)) hs ?_ ?_ ?_ ?_ ?_
      ?_).differentiableAt.differentiableWithinAt
    · filter_upwards [hs] with x hx
      exact (hcont x (ball_subset_closedBall hx)).aestronglyMeasurable
    · exact (hcont x₁ hx₁c).intervalIntegrable _ _
    · refine Continuous.aestronglyMeasurable ?_
      exact (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
        ((ContinuousLinearMap.compL ℂ (ι → ℂ) ((ι → ℂ) × ℂ) ℂ).flip
          (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) |>.continuous.comp
          (hcd.comp_continuous (by fun_prop) (hmem x₁ hx₁c)))
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact hM _ ⟨ball_subset_closedBall hx, circleMap_mem_sphere c hr θ⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap c r θ)) (x, circleMap c r θ) :=
        (hΦ.differentiableAt (hO.mem_nhds (hmem x (ball_subset_closedBall hx) θ))).hasFDerivAt
      exact (h1.comp x (hasFDerivAt_prodMk_left x (circleMap c r θ))).const_smul (circleMap 0 r θ * I)
  exact analyticOnNhd_of_differentiableOn_fd isOpen_ball hdiff x₀ (mem_ball_self hε)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isClosed_zeroSetIn_of_ideal {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroSetIn I) := by
  have h : zeroSetIn I = ⋂ q ∈ I, {z : σ → ℂ | eval z q = 0} := by
    ext z; simp [zeroSetIn]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem HolomorphicOnSubset.continuousWithinAt_trace {σ : Type*} [Fintype σ] {g : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S) {z : σ → ℂ} (hz : z ∈ S) :
    ContinuousWithinAt g S z := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg z hz
  have hFc : ContinuousAt F z := (hF.differentiableAt (hV.mem_nhds hzV)).continuousAt
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hgF ⟨hz, hzV⟩)
  filter_upwards [inter_mem_nhdsWithin S (hV.mem_nhds hzV)] with x hx using hgF hx

theorem HolomorphicOnSubset.differentiableAt_comp {σ : Type*} [Fintype σ] {k : ℕ}
    {g : (σ → ℂ) → ℂ} {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S)
    {s : (Fin k → ℂ) → σ → ℂ} {y : Fin k → ℂ} (hs : DifferentiableAt ℂ s y)
    (hS : ∀ᶠ y' in 𝓝 y, s y' ∈ S) : DifferentiableAt ℂ (fun y' => g (s y')) y := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg (s y) hS.self_of_nhds
  have hFd : DifferentiableAt ℂ F (s y) := hF.differentiableAt (hV.mem_nhds hzV)
  have hev : ∀ᶠ y' in 𝓝 y, s y' ∈ V := hs.continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  refine (hFd.comp y hs).congr_of_eventuallyEq ?_
  filter_upwards [hS, hev] with y' h1 h2 using hgF ⟨h1, h2⟩

theorem LocalTrace.proof (hbc : LocalBranchedCovering.Statement) : LocalTrace.Statement := by
  intro σ _ I w U g hI hw hU hg
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, hwonly, hprop, hδd, hδne, hsheets,
    hopen⟩ := hbc σ I w U hI hw hU
  have hZc : IsClosed (zeroSetIn I) := isClosed_zeroSetIn_of_ideal I
  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left hZc
  have hgc : ContinuousOn g (zeroSetIn I ∩ U) := fun z hz => hg.continuousWithinAt_trace hz
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ zeroSetIn I ∩ closure W, ‖g z‖ ≤ M :=
    hKc.exists_bound_of_continuousOn (hgc.mono (Set.inter_subset_inter_right _ hWU))

  obtain ⟨f, hf⟩ : ∃ f : (Fin k → ℂ) → ℂ,
      ∀ y, f y = ∑ᶠ z ∈ {z | z ∈ zeroSetIn I ∩ W ∧ A z = y}, g z := ⟨_, fun _ => rfl⟩
  have hfsum : ∀ (s : Fin m → σ → ℂ) (y : Fin k → ℂ),
      (∀ j, s j ∈ zeroSetIn I ∩ W ∧ A (s j) = y) → Function.Injective s →
      (∀ z ∈ zeroSetIn I ∩ W, A z = y → z ∈ Set.range s) → f y = ∑ j, g (s j) := by
    intro s y hs hinj hcov
    have hset : {z | z ∈ zeroSetIn I ∩ W ∧ A z = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hf, hset, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  have hmemU : ∀ z ∈ zeroSetIn I ∩ W, z ∈ zeroSetIn I ∩ U := fun z hz =>
    ⟨hz.1, hWU (subset_closure hz.2)⟩
  have hfd : DifferentiableOn ℂ f (D ∩ {t | δ t ≠ 0}) := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    have hev : f =ᶠ[𝓝 y] fun y' => ∑ j, g (s j y') := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      exact hfsum (fun j => s j y') y' (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine hg.differentiableAt_comp ((hsd j).differentiableAt (hOo.mem_nhds hyO)) ?_
    filter_upwards [hOo.mem_nhds hyO] with y' hy' using hmemU _ ((hsO y' hy').1 j).1
  have hfb : ∀ y ∈ D ∩ {t | δ t ≠ 0}, ‖f y‖ ≤ m * M := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    rw [hfsum (fun j => s j y) y (hsO y hyO).1 (hsO y hyO).2.1 (hsO y hyO).2.2]
    calc ‖∑ j, g (s j y)‖ ≤ ∑ j : Fin m, ‖g (s j y)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum fun j _ =>
          hM _ ⟨((hsO y hyO).1 j).1.1, subset_closure ((hsO y hyO).1 j).1.2⟩
      _ = m * M := by simp
  obtain ⟨T, hTd, hTf⟩ := RiemannExtensionAnalytic.proof k D δ f hDo hδd hδne hfd (fun τ _ =>
    ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨m * M, by
      rintro _ ⟨y, ⟨⟨_, hyD⟩, hyδ⟩, rfl⟩
      exact hfb y ⟨hyD, hyδ⟩⟩⟩)
  refine ⟨k, A, W ∩ A ⁻¹' D, D, m, T, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩,
    fun z hz => hWU (subset_closure hz.1), hDo, hAwD,
    fun z hz hAz => hwonly z ⟨hz.1, hz.2.1⟩ hAz, hTd, ?_⟩
  intro y hyD

  have hseq : ∀ n : ℕ, ∃ t ∈ D ∩ Metric.ball y (1 / ((n : ℝ) + 1)), δ t ≠ 0 := fun n =>
    hδne _ (hDo.inter Metric.isOpen_ball) Set.inter_subset_left
      ⟨y, hyD, Metric.mem_ball_self (by positivity)⟩
  choose t ht htδ using hseq
  have htD : ∀ n, t n ∈ D := fun n => (ht n).1
  have httend : Tendsto t atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (ht n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hX : ∀ n, ∃ X : Fin m → σ → ℂ, (∀ j, X j ∈ zeroSetIn I ∩ W ∧ A (X j) = t n) ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = t n → z ∈ Set.range X) ∧ T (t n) = ∑ j, g (X j) := by
    intro n
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets (t n) (htD n) (htδ n)
    obtain ⟨h1, h2, h3⟩ := hsO (t n) hyO
    exact ⟨fun j => s j (t n), h1, h3, by rw [hTf ⟨htD n, htδ n⟩, hfsum _ (t n) h1 h2 h3]⟩
  choose X hXmem hXcov hXT using hX

  have hKm : IsCompact (Set.univ.pi fun _ : Fin m => zeroSetIn I ∩ closure W) :=
    isCompact_univ_pi fun _ => hKc
  obtain ⟨x, hxK, φ, hφ, hXφ⟩ := hKm.tendsto_subseq (x := X) (fun n => Set.mem_univ_pi.2 fun j =>
    ⟨(hXmem n j).1.1, subset_closure (hXmem n j).1.2⟩)
  have hxK' : ∀ j, x j ∈ zeroSetIn I ∩ closure W := fun j => Set.mem_univ_pi.1 hxK j
  have hxj : ∀ j, Tendsto (fun n => X (φ n) j) atTop (𝓝 (x j)) := fun j => tendsto_pi_nhds.1 hXφ j
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 y) := httend.comp hφ.tendsto_atTop
  have hAx : ∀ j, A (x j) = y := fun j =>
    tendsto_nhds_unique ((A.continuous.tendsto _).comp (hxj j))
      (Tendsto.congr (fun n => ((hXmem (φ n) j).2).symm) htφ)
  have hxW : ∀ j, x j ∈ W := fun j => hprop (x j) (hxK' j) (by rw [hAx j]; exact hyD)
  have hT1 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (T y)) :=
    (hTd.differentiableAt (hDo.mem_nhds hyD)).continuousAt.tendsto.comp htφ
  have hT2 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (∑ j, g (x j))) := by
    have hs : Tendsto (fun n => ∑ j, g (X (φ n) j)) atTop (𝓝 (∑ j, g (x j))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hgc (x j) ⟨(hxK' j).1, hWU (hxK' j).2⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxj j, Filter.Eventually.of_forall fun n =>
          hmemU _ (hXmem (φ n) j).1⟩)
    exact Tendsto.congr (fun n => (hXT (φ n)).symm) hs
  refine ⟨x, fun j => ⟨⟨(hxK' j).1, hxW j, by show A (x j) ∈ D; rw [hAx j]; exact hyD⟩, hAx j⟩,
    ?_, tendsto_nhds_unique hT1 hT2⟩

  rintro z ⟨hzZ, hzW, -⟩ hAz
  by_contra hz
  have hne : ∀ j, 0 < dist z (x j) := fun j => dist_pos.2 fun h => hz ⟨j, h.symm⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo z hzW
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ r ∧ ∀ j, 2 * ε < dist z (x j) := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε) (Filter.Eventually.and (nhdsWithin_le_nhds (Iic_mem_nhds hr) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ r)
      (Filter.eventually_all.2 fun j => nhdsWithin_le_nhds ?_))
    have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
    exact h2.eventually (gt_mem_nhds (hne j))
  obtain ⟨ε, hε0, hεr, hεd⟩ := hε.exists
  have hnbhd := hopen z ⟨hzZ, hzW⟩ ε hε0
  rw [hAz] at hnbhd
  have hev1 : ∀ᶠ n in atTop, t (φ n) ∈ A '' (zeroSetIn I ∩ Metric.ball z ε) := htφ hnbhd
  have hev2 : ∀ᶠ n in atTop, ∀ j, dist (X (φ n) j) (x j) < ε :=
    Filter.eventually_all.2 fun j => Metric.tendsto_nhds.1 (hxj j) ε hε0
  obtain ⟨n, ⟨z', ⟨hz'Z, hz'b⟩, hAz'⟩, hd⟩ := (hev1.and hev2).exists
  have hz'W : z' ∈ W := hrW (Metric.ball_subset_ball hεr hz'b)
  obtain ⟨j, hj⟩ := hXcov (φ n) z' ⟨hz'Z, hz'W⟩ hAz'
  have h1 := hd j
  rw [hj] at h1
  rw [Metric.mem_ball] at hz'b
  have h3 := dist_triangle z z' (x j)
  have h4 := hεd j
  rw [dist_comm] at hz'b
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurveJacobian.proof (hDVR : NormalCurvePointDVR.Statement) : NormalCurveJacobian.Statement := by
  intro σ _ I w hI hint hdim hw
  obtain ⟨hd, hdvr⟩ := hDVR σ I w hI hint hdim hw
  let : Algebra (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs (Algebra (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  have : IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs
      (IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  exact JacobianAtCurvePoint.exists_of_isDiscreteValuationRing I w hw (pointLocalRing I w)
    (by exact Ideal.Quotient.mk_surjective) (by exact Ideal.mk_ker)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormalModelDisc.proof (hreg : NormalCurveRegularPoint.Statement) : NormalModelDisc.Statement := by
  intro n J M w _ hdim hw
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  obtain ⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩ :=
    hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw
  have hwg : w ∈ g '' O := hZV ▸ ⟨hw, hwV⟩
  obtain ⟨y₀, hy₀, hgy₀⟩ := hwg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
  have hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O := fun τ hτ ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hτ)
  refine ⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact ((hg _ (hmem τ hτ)).differentiableAt.comp τ
      (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt
  · intro s hs t ht hst
    have h := congrArg A hst
    simp only at h
    rw [hAg _ (hmem s hs), hAg _ (hmem t ht)] at h
    exact add_left_cancel h
  · intro τ hτ
    have h : g (y₀ + τ) ∈ g '' O := ⟨_, hmem τ hτ, rfl⟩
    rw [← hZV] at h
    exact h.1
  · simp [hgy₀]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem zeroSetEuc_subsingleton_of_dim_zero {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((0 : ℕ) : WithBot ℕ∞))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ zeroSetEuc J) :
    ∀ y ∈ zeroSetEuc J, y = z := by
  have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) := Ring.krullDimLE_iff.2 (le_of_eq hdim)
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  obtain ⟨p, hp⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := ℂ)).1 hmax
  have hcoord : ∀ w ∈ zeroSetEuc J, ∀ i, w i = p i := by
    intro w hw i
    have hmem : (X i - C (p i) : MvPolynomial (Fin n) ℂ) ∈ J := by
      rw [hp, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have := hw _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  intro y hy
  ext i
  rw [hcoord y hy i, hcoord z hz i]

theorem VarietyLelongMono.proof (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hW : VarWirtinger.Statement) (hM : VarLelongMono.Statement) : VarietyLelongMono.Statement := by
  intro n d J hJ hdim z hz r s hr hrs
  rcases d with _ | d
  · have hsub := zeroSetEuc_subsingleton_of_dim_zero J hJ hdim hz
    have hpt : ∀ ρ : ℝ, 0 < ρ → zeroSetEuc J ∩ Metric.ball z ρ = {z} := by
      intro ρ hρ
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => hsub y h.1
      · rintro rfl
        exact ⟨hz, Metric.mem_ball_self hρ⟩
    rw [hpt r hr, hpt s (hr.trans_le hrs)]
    simp [Measure.hausdorffMeasure_zero_singleton]
  · obtain ⟨A, hA⟩ := hN n (d + 1) J hdim
    obtain ⟨c, hc, hWc⟩ := hW d
    have hball : ∀ ρ : ℝ, (fun x : Fin n → ℂ => WithLp.toLp 2 x) ⁻¹' Metric.ball z ρ =
        euclBall (WithLp.ofLp z) ρ := by
      intro ρ
      ext y
      rw [Set.mem_preimage, mem_euclBall_iff, Metric.mem_ball]
    have hμ : ∀ ρ : ℝ, μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) =
        ENNReal.ofReal (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) ρ).indicator fun _ => 1)
          (fun _ => euclPot) y) := by
      intro ρ
      rw [← hball ρ]
      exact (hWc n J A hJ hdim hA _ measurableSet_ball Metric.isBounded_ball).2
    have key := hM n d J A (WithLp.ofLp z) r s hJ hdim hA hr hrs
    rw [hμ r, hμ s, ← ENNReal.ofReal_mul (pow_nonneg (hr.le.trans hrs) _),
      ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc s ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y)
        = c * (s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring
      _ ≤ c * (r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := mul_le_mul_of_nonneg_left key hc.le
      _ = r ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem EnergyDensNonneg.proof : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem NormalisationModelLocalization.full : NormalisationModelLocalization.Statement :=
  NormalisationModelLocalization.proof

end GroundTheory.Heights₂.Heights
end
