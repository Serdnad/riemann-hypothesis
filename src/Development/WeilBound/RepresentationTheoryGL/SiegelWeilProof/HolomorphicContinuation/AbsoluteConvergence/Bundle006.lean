module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex

namespace PositivityTheory.Rg.Sw.AbsSt.HP

variable {X : Type} [TopologicalSpace X]

theorem eventually_unif {C : Set X} {U K : Set ℂ} {F : X → ℂ → ℂ}
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hK : IsCompact K) (hKU : K ⊆ U) {x₀ : X} (hx₀ : x₀ ∈ C)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ x in 𝓝 x₀, ∀ ζ ∈ K, x ∈ C → ζ ∈ U → ‖F x ζ - F x₀ ζ‖ < η := by
  have key : ∀ ζ ∈ K, ∀ᶠ p : X × ℂ in 𝓝 (x₀, ζ), p.1 ∈ C → p.2 ∈ U → ‖F p.1 p.2 - F x₀ p.2‖ < η := by
    intro ζ hζ
    have hc := hF (x₀, ζ) ⟨hx₀, hKU hζ⟩
    have h1 : ∀ᶠ p : X × ℂ in 𝓝 (x₀, ζ), p ∈ C ×ˢ U → dist (F p.1 p.2) (F x₀ ζ) < η / 2 :=
      eventually_nhdsWithin_iff.mp (hc.eventually (Metric.ball_mem_nhds _ (half_pos hη)))
    have hg : Tendsto (fun p : X × ℂ => (x₀, p.2)) (𝓝 (x₀, ζ)) (𝓝 (x₀, ζ)) := by
      have hcont : Continuous (fun p : X × ℂ => (x₀, p.2)) := by fun_prop
      simpa using hcont.tendsto (x₀, ζ)
    have h2 := hg.eventually h1
    filter_upwards [h1, h2] with p hp1 hp2 hpC hpU
    have a := hp1 ⟨hpC, hpU⟩
    have b : dist (F x₀ p.2) (F x₀ ζ) < η / 2 := hp2 ⟨hx₀, hpU⟩
    rw [← dist_eq_norm]
    calc dist (F p.1 p.2) (F x₀ p.2) ≤ dist (F p.1 p.2) (F x₀ ζ) + dist (F x₀ p.2) (F x₀ ζ) :=
          dist_triangle_right _ _ _
      _ < η / 2 + η / 2 := add_lt_add a b
      _ = η := add_halves η
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x ζ => x ∈ C → ζ ∈ U → ‖F x ζ - F x₀ ζ‖ < η) key] with x hx ζ hζ hxC hζU
  exact hx ζ hζ hxC hζU

theorem continuousOn_deriv {C : Set X} {U : Set ℂ} {F : X → ℂ → ℂ} (hU : IsOpen U)
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ x ∈ C, DifferentiableOn ℂ (F x) U) :
    ContinuousOn (fun y : X × ℂ => deriv (F y.1) y.2) (C ×ˢ U) := by
  intro ⟨x₀, z₀⟩ ⟨hx₀, hz₀⟩
  have hT : TendstoLocallyUniformlyOn F (F x₀) (𝓝[C] x₀) U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [nhdsWithin_le_nhds (eventually_unif hF hK hKU hx₀ hε), self_mem_nhdsWithin]
      with x hx hxC ζ hζ
    rw [dist_comm, dist_eq_norm]
    exact hx ζ hζ hxC (hKU hζ)
  have hD : ∀ᶠ x in 𝓝[C] x₀, DifferentiableOn ℂ (F x) U := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hd x hx
  have hT' := hT.deriv hD hU
  have hc : ContinuousAt (deriv (F x₀)) z₀ :=
    (((hd x₀ hx₀).deriv hU).continuousOn z₀ hz₀).continuousAt (hU.mem_nhds hz₀)
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  obtain ⟨t, ht, hA⟩ := (Metric.tendstoLocallyUniformlyOn_iff.mp hT') (ε / 2) (half_pos hε) z₀ hz₀
  have hB := (Metric.continuousAt_iff'.mp hc) (ε / 2) (half_pos hε)
  have hB' : ∀ᶠ y in 𝓝[U] z₀, y ∈ t ∧ dist (deriv (F x₀) y) (deriv (F x₀) z₀) < ε / 2 :=
    Filter.inter_mem ht (nhdsWithin_le_nhds hB)
  rw [nhdsWithin_prod_eq]
  filter_upwards [Filter.prod_mem_prod hA hB'] with q hq
  have h1 : dist (deriv (F x₀) q.2) (deriv (F q.1) q.2) < ε / 2 := hq.1 q.2 hq.2.1
  have h2 : dist (deriv (F x₀) q.2) (deriv (F x₀) z₀) < ε / 2 := hq.2.2
  show dist (deriv (F q.1) q.2) (deriv (F x₀) z₀) < ε
  have h3 := dist_triangle (deriv (F q.1) q.2) (deriv (F x₀) q.2) (deriv (F x₀) z₀)
  rw [dist_comm] at h1
  linarith

theorem eqOn_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} (h : EqOn f g U) :
    ∀ r : ℕ, EqOn (iteratedDeriv r f) (iteratedDeriv r g) U := by
  intro r
  induction r with
  | zero => simpa using h
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact (ih.eventuallyEq_of_mem (hU.mem_nhds hz)).deriv_eq

variable [MeasurableSpace X] [BorelSpace X]

theorem aesm_of {μ : Measure X} {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0) {f : X → ℂ}
    (hf : ContinuousOn f C) : AEStronglyMeasurable f μ := by
  set t := (toMeasurable μ Cᶜ)ᶜ with ht
  have htm : MeasurableSet t := (measurableSet_toMeasurable μ Cᶜ).compl
  have htC : t ⊆ C := by
    intro x hx
    by_contra hxC
    exact hx (subset_toMeasurable μ Cᶜ hxC)
  have hμ : μ.restrict t = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have e : {a | ¬ a ∈ t} = toMeasurable μ Cᶜ := by
      ext a
      simp [ht]
    rw [e, measure_toMeasurable]
    exact hCn
  have hh := hf.aestronglyMeasurable_of_subset_isCompact (μ := μ) hC htm htC
  rwa [hμ] at hh

theorem hasDerivAt_int {μ : Measure X} [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0)
    {U : Set ℂ} {F : X → ℂ → ℂ} (hU : IsOpen U)
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ x ∈ C, DifferentiableOn ℂ (F x) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : HasDerivAt (fun z => ∫ x, F x z ∂μ) (∫ x, deriv (F x) z₀ ∂μ) z₀ := by
  have hcz : ∀ z ∈ U, ContinuousOn (fun x => F x z) C := fun z hz =>
    hF.comp (by fun_prop : Continuous fun x : X => (x, z)).continuousOn (fun x hx => ⟨hx, hz⟩)
  have hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun x => F x z) μ :=
    fun z hz => aesm_of hC hCn (hcz z hz)
  have hae : ∀ᵐ x ∂μ, x ∈ C := ae_iff.mpr hCn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hsub : closedBall z₀ (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hD := continuousOn_deriv hU hF hd
  obtain ⟨M, hM⟩ := (hC.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    (hD.mono (prod_mono subset_rfl hsub))
  obtain ⟨M0, hM0⟩ := (hC.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    (hF.mono (prod_mono subset_rfl hsub))
  have hint : Integrable (fun x => F x z₀) μ := by
    refine Integrable.of_bound (hmeas z₀ hz₀) M0 ?_
    filter_upwards [hae] with x hx
    exact hM0 (x, z₀) ⟨hx, mem_closedBall_self (half_pos hε).le⟩
  have hcd : ContinuousOn (fun x => deriv (F x) z₀) C :=
    hD.comp (by fun_prop : Continuous fun x : X => (x, z₀)).continuousOn (fun x hx => ⟨hx, hz₀⟩)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z x => F x z)
    (F' := fun z x => deriv (F x) z) (bound := fun _ => M)
    (closedBall_mem_nhds z₀ (half_pos hε))
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) hmeas) hint (aesm_of hC hCn hcd)
    (by filter_upwards [hae] with x hx z hz using hM (x, z) ⟨hx, hz⟩)
    (integrable_const M)
    (by
      filter_upwards [hae] with x hx z hz
      exact (((hd x hx) z (hsub hz)).differentiableAt (hU.mem_nhds (hsub hz))).hasDerivAt)
  exact key.2

theorem main {μ : Measure X} [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0)
    {U : Set ℂ} (hU : IsOpen U) : ∀ (r : ℕ) (F : X → ℂ → ℂ), ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U) →
      (∀ x ∈ C, DifferentiableOn ℂ (F x) U) →
      ∀ z ∈ U, iteratedDeriv r (fun z => ∫ x, F x z ∂μ) z = ∫ x, iteratedDeriv r (F x) z ∂μ := by
  intro r
  induction r with
  | zero =>
    intro F _ _ z _
    simp
  | succ n ih =>
    intro F hF hd z hz
    have hEq : EqOn (deriv (fun z => ∫ x, F x z ∂μ)) (fun z => ∫ x, deriv (F x) z ∂μ) U :=
      fun w hw => (hasDerivAt_int hC hCn hU hF hd hw).deriv
    rw [iteratedDeriv_succ', eqOn_iteratedDeriv hU hEq n hz,
      ih (fun x => deriv (F x)) (continuousOn_deriv hU hF hd) (fun x hx => (hd x hx).deriv hU) z hz]
    simp_rw [iteratedDeriv_succ']

end PositivityTheory.Rg.Sw.AbsSt.HP

namespace PositivityTheory.Rg.Sw.AbsSt

theorem holParam : HolParam := by
  intro X _ _ _ μ _ C hC hCn U F hU hF hd
  exact ⟨fun z hz => (HP.hasDerivAt_int hC hCn hU hF hd hz).differentiableAt.differentiableWithinAt,
    fun z hz r => HP.main hC hCn hU r F hF hd z hz⟩

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open GlobalTheory.Cont

theorem rightConn : RightConn := by
  intro U _ hU
  obtain ⟨⟨σ, hσ⟩, hR⟩ := hU
  refine isPreconnected_of_forall (((σ + 1 : ℝ)) : ℂ) fun y hy => ?_
  have hx : (((σ + 1 : ℝ)) : ℂ) ∈ rightOf σ := by
    show σ < (((σ + 1 : ℝ)) : ℂ).re
    simp
  set T : ℝ := |y.re| + |σ| + 1 with hTdef
  have hT : (y + (T : ℂ)) ∈ rightOf σ := by
    show σ < (y + (T : ℂ)).re
    simp only [Complex.add_re, Complex.ofReal_re, hTdef]
    linarith [neg_abs_le y.re, le_abs_self σ]
  have hconv : Convex ℝ (rightOf σ) := convex_halfSpace_re_gt σ
  refine ⟨segment ℝ y (y + (T : ℂ)) ∪ segment ℝ (y + (T : ℂ)) (((σ + 1 : ℝ)) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine Set.union_subset ?_ ((hconv.segment_subset hT hx).trans hσ)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have heq : a • y + b • (y + (T : ℂ)) = y + ((b * T : ℝ) : ℂ) := by
      simp only [Complex.real_smul]
      push_cast
      linear_combination y * hab'
    rw [heq]
    exact hR y hy _ (mul_nonneg hb (by positivity))
  · exact Or.inr (right_mem_segment _ _ _)
  · exact Or.inl (left_mem_segment _ _ _)
  · exact IsPreconnected.union (y + (T : ℂ)) (right_mem_segment _ _ _) (left_mem_segment _ _ _)
      (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected

theorem glue : Glue := by
  intro U f h σ s₀ hUo hU hs₀ hfm hfa hσU hhd hfh
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ w, H w = if σ + 1 < w.re then h w else f w := ⟨_, fun _ => rfl⟩
  have hHf : ∀ z, H =ᶠ[𝓝[≠] z] f := by
    intro z
    by_cases hz : σ < z.re
    · filter_upwards [hfh z hz] with w hw
      rw [hH]
      split_ifs
      · exact hw.symm
      · rfl
    · have hlt : z.re < σ + 1 := by linarith [not_lt.1 hz]
      have hn : {w : ℂ | w.re < σ + 1} ∈ 𝓝 z :=
        Complex.continuous_re.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)
      filter_upwards [nhdsWithin_le_nhds hn] with w hw
      rw [hH, if_neg (not_lt.2 (le_of_lt hw))]
  have hmer : IsMerExt h U H := by
    refine ⟨hU, fun z hz => (hfm z hz).congr (hHf z).symm, σ + 1, fun z hz => ?_⟩
    rw [hH, if_pos (show σ + 1 < z.re from hz)]
  have hext : IsExtAt h s₀ (Function.update H s₀ (f s₀)) := (hmer.isExtAt hs₀).update _
  refine ⟨_, hext, ?_, by simp⟩
  apply hfa.congr
  have h2 := eventually_nhdsWithin_iff.1 (hHf s₀)
  filter_upwards [h2] with w hw
  by_cases hw0 : w = s₀
  · subst hw0
    simp
  · rw [Function.update_of_ne hw0]
    exact (hw hw0).symm

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem projected_block_lower_sum (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
  simp

theorem lowerDiagonalBlockAsGL (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
  simp

theorem k_blocks {k : GR n} (hk : k ∈ KR n) :
    (mR k).toBlocks₂₁ = -(mR k).toBlocks₁₂ ∧ (mR k).toBlocks₂₂ = (mR k).toBlocks₁₁ := by
  have hK : InK (mR k) := hk
  have h2 : mR k * (mR k)ᴴ = 1 := mul_eq_one_comm.1 hK.2
  have h3 : JJ n * mR k = mR k * JJ n := by
    calc JJ n * mR k = (mR k * (mR k)ᴴ) * (JJ n * mR k) := by rw [h2, Matrix.one_mul]
      _ = mR k * ((mR k)ᴴ * JJ n * mR k) := by simp only [Matrix.mul_assoc]
      _ = mR k * JJ n := by rw [hK.1]
  rw [← fromBlocks_toBlocks (mR k)] at h3
  unfold JJ at h3
  rw [fromBlocks_multiply, fromBlocks_multiply] at h3
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, fromBlocks_inj] at h3
  obtain ⟨h11, h12, _, _⟩ := h3
  exact ⟨h11, h12⟩

theorem first_block_mul_compact (g : M2 n) {k : GR n} (hk : k ∈ KR n) : u1 (g * mR k) = u1 g * u1 (mR k) := by
  obtain ⟨hC, hD⟩ := k_blocks hk
  simp only [u1, projected_block_lower_sum, lowerDiagonalBlockAsGL, hC, hD]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
    Matrix.mul_neg, smul_add, smul_neg, neg_smul, one_smul]
  abel

theorem second_block_mul_compact (g : M2 n) {k : GR n} (hk : k ∈ KR n) : u2 (g * mR k) = u2 g * u2 (mR k) := by
  obtain ⟨h21, h22⟩ := k_blocks hk
  unfold u2
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, h21, h22]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, neg_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_add]
  abel

theorem first_block_compact_unitary {k : GR n} (hk : k ∈ KR n) : (u1 (mR k))ᴴ * u1 (mR k) = 1 := by
  obtain ⟨h21, h22⟩ := k_blocks hk
  have hK : InK (mR k) := hk
  have e := hK.2
  rw [← fromBlocks_toBlocks (mR k), h21, h22, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at e
  obtain ⟨e11, e12, _, _⟩ := e
  unfold u1
  rw [h21, h22]
  simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at e11 e12
  simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_neg, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, neg_neg, smul_smul, neg_mul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
  rw [(add_neg_eq_zero.1 e12).symm, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, ← e11]
  abel

theorem norm_det_first_block_compact {k : GR n} (hk : k ∈ KR n) : ‖(u1 (mR k)).det‖ = 1 := by
  have h := congrArg Matrix.det (first_block_compact_unitary hk)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have h2 : Complex.normSq (u1 (mR k)).det = 1 := by
    have : ((Complex.normSq (u1 (mR k)).det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      simpa [Complex.star_def] using h
    exact_mod_cast this
  have h3 : ‖(u1 (mR k)).det‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h2
  have h4 : 0 ≤ ‖(u1 (mR k)).det‖ := norm_nonneg _
  nlinarith [h3, h4]

theorem first_block_upper_mul (y : GR n) (g : M2 n) (hy : IsUp y) : u1 (mR y * g) = (mR y).toBlocks₂₂ * u1 g := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u1
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, hy']
  simp [Matrix.mul_add, Matrix.mul_smul]

theorem second_block_upper_mul (y : GR n) (g : M2 n) (hy : IsUp y) : u2 (mR y * g) = (mR y).toBlocks₂₂ * u2 g := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u2
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, hy']
  simp [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem first_block_of_upper (y : GR n) (hy : IsUp y) : u1 (mR y) = (mR y).toBlocks₂₂ := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u1
  rw [hy']
  simp

theorem second_block_of_upper (y : GR n) (hy : IsUp y) : u2 (mR y) = (mR y).toBlocks₂₂ := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u2
  rw [hy']
  simp

theorem mult : Mult := by
  intro n p q e
  constructor
  · intro g k hk
    constructor
    · unfold F0 f0
      rw [mR_mul, first_block_mul_compact _ hk, second_block_mul_compact _ hk, det_mul, det_mul, det_mul, mul_zpow, mul_zpow, mul_zpow]
      ring
    · unfold hLoc
      rw [mR_mul, first_block_mul_compact _ hk, det_mul, norm_mul, norm_det_first_block_compact hk, mul_one]
  · intro y g hy
    constructor
    · unfold F0 f0
      rw [mR_mul, first_block_upper_mul y _ hy, second_block_upper_mul y _ hy, first_block_of_upper y hy, second_block_of_upper y hy, det_mul, det_mul, det_mul,
        mul_zpow, mul_zpow, mul_zpow]
      ring
    · unfold hLoc
      rw [mR_mul, first_block_upper_mul y _ hy, first_block_of_upper y hy, det_mul, norm_mul, mul_pow, mul_inv]

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def FlatEq : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (Q Q' : PX m n),
    (∀ k : GR n, InK (mR k) → sL Q k = sL Q' k) → ∀ y, sL Q y = sL Q' y

def Basis : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)],
    ∀ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W → (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) →
    ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν → Continuous κ →
      (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
      (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
      ∀ P ∈ W, ∃ (N : ℕ) (yy : Fin N → GR n) (QQ : Fin N → PX m n) (cc : Fin N → ℂ) (M : ℂ → Matrix (Fin N) (Fin N) ℂ),
        (∀ j, QQ j ∈ W) ∧ (∀ y, sL P y = ∑ j, cc j * sL (QQ j) y) ∧ M 0 = 1 ∧ (∀ i j, Differentiable ℂ fun w => M w i j) ∧
        (∀ i, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * yy i) ∂ν = sL (QQ i) y') ∧
        ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν =
          (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y'

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def bS (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) * b * diagonal (fun j => (Real.exp (-(h * X j)) : ℂ))

def GaussPart : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (X : Fin n → ℝ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    ∀ Q : PX m n, HasDerivAt (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b))
      (secN ε c t (dil c X Q) b) 0

def GroupPart : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    (∀ s s', a (s + s') = a s * a s') ∧ a 0 = 1 ∧ (∀ s, IsUp (a s)) ∧ Continuous a ∧
    (∀ y : GR n, IsUp y → ∀ s, IsUp (y * a s)) ∧
    (∀ (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
      mR g = JJ n * nU b ∧ y = y₁ * g) ∧
    (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), mR g = JJ n * nU b → ∀ h, mR (a h * g * a h) = JJ n * nU (bS X h b)) ∧
    (∀ y : GR n, (mR y).toBlocks₂₁.det ≠ 0 → ∀ s, (mR (y * a s)).toBlocks₂₁.det ≠ 0) ∧
    Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ∧
    ∀ (p q : ℕ) (e : ℤ) (h : ℝ), F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ))

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end
