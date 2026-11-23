module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def fbHom (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    Matrix m m ℂ × Matrix n n ℂ →+* Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  map_zero' := by simp
  map_add' p q := by simp [Matrix.fromBlocks_add]

set_option backward.isDefEq.respectTransparency false in
theorem exp_reindex (e : m ≃ n) (M : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e M) = Matrix.reindex e e (NormedSpace.exp M) := by
  have hc : Continuous fun M : Matrix m m ℂ => Matrix.reindexAlgEquiv ℂ ℂ e M := by
    simp only [Matrix.coe_reindexAlgEquiv]; exact continuous_id.matrix_reindex e e
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hc M
  simp only [Matrix.coe_reindexAlgEquiv] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem exp_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D) = Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  have hc : Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => fbHom m n p := by
    show Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => Matrix.fromBlocks p.1 0 0 p.2
    exact Continuous.matrix_fromBlocks continuous_fst continuous_const continuous_const continuous_snd
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (fbHom m n) hc (A, D)
  open scoped Matrix.Norms.Operator in
  have h1 := Prod.fst_exp (A, D)
  open scoped Matrix.Norms.Operator in
  have h2 := Prod.snd_exp (A, D)
  change Matrix.fromBlocks _ 0 0 _ = NormedSpace.exp (Matrix.fromBlocks _ 0 0 _) at h
  rw [h1, h2] at h
  exact h.symm

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

section

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Finset
open scoped ComplexConjugate InnerProductSpace

theorem norm_sq_comb {κ : Type} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J : Finset κ) (b : κ → ℂ)
    (y : κ → W) :
    ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ J, ∑ l ∈ J, conj (b j) * b l * ⟪y j, y l⟫_ℂ := by
  rw [show ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ⟪∑ j ∈ J, b j • y j, ∑ j ∈ J, b j • y j⟫_ℂ by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem sum_sq_le_sq_sum {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hx j) (mem_univ i)) (hx i)

theorem norm_sum_le_of_gram {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ P Q, k P Q = ⟪v P, v Q⟫_ℂ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = ∑ i, (c i : ℂ) * ⟪Y i (P l), Y i (P j)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ := by
  have h1 : ((‖∑ j ∈ J, a j • v (P j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_comb]
    calc ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * ⟪v (P j), v (P l)⟫_ℂ
        = ∑ j ∈ J, ∑ l ∈ J, ∑ i, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
          rw [← hv, hk j hj l hl, mul_sum]
          refine sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j ∈ J, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          exact (sum_congr rfl fun j _ => sum_comm).trans sum_comm
      _ = ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
          refine sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_mul, norm_sq_comb, mul_sum, sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [Complex.conj_conj]
          ring
  have h2 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 := by
    exact_mod_cast h1
  have h3 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 ≤ (∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
    rw [h2]
    have : ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 =
        ∑ i, (√(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hc i)]
    rw [this]
    exact sum_sq_le_sq_sum _ fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ :=
    sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (∑ j ∈ J, a j • v (P j))]

end Formalism.FourierDecayAlt.P.GermRateSplit
end

section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section L2m

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma mul_le_young_bounds_of_le_add {nF nG g e t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (hnF : 0 ≤ nF)
    (hG : nG ≤ g + e) :
    (nF ≤ δ → nF * nG ≤ t * nF ^ 2 + (0 + e ^ 2) / (2 * t) + δ / 2 * (1 + g ^ 2)) ∧
      nF * nG ≤ t * nF ^ 2 + (g ^ 2 + e ^ 2) / (2 * t) + δ / 2 * (0 + g ^ 2) := by
  have h2t : 0 < 2 * t := by positivity
  have hGa : nF * nG ≤ nF * |g| + nF * |e| := by
    have : nG ≤ |g| + |e| := hG.trans (add_le_add (le_abs_self g) (le_abs_self e))
    nlinarith

  have hA : ∀ y : ℝ, nF * |y| ≤ t * nF ^ 2 / 2 + y ^ 2 / (2 * t) := by
    intro y
    rw [show t * nF ^ 2 / 2 + y ^ 2 / (2 * t) = (t ^ 2 * nF ^ 2 + y ^ 2) / (2 * t) by field_simp <;> ring,
      le_div_iff₀ h2t]
    nlinarith [sq_nonneg (t * nF - |y|), sq_abs y]
  have hg1 : |g| ≤ (1 + g ^ 2) / 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  refine ⟨fun hK => ?_, ?_⟩
  · have h1 : nF * |g| ≤ δ * |g| := mul_le_mul_of_nonneg_right hK (abs_nonneg g)
    have h2 : δ * |g| ≤ δ / 2 * (1 + g ^ 2) := by nlinarith
    have h3 := hA e
    have h4 : t * nF ^ 2 / 2 ≤ t * nF ^ 2 := by nlinarith [sq_nonneg nF]
    have h5 : (0 + e ^ 2) / (2 * t) = e ^ 2 / (2 * t) := by ring
    rw [h5]
    linarith
  · have h3 := hA e
    have h4 := hA g
    have h5 : (g ^ 2 + e ^ 2) / (2 * t) = g ^ 2 / (2 * t) + e ^ 2 / (2 * t) := by ring
    have h6 : 0 ≤ δ / 2 * (0 + g ^ 2) := by positivity
    rw [h5]
    linarith

private lemma exists_isCompact_integral_compl_sq_lt (μ : Measure ℂ) [NullSingletonClass μ] {g : ℂ → ℝ}
    (hg2 : Integrable (fun D => g D ^ 2) μ) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ < η := by
  let Kn : ℕ → Set ℂ := fun n => Metric.closedBall (0 : ℂ) (n + 1) \ Metric.ball 0 (1 / (n + 1))
  have hKc : ∀ n, IsCompact (Kn n) := fun n => (isCompact_closedBall 0 _).diff Metric.isOpen_ball
  have h0K : ∀ n, (0 : ℂ) ∉ Kn n := by
    intro n h
    exact h.2 (Metric.mem_ball_self (by positivity))
  have hlim : Tendsto (fun n : ℕ => ∫ D, (Kn n)ᶜ.indicator (fun D => g D ^ 2) D ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun D => g D ^ 2)
      (F := fun n D => (Kn n)ᶜ.indicator (fun D => g D ^ 2) D) (f := fun _ => (0 : ℝ))
      (fun n => (hg2.indicator (hKc n).isClosed.measurableSet.compl).aestronglyMeasurable) hg2
      (fun n => Filter.Eventually.of_forall fun D => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)]
        exact Set.indicator_le_self' (fun _ _ => sq_nonneg _) D)
      (by
        have h0 : ∀ᵐ D ∂μ, D ≠ (0 : ℂ) := compl_mem_ae_iff.2 (measure_singleton 0)
        filter_upwards [h0] with D hD
        have hpos : 0 < ‖D‖ := norm_pos_iff.2 hD
        obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖D‖) ‖D‖)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have ha : 1 / ‖D‖ < n + 1 := by linarith [le_max_left (1 / ‖D‖) ‖D‖]
        have hb : ‖D‖ < n + 1 := by linarith [le_max_right (1 / ‖D‖) ‖D‖]
        have hmem : D ∈ Kn n := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact hb.le
          · rw [Metric.mem_ball, dist_zero_right, not_lt]
            rw [div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ hpos] at ha
            linarith
        simp [Set.indicator_apply, hmem])
    simpa using h
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨Kn n, hKc n, h0K n, hn⟩

theorem tendsto_integral_inner_germ_moving {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (e : α → ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (he : ∀ᶠ x in l, MemLp (e x) 2 μ)
    (he0 : Tendsto (fun x => ∫ D, e x D ^ 2 ∂μ) l (𝓝 0))
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D + e x D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  set t : ℝ := ε / (4 * B') with ht_def
  have ht : 0 < t := by positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := hg.integrable_sq
  obtain ⟨K, hKc, h0K, hKint⟩ := exists_isCompact_integral_compl_sq_lt μ hg2 (η := ε * t / 2) (by positivity)
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hI1 : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hKmeas).2 (integrableOn_const hKfin.ne)
  set M : ℝ := ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ + ∫ D, g D ^ 2 ∂μ + 1 with hM_def
  have hM : 0 < M := by
    have h1 : 0 ≤ ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ :=
      integral_nonneg fun D => Set.indicator_nonneg (fun _ _ => zero_le_one) D
    have h2 : 0 ≤ ∫ D, g D ^ 2 ∂μ := integral_nonneg fun D => sq_nonneg _
    linarith
  set δ : ℝ := ε / (4 * M) with hδ_def
  have hδ : 0 < δ := by positivity
  have he' : ∀ᶠ x in l, ∫ D, e x D ^ 2 ∂μ < ε * t / 2 := he0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hF, he, he', hG, hloc K hKc h0K δ hδ] with x hFx hex he2 hGx hlx
  have hFmem : MemLp (F x) 2 μ := hFx.1
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).1 hFmem
  have he2i : Integrable (fun D => e x D ^ 2) μ := hex.integrable_sq
  have hIc : Integrable (Kᶜ.indicator (fun D => g D ^ 2)) μ := hg2.indicator hKmeas.compl
  have i1 : Integrable (fun D => t * ‖F x D‖ ^ 2) μ := hF2.const_mul t
  have i2 : Integrable (fun D => (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ :=
    (hIc.add he2i).div_const _
  have i3 : Integrable (fun D => δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) μ :=
    (hI1.add hg2).const_mul _
  have i12 : Integrable (fun D => t * ‖F x D‖ ^ 2 +
      (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ := i1.add i2
  have hbnd : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤
      t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2) := by
    filter_upwards [hGx, hlx] with D hGD hlD
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * ‖G x D‖ := norm_inner_le_norm _ _
    have hP := mul_le_young_bounds_of_le_add ht hδ.le (norm_nonneg (F x D)) hGD
    by_cases hD : D ∈ K
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 1 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = 0 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans (hP.1 (hlD hD))
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 0 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = g D ^ 2 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans hP.2
  have hsplit : ∫ D, (t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) ∂μ =
      t * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) +
        δ / 2 * (M - 1) := by
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_div,
      integral_add hIc he2i, integral_const_mul, integral_add hI1 hg2]
    simp only [hM_def]
    ring
  have hle : ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ t * ∫ D, ‖F x D‖ ^ 2 ∂μ +
      (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) + δ / 2 * (M - 1) := by
    rw [← hsplit]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (i12.add i3) hbnd)
  have hb1 : t * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hFB' : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B' := by linarith [le_max_left B 0]
    have : t * B' = ε / 4 := by rw [ht_def]; field_simp <;> ring
    nlinarith
  have hb2 : (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hb3 : δ / 2 * (M - 1) ≤ ε / 8 := by
    have : δ * M = ε / 4 := by rw [hδ_def]; field_simp <;> ring
    nlinarith
  linarith

end L2m

end

end Formalism.FourierDecayAlt.P.PBK
end

section

open MeasureTheory Real Module
open scoped FourierTransform

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem moment_integrable {u : V → ℂ} (hu : Continuous u) (m : ℕ) (C : ℝ)
    (hdec : ∀ w, ‖u w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) (n : ℕ) (hn : n ≤ m) :
    Integrable (fun v => ‖v‖ ^ n * ‖u v‖) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hdec 0)
    have hp : 0 < (1 + ‖(0 : V)‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hint : Integrable (fun v : V => C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1))) :=
    (integrable_one_add_norm (by linarith)).const_mul C
  refine hint.mono' ((continuous_norm.pow n).mul (continuous_norm.comp hu)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have h0 : (0 : ℝ) < 1 + ‖v‖ := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ n * ‖u v‖ ≤ (1 + ‖v‖) ^ n * (C * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        gcongr
        · linarith [norm_nonneg v]
        · exact hdec v
    _ = C * ((1 + ‖v‖) ^ (n : ℝ) * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        rw [Real.rpow_natCast]; ring
    _ = C * (1 + ‖v‖) ^ ((n : ℝ) + -((m : ℝ) + finrank ℝ V + 1)) := by
        rw [← Real.rpow_add h0]
    _ ≤ C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)) := by
        gcongr
        have : (n : ℝ) ≤ m := by exact_mod_cast hn
        linarith

theorem fourier_smooth (D : V → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ w, ‖𝓕 D w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) :
    ∃ D' : V → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  set g : V → ℂ := 𝓕 D with hg
  have hgc : Continuous g :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hD
  set h : V → ℂ := fun x => g (-x) with hh
  have hhc : Continuous h := hgc.comp continuous_neg
  have hhd : ∀ w, ‖h w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by
    intro w
    have := hdec (-w)
    rwa [norm_neg] at this
  have hmom : ∀ n : ℕ, n ≤ m → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    moment_integrable hhc m C hhd
  have hmomN : ∀ n : ℕ, (n : ℕ∞) ≤ (m : ℕ∞) → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    fun n hn => hmom n (by exact_mod_cast hn)
  have hgi : Integrable g := by
    have := moment_integrable hgc m C hdec 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hgc.aestronglyMeasurable).1 this
  have hinv : 𝓕 h = 𝓕⁻ g := (fourierInv_eq_fourier_comp_neg g).symm
  refine ⟨𝓕 h, Real.contDiff_fourier hmomN, fun j hj => ?_, fun t ht => ?_⟩
  · refine ⟨∫ v, (2 * π * ‖innerSL ℝ (E := V)‖) ^ j * (‖v‖ ^ j * ‖h v‖), fun t => ?_⟩
    rw [Real.iteratedFDeriv_fourier hmomN hhc.aestronglyMeasurable (by exact_mod_cast hj)]
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
      ((hmom j hj).const_mul _) (Filter.Eventually.of_forall fun v => ?_)
    have := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) h v j
    simpa [mul_assoc] using this
  · rw [hinv]
    exact hD.fourierInv_fourier_eq hgi ht

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section

open MeasureTheory Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem integral_fderiv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : V → W} (hd : Differentiable ℝ F) (hF : Integrable F) (hF' : Integrable (fderiv ℝ F)) (v : V) :
    ∫ x, fderiv ℝ F x v = 0 := by
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ : V => (1 : ℝ)) (f' := fun _ => 0) (g := F) (g' := fderiv ℝ F) (v := v)
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (by simp) (by simpa using hF'.apply_continuousLinearMap v) (by simpa using hF)
    (fun x _ => hasFDerivAt_const _ _) (fun x _ => hd x |>.hasFDerivAt)
  simpa using h

theorem integrable_of_decay {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : V → W} (hu : Continuous u)
    (C : ℝ) (hdec : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1))) : Integrable u :=
  ((integrable_one_add_norm (by linarith)).const_mul C).mono' hu.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hdec x)

theorem integral_iteratedFDeriv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {D : V → W} {m : ℕ} (hD : ContDiff ℝ m D) (C : ℝ)
    (hdec : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  have hint : ∀ i ≤ m, Integrable (iteratedFDeriv ℝ i D) := fun i hi =>
    integrable_of_decay (hD.continuous_iteratedFDeriv (by exact_mod_cast hi)) C (hdec i hi)
  refine ⟨hint j hjm, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i D) :=
    hD.differentiable_iteratedFDeriv (by exact_mod_cast (show i < m by omega))
  have hF' : Integrable (fderiv ℝ (iteratedFDeriv ℝ i D)) := by
    have h := hint (i + 1) hjm
    have hc1 : ContDiff ℝ 1 (iteratedFDeriv ℝ i D) :=
      hD.iteratedFDeriv_right (by exact_mod_cast (show 1 + i ≤ m by omega))
    refine h.norm.mono' (hc1.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_fderiv_iteratedFDeriv]
  ext m'
  rw [ContinuousMultilinearMap.integral_apply (hint (i + 1) hjm)]
  simp only [iteratedFDeriv_succ_apply_left, ContinuousMultilinearMap.zero_apply]
  have h0 := integral_fderiv_eq_zero hdiff (hint i (by omega)) hF' (m' 0)
  rw [← ContinuousMultilinearMap.integral_apply (hF'.apply_continuousLinearMap (m' 0)), h0]
  rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end
