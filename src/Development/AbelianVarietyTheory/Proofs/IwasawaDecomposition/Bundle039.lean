module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle005
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataCD
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

@[expose] public section

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem _root_.GlobalTheory.densHom_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    l (Metric.closedBall x (s * r)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (Metric.ball 0 r) := by
  rw [Measure.addHaar_closedBall_mul_of_pos l x hs r, Measure.addHaar_closedBall l 0 hr.le,
    Measure.addHaar_ball_of_pos l 0 hr]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem _root_.GlobalTheory.densHom_tendsto_mul {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => s * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun r : ℝ => s * r) (𝓝 0) (𝓝 (s * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hs hr

end

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem closedBall_smul_div_ball_eq_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] (x : V)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ν (Metric.closedBall x (s * r)) / l (Metric.ball 0 r) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) *
        (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r))) := by
  rw [_root_.GlobalTheory.densHom_scale l x hs hr, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hs _)).ne' ENNReal.ofReal_ne_top]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem ofReal_pow_mul_le_liminf_ball_ratio (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.closedBall x (s * r)) ≤ ν (Metric.ball 0 r)) :
    ENNReal.ofReal (s ^ Module.finrank ℝ V) * D ≤
      liminf (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (le_of_eq htend.liminf_eq.symm).trans (Filter.liminf_le_liminf ?_)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem limsup_ball_ratio_le_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.ball 0 r) ≤ ν (Metric.closedBall x (s * r))) :
    limsup (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) ≤
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * D := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (Filter.limsup_le_limsup ?_).trans (le_of_eq htend.limsup_eq)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _


open MeasureTheory Filter Topology Matrix in
theorem _root_.GlobalTheory.exists_density_origin_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V)
    [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (Metric.ball 0 r) ≠ 0) →
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ →
      ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧
        ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) →
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  intro V _ _ _ _ _ l ν _ _ hpos halmost
  set ρ := fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r) with hρ
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ D : ENNReal, D < ⊤ ∧
      ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D ≤ liminf ρ (𝓝[>] 0) ∧
      limsup ρ (𝓝[>] 0) ≤ ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D := by
    intro ε hε hε2
    obtain ⟨δ, hδ, hx⟩ := halmost ε hε (by linarith)
    obtain ⟨x, hxmem, hxD, hxfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos l (0 : V) hδ).ne'
      (ae_restrict_of_ae ((Besicovitch.ae_tendsto_rnDeriv ν l).and (Measure.rnDeriv_lt_top ν l)))
    have hxr := hx x (mem_ball_zero_iff.1 hxmem)
    refine ⟨_, hxfin, ofReal_pow_mul_le_liminf_ball_ratio l ν (by linarith) hxD ?_,
      limsup_ball_ratio_le_ofReal_pow_mul l ν (by linarith) hxD ?_⟩
    · filter_upwards [hxr, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
      exact (measure_mono (Metric.closedBall_subset_ball (by nlinarith))).trans hr.1
    · filter_upwards [hxr] with r hr
      exact hr.2.trans (measure_mono Metric.ball_subset_closedBall)
  have hML : liminf ρ (𝓝[>] 0) ≤ limsup ρ (𝓝[>] 0) := liminf_le_limsup
  have hLtop : limsup ρ (𝓝[>] 0) < ⊤ := by
    obtain ⟨D, hD, -, hup⟩ := key (1 / 4) (by norm_num) (by norm_num)
    exact hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD)
  have hLM : limsup ρ (𝓝[>] 0) ≤ liminf ρ (𝓝[>] 0) := by
    have hK : Tendsto (fun ε : ℝ => ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V))
        (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ =>
          ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V)) 0 :=
        ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp)
      simpa using hc.tendsto
    have hT : Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) * liminf ρ (𝓝[>] 0))
        (𝓝[>] 0) (𝓝 (liminf ρ (𝓝[>] 0))) := by
      have h1 := ENNReal.Tendsto.mul_const (b := liminf ρ (𝓝[>] 0)) (ENNReal.tendsto_ofReal hK)
        (Or.inr (hML.trans_lt hLtop).ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    obtain ⟨D, -, hlow, hup⟩ := key ε hε.1 hε.2
    have hb : 0 < (1 - 2 * ε) ^ Module.finrank ℝ V := pow_pos (by linarith [hε.2]) _
    refine hup.trans ?_
    calc ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D
        = ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) *
          (ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by linarith [hε.1]) _) hb.le),
            div_mul_cancel₀ _ hb.ne']
      _ ≤ _ := by gcongr
  have htend : Tendsto ρ (𝓝[>] 0) (𝓝 (limsup ρ (𝓝[>] 0))) :=
    tendsto_of_liminf_eq_limsup (le_antisymm hML hLM) rfl
  refine ⟨limsup ρ (𝓝[>] 0), ?_, hLtop.ne, htend⟩
  intro hL0
  rw [hL0] at htend
  obtain ⟨δ, hδ, hx⟩ := halmost (1 / 2) (by norm_num) (by norm_num)
  have hs_le : ∀ t : NNReal, 0 < t → ν (Metric.ball 0 δ) ≤ t * l (Metric.ball 0 δ) := by
    intro t ht
    have hle := VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily ν) (t • l)
      (Measure.AbsolutelyContinuous.refl ν) (Metric.ball (0 : V) δ) ?_
    · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hle
      exact hle
    intro x hxs
    apply ((Besicovitch.tendsto_filterAt ν x).comp
      (_root_.GlobalTheory.densHom_tendsto_mul (show (0 : ℝ) < 1 / 4 by norm_num))).frequently
    refine Filter.Eventually.frequently ?_
    have hpos' : (0 : ENNReal) < t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) :=
      ENNReal.mul_pos (by exact_mod_cast ht.ne') (ENNReal.ofReal_pos.2 (by positivity)).ne'
    filter_upwards [(tendsto_order.1 htend).2 _ hpos', hx x (mem_ball_zero_iff.1 hxs),
      self_mem_nhdsWithin] with r hr hxr (hr0 : 0 < r)
    show ν (Metric.closedBall x (1 / 4 * r)) ≤ (t • l) (Metric.closedBall x (1 / 4 * r))
    have hlt : ν (Metric.ball 0 r) <
        t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) * l (Metric.ball 0 r) :=
      (ENNReal.div_lt_iff (Or.inl (Metric.measure_ball_pos l 0 hr0).ne')
        (Or.inl measure_ball_lt_top.ne)).1 hr
    rw [mul_assoc, ← _root_.GlobalTheory.densHom_scale l x (by norm_num) hr0] at hlt
    have hsub : Metric.closedBall x (1 / 4 * r) ⊆ Metric.ball x ((1 - 1 / 2) * r) :=
      Metric.closedBall_subset_ball (by linarith)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((measure_mono hsub).trans hxr.1).trans hlt.le
  have hzero : ν (Metric.ball 0 δ) = 0 := by
    have hT : Tendsto (fun t : NNReal => (t : ENNReal) * l (Metric.ball 0 δ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul_const (b := l (Metric.ball 0 δ))
        (ENNReal.tendsto_coe.2 (tendsto_id (x := 𝓝 (0 : NNReal)))) (Or.inr measure_ball_lt_top.ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hs_le t ht))
      bot_le
  exact hpos δ hδ hzero

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_of_pow_eq_pow {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    {n : ℕ} (hn : 0 < n) {x y : R} (h : x ^ n = y ^ n) : ∃ z : ℂ, x = z • y := by
  have : NeZero n := ⟨hn.ne'⟩
  have h0 := Complex.isPrimitiveRoot_exp n hn.ne'
  have h1 := h0.map_of_injective (algebraMap ℂ R).injective
  have h2 := h1.pow_sub_pow_eq_prod_sub_mul x y hn
  rw [h, sub_self] at h2
  obtain ⟨ζ, hζ, hz⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [Polynomial.mem_nthRootsFinset hn] at hζ
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ i, ?_⟩
  rw [Algebra.smul_def, map_pow, hi]
  exact sub_eq_zero.1 hz

theorem exists_eq_smul_pow_of_pow_eq_tmul :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A]
      [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 →
      w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  intro K _ _ A _ _ _ n w C u hn hC hu hw
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : ℂ) ≠ 0)
  let T : ℂ ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ LinearMap.rTensor A f
  have hT : ∀ (c : ℂ) (a : A), T (c ⊗ₜ a) = f c • a := fun c a => by simp [T]
  have hne : ∀ (c : ℂ) (a : A), c ≠ 0 → a ≠ 0 → c ⊗ₜ[K] a ≠ 0 := by
    intro c a hc ha h
    have h1 : (1 : ℂ) ⊗ₜ[K] a = 0 := by
      have := congrArg (fun t : ℂ ⊗[K] A => c⁻¹ • t) h
      simpa [TensorProduct.smul_tmul', hc] using this
    have h2 := hT 1 a
    rw [h1, map_zero, hf, one_smul] at h2
    exact ha h2.symm
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact hne C u hC hu hw.symm
  have hst : ∀ σ : ℂ ≃ₐ[K] ℂ, ∀ x ∈ Submodule.span ℂ {w},
      σ.toLinearMap.rTensor A x ∈ Submodule.span ℂ {w} := by
    intro σ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    let S : ℂ ⊗[K] A →ₐ[K] ℂ ⊗[K] A := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
    have hS : ∀ t, σ.toLinearMap.rTensor A t = S t := by
      intro t
      induction t with
      | tmul b v => simp [S]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (σ C / C) hn
    have h1 : (S w) ^ n = (μ • w) ^ n := by
      rw [← map_pow, smul_pow, hw, hμ, TensorProduct.smul_tmul', smul_eq_mul,
        div_mul_cancel₀ _ hC]
      simp [S]
    obtain ⟨z, hz⟩ := exists_eq_smul_of_pow_eq_pow hn h1
    have h2 : c • w = (c ⊗ₜ[K] (1 : A)) * w := by
      rw [Algebra.smul_def]; rfl
    have h3 : S (c ⊗ₜ[K] (1 : A)) * S w = σ c • S w := by
      rw [Algebra.smul_def]
      simp [S]
    rw [hS, h2, map_mul, h3, hz, smul_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  obtain ⟨N, hN, -⟩ := (GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange _).1 hst
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    rw [Submodule.baseChange_bot, eq_comm, Submodule.span_singleton_eq_bot] at hN
    exact hw0 hN
  obtain ⟨b, hbN, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hb : (1 : ℂ) ⊗ₜ[K] b ∈ Submodule.span ℂ {w} :=
    hN ▸ Submodule.tmul_mem_baseChange_of_mem 1 hbN
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hb
  have hpow : (1 : ℂ) ⊗ₜ[K] (b ^ n) = (l ^ n * C) ⊗ₜ[K] u := by
    have := congrArg (· ^ n) hl
    simp only [smul_pow, hw, Algebra.TensorProduct.tmul_pow, one_pow, TensorProduct.smul_tmul',
      smul_eq_mul] at this
    exact this.symm
  have hbn : b ^ n ≠ 0 := by
    intro h
    have h1 : ((1 : ℂ) ⊗ₜ[K] b) ^ n = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, h, TensorProduct.tmul_zero]
    exact hne 1 b one_ne_zero hb0 (pow_eq_zero_iff hn.ne' |>.1 h1)
  have h4 := congrArg T hpow
  rw [hT, hT, hf, one_smul] at h4
  have h5 : f (l ^ n * C) ≠ 0 := by
    intro h
    rw [h, zero_smul] at h4
    exact hbn h4
  exact ⟨(f (l ^ n * C))⁻¹, b, inv_ne_zero h5, by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩

end GlobalTheory.KeyFourth
end

section

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

namespace LogTrace

theorem coeff_sub_one_pow {S : Type} [CommRing S] [Algebra ℝ S] (f : S[X]) (s n : ℕ) (hs : s ≤ n) :
    ((f - 1) ^ s).coeff n =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℝ) ^ (s - k) * (s.choose k : ℝ)) • (f ^ k).coeff n := by
  rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : s + 1 ≤ n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show f ^ k * (-1) ^ (s - k) * ((s.choose k : ℕ) : S[X]) =
        C ((-1 : S) ^ (s - k) * (s.choose k : S)) * f ^ k by simp [map_mul, map_pow, map_neg]; ring]
    rw [coeff_C_mul, Algebra.smul_def]
    simp
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem coeff_zero_charpolyRev {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    M.charpolyRev.coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

def newtonPoly {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (m + 1), C (-(M ^ (i + 1)).trace) * X ^ i

theorem coeff_newtonPoly {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m k : ℕ)
    (hk : k ≤ m) : (newtonPoly M m).coeff k = -(M ^ (k + 1)).trace := by
  simp only [newtonPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

theorem X_pow_dvd_derivative_sub {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m : ℕ) :
    (X : R[X]) ^ (m + 1) ∣ derivative M.charpolyRev - newtonPoly M m * M.charpolyRev := by
  rw [X_pow_dvd_iff]
  intro d hd
  have hN := GlobalTheory.natCast_mul_coeff_charpolyRev M (d + 1)
  rw [coeff_sub, coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [coeff_newtonPoly M m k (by simp only [Finset.mem_range] at hk; omega)])]
  simp only [Nat.add_sub_cancel, neg_mul, Finset.sum_neg_distrib] at hN ⊢
  push_cast at hN
  linear_combination hN

def logTrunc {S : Type} [CommRing S] [Algebra ℝ S] (m : ℕ) (f : S[X]) : S[X] :=
  ∑ s ∈ Finset.range (m + 1), C (algebraMap ℝ S ((-1) ^ s / ((s : ℝ) + 1))) * (f - 1) ^ (s + 1)

theorem mul_derivative_logTrunc {S : Type} [CommRing S] [Algebra ℝ S] (m : ℕ) (f : S[X]) :
    f * derivative (logTrunc m f) = derivative f * (1 - (-(f - 1)) ^ (m + 1)) := by
  have hs : ∀ s : ℕ, C (algebraMap ℝ S ((-1) ^ s / ((s : ℝ) + 1))) * C ((s : S) + 1) = (-1) ^ s := by
    intro s
    rw [← C_mul, show ((s : S) + 1) = algebraMap ℝ S ((s : ℝ) + 1) by simp, ← map_mul,
      div_mul_cancel₀ _ (by positivity)]
    simp
  have hD : derivative (logTrunc m f) = (∑ s ∈ Finset.range (m + 1), (-(f - 1)) ^ s) * derivative f := by
    simp only [logTrunc, derivative_sum, derivative_C_mul, derivative_pow_succ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [derivative_sub, derivative_one, sub_zero, neg_pow (f - 1) s]
    linear_combination ((f - 1) ^ s * derivative f) * hs s
  have hg := mul_neg_geom_sum (-(f - 1)) (m + 1)
  rw [hD]
  linear_combination (derivative f) * hg

theorem coeff_logTrunc_charpolyRev {S : Type} [CommRing S] [Algebra ℝ S] {N : ℕ}
    (L : Matrix (Fin N) (Fin N) S) (m : ℕ) :
    ((m : S) + 1) * (logTrunc m (Matrix.charpolyRev (-L))).coeff (m + 1) =
      (-1) ^ m * (L ^ (m + 1)).trace := by
  set f := Matrix.charpolyRev (-L) with hf
  have hX : (X : S[X]) ∣ f - 1 := by
    simp [X_dvd_iff, hf, coeff_zero_charpolyRev]
  have h1 := X_pow_dvd_derivative_sub (-L) m
  rw [← hf] at h1
  have h2 : (X : S[X]) ^ (m + 1) ∣ derivative f * (-(f - 1)) ^ (m + 1) :=
    Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (dvd_neg.2 hX) (m + 1)) _
  have h3 : (X : S[X]) ^ (m + 1) ∣ f * (derivative (logTrunc m f) - newtonPoly (-L) m) := by
    have e : f * (derivative (logTrunc m f) - newtonPoly (-L) m) =
        (derivative f - newtonPoly (-L) m * f) - derivative f * (-(f - 1)) ^ (m + 1) := by
      linear_combination mul_derivative_logTrunc m f
    rw [e]
    exact dvd_sub h1 h2
  have hcop : IsCoprime (X : S[X]) f := by
    obtain ⟨h, hh⟩ := hX
    exact ⟨-h, 1, by linear_combination hh⟩
  have h4 := (X_pow_dvd_iff.1 (hcop.pow_left.dvd_of_dvd_mul_left h3)) m (by omega)
  rw [coeff_sub, coeff_derivative, coeff_newtonPoly (-L) m m le_rfl] at h4
  have ht : ((-L) ^ (m + 1)).trace = -((-1) ^ m * (L ^ (m + 1)).trace) := by
    rw [show -L = (-1 : S) • L by simp, _root_.smul_pow, Matrix.trace_smul, smul_eq_mul, pow_succ]
    ring
  linear_combination h4 - ht

end LogTrace


open LogTrace in
theorem trace_pow_eq_sum_smul_coeff_charpolyRev_pow :
    ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ → ℝ, ∀ (S : Type) [CommRing S] [Algebra ℝ S] (N : ℕ)
      (L : Matrix (Fin N) (Fin N) S),
      ∑ k ∈ Finset.range (n + 1), c k • ((Matrix.charpolyRev (-L)) ^ k).coeff n = (L ^ n).trace := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨fun k => ∑ s ∈ Finset.range (m + 1),
    ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) *
      ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ)), ?_⟩
  intro S _ _ N L
  have key := coeff_logTrunc_charpolyRev L m
  set f := Matrix.charpolyRev (-L)
  have hsq : ((-1 : S) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  calc ∑ k ∈ Finset.range (m + 1 + 1), (∑ s ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) *
          ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ))) • (f ^ k).coeff (m + 1)
      = ∑ s ∈ Finset.range (m + 1), ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) •
          ∑ k ∈ Finset.range (m + 1 + 1),
            ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ)) • (f ^ k).coeff (m + 1) := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
    _ = ∑ s ∈ Finset.range (m + 1), ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) •
          ((f - 1) ^ (s + 1)).coeff (m + 1) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [coeff_sub_one_pow f (s + 1) (m + 1) (by simp only [Finset.mem_range] at hs; omega)]
    _ = ((-1 : ℝ) ^ m * ((m : ℝ) + 1)) • (logTrunc m f).coeff (m + 1) := by
        simp only [logTrunc, finsetSum_coeff, coeff_C_mul, Finset.smul_sum, ← Algebra.smul_def,
          smul_smul]
    _ = (L ^ (m + 1)).trace := by
        rw [Algebra.smul_def]
        simp only [map_mul, map_pow, map_neg, map_one, map_add (f := _), map_natCast]
        linear_combination (-1 : S) ^ m * key + (L ^ (m + 1)).trace * hsq

end GlobalTheory
end
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by
  first | exact @GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | exact GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | (intros; apply GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes <;> assumption)
end
