module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Aesop.Main
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem le_mul_setIntegral_image2_of_forall_le (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ)
    (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ)
    (hΘ : Continuous Θ) (hQ : IsCompact Q) (hB : IsCompact B) (hB1 : B ∈ nhds (1 : G))
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) →
      (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) →
      a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  have hBfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hQfin : (volume : Measure (Fin N → ℝ)) Q ≠ ⊤ := hQ.measure_lt_top.ne
  have hBpos : 0 < μ.real B :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds μ hB1).ne' hBfin
  refine ⟨K * (volume : Measure (Fin N → ℝ)).real Q / μ.real B, by positivity, ?_⟩
  intro F a hF hF0 ha
  set Ω : Set G := Set.image2 (fun t b => Θ t * b) Q B with hΩdef
  have hΩ : IsCompact Ω := by
    rw [hΩdef, ← Set.image_prod]
    exact (hQ.prod hB).image (by fun_prop)
  have hFΩ : IntegrableOn F Ω μ := hF.continuousOn.integrableOn_compact hΩ
  have hstep : ∀ t ∈ Q, ∫ x in B, F (Θ t * x) ∂μ ≤ ∫ x in Ω, F x ∂μ := by
    intro t ht
    rw [← (measurePreserving_mul_left μ (Θ t)).setIntegral_image_emb
      (measurableEmbedding_mulLeft (Θ t)) F B]
    refine setIntegral_mono_set hFΩ (Filter.Eventually.of_forall hF0) ?_
    refine Filter.Eventually.of_forall ?_
    rintro _ ⟨b, hb, rfl⟩
    exact Set.mem_image2_of_mem ht hb
  have hint : Integrable (Function.uncurry fun (x : G) (t : Fin N → ℝ) => F (Θ t * x))
      ((μ.restrict B).prod (volume.restrict Q)) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.integrableOn_compact (hB.prod hQ) ?_
    exact (by fun_prop : Continuous fun p : G × (Fin N → ℝ) => F (Θ p.2 * p.1)).continuousOn
  have h1 : μ.real B * a ≤ ∫ x in B, K * ∫ t in Q, F (Θ t * x) ∂volume ∂μ := by
    have hc : μ.real B * a = ∫ _x in B, a ∂μ := by simp
    rw [hc]
    refine setIntegral_mono_on (integrableOn_const hBfin) ?_ hB.measurableSet ha
    exact hint.integral_prod_left.const_mul K
  have h2 : ∫ x in B, ∫ t in Q, F (Θ t * x) ∂volume ∂μ ≤
      (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ := by
    rw [integral_integral_swap hint]
    have hc : (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ =
        ∫ _t in Q, (∫ x in Ω, F x ∂μ) := by simp
    rw [hc]
    exact setIntegral_mono_on hint.integral_prod_right (integrableOn_const hQfin)
      hQ.measurableSet hstep
  rw [integral_const_mul] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hBpos, mul_comm a, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem volume_le_mul_volume_image_of_expanding (N : ℕ) (S : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (hK : 0 ≤ K)
    (hf : ∀ t ∈ S, ∀ t' ∈ S, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    volume S ≤ ENNReal.ofReal (K ^ N) * volume (f '' S) := by
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    have := hf a ha b hb
    rw [hab, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hg : ∀ a ∈ S, Function.invFunOn f S (f a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
  have hlip : LipschitzOnWith K.toNNReal (Function.invFunOn f S) (f '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hg a ha, hg b hb, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]
    exact hf a ha b hb
  have himg : Function.invFunOn f S '' (f '' S) = S := hinj.invFunOn_image subset_rfl
  have h := hlip.hausdorffMeasure_image_le (d := (Fintype.card (Fin N) : ℝ)) (by positivity)
  rw [himg, hausdorffMeasure_pi_real, Fintype.card_fin, ENNReal.rpow_natCast] at h
  rw [ENNReal.ofReal_pow hK]
  exact h

theorem setIntegral_le_of_expanding (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ)
    (hA : IsCompact A) (hQ : IsCompact Q) (hK : 0 ≤ K) (c₁ : Continuous h₁) (c₂ : Continuous h₂)
    (n₁ : ∀ t, 0 ≤ h₁ t) (n₂ : ∀ t, 0 ≤ h₂ t) (hm : ∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t))
    (hf : ∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  have i₁ : IntegrableOn h₁ A volume := c₁.continuousOn.integrableOn_compact hA
  have i₂ : IntegrableOn h₂ Q volume := c₂.continuousOn.integrableOn_compact hQ
  have hKN : 0 ≤ K ^ N := pow_nonneg hK N
  have hI₂ : 0 ≤ ∫ t in Q, h₂ t := integral_nonneg n₂
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKN hI₂), ENNReal.ofReal_mul hKN,
    ofReal_integral_eq_lintegral_ofReal i₁ (Filter.Eventually.of_forall n₁),
    ofReal_integral_eq_lintegral_ofReal i₂ (Filter.Eventually.of_forall n₂),
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₁) c₁.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₂) c₂.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  have m₁ : MeasurableSet {a | r < h₁ a} := measurableSet_lt measurable_const c₁.measurable
  have m₂ : MeasurableSet {a | r < h₂ a} := measurableSet_lt measurable_const c₂.measurable
  rw [Measure.restrict_apply m₁, Measure.restrict_apply m₂]
  refine (volume_le_mul_volume_image_of_expanding N ({a | r < h₁ a} ∩ A) K f hK
    (fun t ht t' ht' => hf t ht.2 t' ht'.2)).trans ?_
  gcongr
  rintro _ ⟨a, ⟨ha, haA⟩, rfl⟩
  exact ⟨lt_of_lt_of_le ha (hm a haA).2, (hm a haA).1⟩

end GlobalTheory
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem rayAvg_inner {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ)
    (hΨ : Measurable Ψ) (hd : finrank ℝ E = m + 1) {t : ℝ} (ht : 0 < t) :
    ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ
      = ∫⁻ y, (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ := by
  set f : E → ℝ≥0∞ := fun y => if ‖y‖ ≤ t then ENNReal.ofReal (t ^ m * (‖y‖ / t) ^ (m + 1)) * Ψ y else 0
    with hfdef
  have hf : Measurable f := by
    refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hΨ
  have h1 : ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ
      = ∫⁻ v, f (t • v) ∂μ := by
    rw [← lintegral_indicator measurableSet_closedBall]
    congr 1; ext v
    have hiff : t * ‖v‖ ≤ t ↔ ‖v‖ ≤ 1 := mul_le_iff_le_one_right ht
    have hdiv : t * ‖v‖ / t = ‖v‖ := by field_simp
    simp only [indicator, Metric.mem_closedBall, dist_zero_right, hfdef, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, hiff, hdiv]
  rw [h1, ← lintegral_map hf (measurable_const_smul t), Measure.map_addHaar_smul μ ht.ne',
    lintegral_smul_measure, hd, smul_eq_mul, ← lintegral_const_mul _ hf]
  congr 1; ext y
  simp only [hfdef]
  split_ifs with hy
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 2
    rw [abs_of_pos (inv_pos.mpr (pow_pos ht _))]
    have htne := ht.ne'
    rw [div_pow]
    field_simp
    ring
  · simp

theorem rayAvg_radial (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0; simp
  set g : ℝ → ℝ := fun t => r ^ (m + 1) / t ^ (m + 2) with hgdef
  have hrpow : ∀ t : ℝ, 0 < t → (t ^ (-(m:ℝ) - 2)) = (t ^ (m + 2))⁻¹ := by
    intro t ht
    rw [show (-(m:ℝ) - 2) = -(((m + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
      Real.rpow_natCast]
  have hcongr : EqOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) g (Ioi r) := by
    intro t ht
    simp only [hgdef, hrpow t (hpos.trans ht), div_eq_mul_inv]
  have hint : IntegrableOn g (Ioi r) :=
    (show IntegrableOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) (Ioi r) volume from
      (integrableOn_Ioi_rpow_of_lt (a := -(m:ℝ) - 2)
        (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos).const_mul (r ^ (m + 1))).congr_fun
      hcongr measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : 0 < t := hpos.trans ht
    simp only [Pi.zero_apply, hgdef]; positivity
  have hval : ∫ t in Ioi r, g t = 1 / ((m:ℝ) + 1) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -(m:ℝ) - 2) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos]
    rw [show (-(m:ℝ) - 2 + 1) = -(((m + 1 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      Real.rpow_natCast]
    have : 0 < r ^ (m + 1) := pow_pos hpos _
    field_simp
    push_cast; ring
  have hgm : Measurable fun t : ℝ => ENNReal.ofReal (g t) :=
    ENNReal.measurable_ofReal.comp (by simp only [hgdef]; fun_prop)
  calc ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t * a := by
        refine le_trans (setLIntegral_le_lintegral _ _) (le_of_eq ?_)
        congr 1; ext t
        simp only [indicator, mem_Ici, hgdef]
        split_ifs <;> simp
    _ = (∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t) * a :=
        lintegral_mul_const _ (hgm.indicator measurableSet_Ici)
    _ = (∫⁻ t in Ioi r, ENNReal.ofReal (g t)) * a := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

theorem rayAvg_bound : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ), Measurable Ψ → finrank ℝ E = m + 1 → ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := by
  intro E _ _ _ _ _ μ _ Ψ m hΨ hd
  have hF : Measurable fun p : E × ℝ => ENNReal.ofReal (p.2 ^ m * ‖p.1‖ ^ (m + 1)) * Ψ (p.2 • p.1) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp (measurable_snd.smul measurable_fst))
  have hK : Measurable fun p : ℝ × E =>
      (if ‖p.2‖ ≤ p.1 then ENNReal.ofReal (‖p.2‖ ^ (m + 1) / p.1 ^ (m + 2)) * Ψ p.2 else 0) := by
    refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_fst) ?_
      measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp measurable_snd)
  calc ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ
      = ∫⁻ t in Ioi (0:ℝ), (∫⁻ v in Metric.closedBall (0:E) 1,
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ t in Ioi (0:ℝ), (∫⁻ y,
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ) :=
        setLIntegral_congr_fun measurableSet_Ioi (fun t ht => rayAvg_inner μ Ψ m hΨ hd ht)
    _ = ∫⁻ y, (∫⁻ t in Ioi (0:ℝ),
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0)) ∂μ :=
        lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ y, ENNReal.ofReal (1 / ((m : ℝ) + 1)) * Ψ y ∂μ :=
        lintegral_mono (fun y => rayAvg_radial m (norm_nonneg y) (Ψ y))
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := lintegral_const_mul _ hΨ

end GlobalTheory
end

section

open ValuativeRel Matrix

namespace GlobalTheory

theorem frame_normalise_integral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ)
    (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k) (hYQ : Y * Q' = 1) :
    ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k),
      (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  classical

  have key : (Y * Q').det = ∑ p : Fin s → D, (∏ i, Q' (p i) i) * (Y.submatrix id p).det := by
    simp only [det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [hYQ, det_one] at key
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (key ▸ one_ne_zero)
  haveI : Nonempty (Fin s → D) := ⟨p₀⟩
  obtain ⟨κ, hκ⟩ := Finite.exists_max (fun p : Fin s → D => valuation k (Y.submatrix id p).det)
  have hne : (Y.submatrix id κ).det ≠ 0 := by
    intro h0
    have := hκ p₀
    rw [h0, map_zero] at this
    exact right_ne_zero_of_mul hp₀ ((valuation k).zero_iff.mp (le_antisymm this zero_le'))
  set h := (Y.submatrix id κ)⁻¹ with hh
  have hsub : ∀ p : Fin s → D, (h * Y).submatrix id p = h * Y.submatrix id p := by
    intro p; ext r c; simp [Matrix.mul_apply]
  have hone : (h * Y).submatrix id κ = 1 := by
    rw [hsub, hh]
    exact nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)
  refine ⟨h, Matrix.of fun j l => if j = κ l then 1 else 0, ?_, ?_, ?_⟩
  · intro i j
    have e : (h * Y) i j = ((h * Y).submatrix id (Function.update κ i j)).det := by
      have : (h * Y).submatrix id (Function.update κ i j) =
          (1 : Matrix (Fin s) (Fin s) k).updateCol i (fun r => (h * Y) r j) := by
        ext r c
        by_cases hc : c = i
        · subst hc; simp
        · rw [updateCol_ne hc, ← hone]
          simp [Function.update_of_ne hc]
      rw [this, ← cramer_apply, cramer_one]; rfl
    rw [Valuation.mem_integer_iff, e, hsub, det_mul, hh, det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀]
    have hpos : 0 < valuation k (Y.submatrix id κ).det :=
      lt_of_le_of_ne zero_le' (Ne.symm ((valuation k).ne_zero_iff.mpr hne))
    rw [mul_comm, ← div_eq_mul_inv, div_le_one₀ hpos]
    exact hκ _
  · intro i j
    rw [Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · have : h * Y * (Matrix.of fun j l => if j = κ l then (1 : k) else 0 : Matrix D (Fin s) k) =
        (h * Y).submatrix id κ := by
      ext r l; simp [Matrix.mul_apply]
    rw [this, hone]

end GlobalTheory
end

section

noncomputable section

open NumberField

namespace GlobalTheory.WeilUnitaryTransport

def ratPair (F : Type) [Field F] [NumberField F] (κ : Type) :
    AddSubgroup ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :=
  ((AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).prodMap
    (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ)).range

theorem mem_ratPair_iff {F : Type} [Field F] [NumberField F] {κ : Type}
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    w ∈ ratPair F κ ↔ ∃ y z : κ → F,
      w = (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) := by
  constructor
  · rintro ⟨⟨y, z⟩, rfl⟩
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    exact ⟨(y, z), rfl⟩

end GlobalTheory.WeilUnitaryTransport

end
end

section

noncomputable section

open NumberField

namespace GlobalTheory.ThetaParseval

def ratVec (F : Type) [Field F] [NumberField F] (κ : Type) : AddSubgroup (κ → AdeleRing (𝓞 F) F) :=
  (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).range

theorem mem_ratVec_iff {F : Type} [Field F] [NumberField F] {κ : Type} (x : κ → AdeleRing (𝓞 F) F) :
    x ∈ ratVec F κ ↔ ∃ ξ : κ → F, x = fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i) := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩

end GlobalTheory.ThetaParseval

end
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ringOfIntegers_trace_mulLeft_nondegenerate :
    ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K),
      (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro K _ _ x hx
  by_contra hne
  have hxK : (x : K) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_eq_zero_iff.mp h)
  have halg : IsAlgebraic ℤ ((x : K)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨d, hd0, hdi⟩ := halg.exists_integral_multiple
  let y : 𝓞 K := ⟨d • (x : K)⁻¹, hdi⟩
  have hxy : x * y = algebraMap ℤ (𝓞 K) d := by
    apply RingOfIntegers.coe_injective
    show (x : K) * (d • (x : K)⁻¹) = ((algebraMap ℤ (𝓞 K) d : 𝓞 K) : K)
    rw [eq_intCast, zsmul_eq_mul]
    push_cast
    field_simp
    first | exact (map_intCast (algebraMap (𝓞 K) K) d).symm | norm_cast | simp
  have h := hx y
  rw [hxy] at h
  have h2 : LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (algebraMap ℤ (𝓞 K) d))
      = Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d) := by
    rw [Algebra.trace_apply]; rfl
  rw [h2, Algebra.trace_algebraMap] at h
  have hpos : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h) hpos.ne'
  · exact hd0 h

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsReduced (k ⊗[ℤ] 𝓞 F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : IsReduced (k ⊗[ℤ] F) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ℤ] F)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℤ k) (IsScalarTower.toAlgHom ℤ (𝓞 F) F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective _ hinj

instance isSemisimpleRing_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsSemisimpleRing (k ⊗[ℤ] 𝓞 F) := by
  haveI := isReduced_charZero_tensor_ringOfIntegers F k
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem projective_charZero_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] 𝓞 F) M], Module.Projective (k ⊗[ℤ] 𝓞 F) M := by
  intro F _ _ k _ _ M _ _
  exact Module.projective_of_isSemisimpleRing _ _

end GlobalTheory
end
