module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
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
public import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.S.Pv.SchurTens

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]

private theorem aestronglyMeasurable_norm_sq {u : X → ℂ} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => ‖u x‖ ^ 2) μ := by
  exact hu.norm.pow 2

theorem memLp_two_of_lintegral {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp u 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hu).2 ⟨aestronglyMeasurable_norm_sq hu, ?_⟩
  have e : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2 := fun x => by
    rw [Real.enorm_of_nonneg (by positivity), enorm_sq_eq]
  rw [hasFiniteIntegral_iff_enorm]
  simp only [e]
  exact h

theorem lintegral_sq_eq {u : X → ℂ} (hu : MemLp u 2 μ) :
    ∫ x, ‖u x‖ ^ 2 ∂μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by
  have h0 : 0 ≤ᵐ[μ] fun x => ‖u x‖ ^ 2 := ae_of_all _ fun x => by
    exact sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae h0 (aestronglyMeasurable_norm_sq hu.aestronglyMeasurable)]
  congr 1
  exact lintegral_congr fun x => (enorm_sq_eq (u x)).symm

private theorem norm_conj_complex (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj z

theorem integrable_mul_conj {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hm : AEStronglyMeasurable (fun x => u x * conj (v x)) μ :=
    hu.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hv.aestronglyMeasurable)
  refine (hu2.add hv2).mono hm (ae_of_all _ fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ ‖‖u x‖ ^ 2 + ‖v x‖ ^ 2‖
  rw [norm_mul, norm_conj_complex, Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
    mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))]

private theorem mul_le_weighted_sq_add_half {a b t : ℝ} (ht : 0 < t) : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have ht1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + b ^ 2 / t := by
    linear_combination (t * a ^ 2 - 2 * a * b) * ht1
  linarith

theorem norm_integral_mul_conj_le {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) {t : ℝ} (ht : 0 < t) :
    ‖∫ x, u x * conj (v x) ∂μ‖ ≤ (t * ∫ x, ‖u x‖ ^ 2 ∂μ + (∫ x, ‖v x‖ ^ 2 ∂μ) / t) / 2 := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hR : Integrable (fun x => (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2) μ :=
    ((hu2.const_mul t).add (hv2.div_const t)).div_const 2
  have h1 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2 ∂μ
      = (∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ) / 2 := integral_div _ _
  have h2 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ
      = ∫ x, t * ‖u x‖ ^ 2 ∂μ + ∫ x, ‖v x‖ ^ 2 / t ∂μ :=
    integral_add (hu2.const_mul t) (hv2.div_const t)
  have h3 : ∫ x, t * ‖u x‖ ^ 2 ∂μ = t * ∫ x, ‖u x‖ ^ 2 ∂μ := integral_const_mul _ _
  have h4 : ∫ x, ‖v x‖ ^ 2 / t ∂μ = (∫ x, ‖v x‖ ^ 2 ∂μ) / t := integral_div _ _
  rw [← h4, ← h3, ← h2, ← h1]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_mul_conj hu hv).norm hR fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2
  rw [norm_mul, norm_conj_complex]
  exact mul_le_weighted_sq_add_half ht

private theorem lintegral_enorm_sub_limit_sq_le {f : ℕ → X → ℂ} {F : X → ℂ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) (n N : ℕ) {ε : ℝ≥0∞}
    (h : ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε) :
    ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ ≤ ε := by
  have hlim : ∀ x, Tendsto (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop (𝓝 (‖F x - f n x‖ₑ ^ 2)) := by
    intro x
    have h1 : Tendsto (fun m => f m x - f n x) atTop (𝓝 (F x - f n x)) := (hpt x).sub_const _
    have h2 : Tendsto (fun m => ‖f m x - f n x‖ₑ) atTop (𝓝 ‖F x - f n x‖ₑ) :=
      (continuous_enorm.tendsto _).comp h1
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h2
  have hmeas : ∀ m, AEMeasurable (fun x => ‖f m x - f n x‖ₑ ^ 2) μ := fun m =>
    (((hf m).sub (hf n)).enorm).pow_const 2
  have hfreq : ∃ᶠ m in atTop, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε :=
    (eventually_atTop.2 ⟨N, h⟩).frequently
  calc ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, liminf (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop ∂μ :=
        lintegral_congr fun x => ((hlim x).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le' (f := fun m x => ‖f m x - f n x‖ₑ ^ 2) hmeas
    _ ≤ ε := liminf_le_of_frequently_le' hfreq

theorem limit_memLp_and_integral_eq (f : ℕ → X → ℂ) (F g : X → ℂ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hFm : AEStronglyMeasurable F μ)
    (hg : MemLp g 2 μ) (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε)
    {L : ℂ} (hL : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 L)) :
    MemLp F 2 μ ∧ Integrable (fun x => F x * conj (g x)) μ ∧ ∫ x, F x * conj (g x) ∂μ = L := by
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n => (hf2 n).aestronglyMeasurable
  obtain ⟨N₀, hN₀⟩ := hC 1 one_pos
  have h0 := lintegral_enorm_sub_limit_sq_le hfm hpt N₀ N₀ (hN₀ N₀ le_rfl)
  have hsub0 : MemLp (fun x => F x - f N₀ x) 2 μ :=
    memLp_two_of_lintegral (hFm.sub (hf2 N₀).aestronglyMeasurable) (lt_of_le_of_lt h0 ENNReal.one_lt_top)
  have hF : MemLp F 2 μ := by
    have hadd := hsub0.add (hf2 N₀)
    convert hadd using 1
    ext x
    simp
  have hFg : Integrable (fun x => F x * conj (g x)) μ := integrable_mul_conj hF hg
  refine ⟨hF, hFg, ?_⟩
  have hlim : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 (∫ x, F x * conj (g x) ∂μ)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨G, hGe⟩ : ∃ G, ∫ x, ‖g x‖ ^ 2 ∂μ = G := ⟨_, rfl⟩
    have hG : 0 ≤ G := by
      rw [← hGe]
      exact integral_nonneg fun x => sq_nonneg _
    have hc : 0 < G + 1 := by linarith
    have hB : 0 < δ ^ 2 / (2 * (G + 1)) := div_pos (pow_pos hδ 2) (mul_pos two_pos hc)
    obtain ⟨N, hN⟩ := hC (ENNReal.ofReal (δ ^ 2 / (2 * (G + 1)))) (ENNReal.ofReal_pos.2 hB)
    refine ⟨N, fun n hn => ?_⟩
    show dist (∫ x, f n x * conj (g x) ∂μ) (∫ x, F x * conj (g x) ∂μ) < δ
    have hsub : MemLp (fun x => F x - f n x) 2 μ := hF.sub (hf2 n)
    have hlin := lintegral_enorm_sub_limit_sq_le hfm hpt n N (hN n hn)
    have hA : ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ ^ 2 / (2 * (G + 1)) := by
      rw [lintegral_sq_eq hsub]
      exact ENNReal.toReal_le_of_le_ofReal hB.le hlin
    have ht : 0 < (G + 1) / δ := div_pos hc hδ
    have hbound := norm_integral_mul_conj_le hsub hg ht
    rw [hGe] at hbound
    have hdiff : ∫ x, F x * conj (g x) ∂μ - ∫ x, f n x * conj (g x) ∂μ
        = ∫ x, (F x - f n x) * conj (g x) ∂μ := by
      rw [← integral_sub hFg (integrable_mul_conj (hf2 n) hg)]
      congr 1
      funext x
      ring
    rw [dist_eq_norm, norm_sub_rev, hdiff]
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hc0 : G + 1 ≠ 0 := hc.ne'
    have h1 : (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ / 2 := by
      calc (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ
          ≤ (G + 1) / δ * (δ ^ 2 / (2 * (G + 1))) := mul_le_mul_of_nonneg_left hA ht.le
        _ = δ / 2 := by field_simp
    have h2 : G / ((G + 1) / δ) < δ := by
      rw [div_div_eq_mul_div]
      rw [div_lt_iff₀ hc]
      nlinarith
    linarith
  exact tendsto_nhds_unique hlim hL

end Formalism.L2.S.Pv.SchurTens
end
end

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def yv (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) : HH :=
  ∫ z, ∫ s in Ω, ⟪W (s⁻¹ * z), e⟫_ℂ • σ (s⁻¹ * z) w ∂μS ∂ν

def Yop (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) : V →L[ℂ] HH :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ V i)).smulRight (yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i))

theorem Yop_apply (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) :
    Yop μS ν σ w W Ω e =
      ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
  simp only [Yop, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem Yop_apply_basis (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G)
    (j : Fin (Module.finrank ℂ V)) :
    Yop μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) := by
  rw [Yop_apply, Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal]; simp
  · intro i _ hij
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal, if_neg hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Formalism.L2.S.Pv.EnergyAbs
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

theorem lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by
  have hsec : ∀ s, Measurable (f s) := fun s =>
    hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))
  have hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS' := by
    intro s hs
    calc c * μS' E' ≤ c * μS' {s' | c ≤ f s s'} :=
          mul_le_mul' le_rfl (measure_mono fun s' hs' => h s hs s' hs')
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (hsec s).aemeasurable c
  have hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS') := hf.lintegral_prod_right'
  calc c * μS' E' * μS E ≤ c * μS' E' * μS {s | c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'} :=
        mul_le_mul' le_rfl (measure_mono fun s hs => hin s hs)
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hg.aemeasurable _

def folInt (Ω K : Set G) : Set G := {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

theorem measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm

theorem tendsto_ratio_ennreal {a b : ℕ → ℝ≥0∞} (hb0 : ∀ n, 0 < b n) (hbt : ∀ n, b n < ⊤)
    (hab : ∀ n, a n ≤ b n) (h : Tendsto (fun n => (a n).toReal / (b n).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have hfin : ∀ n, a n / b n ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'
  have hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal) := by
    funext n
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]
  rw [hfun, ← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h

theorem liminf_lower {μS μS' : Measure G} [SFinite μS'] [MeasurableInv G]
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (Ω Ω' : ℕ → Set G) (hΩ0 : ∀ n, 0 < μS (Ω n)) (hΩt : ∀ n, μS (Ω n) < ⊤)
    (hΩ0' : ∀ n, 0 < μS' (Ω' n)) (hΩt' : ∀ n, μS' (Ω' n) < ⊤)
    (f : ℕ → G → G → ℝ≥0∞) (hf : ∀ n, Measurable (fun p : G × G => f n p.1 p.2)) (h : ℝ) (hh : 0 ≤ h)
    (key : ∀ ε : ℝ, 0 < ε → ∃ K K' : Set G,
      Tendsto (fun n => μS (folInt (Ω n) K) / μS (Ω n)) atTop (𝓝 1) ∧
      Tendsto (fun n => μS' (folInt (Ω' n) K') / μS' (Ω' n)) atTop (𝓝 1) ∧
      ∀ n s s', s⁻¹ ∈ folInt (Ω n) K → s'⁻¹ ∈ folInt (Ω' n) K' →
        ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ f n s s') :
    ENNReal.ofReal h ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop := by
  set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop
    with hL
  have step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L := by
    intro ε hε
    obtain ⟨K, K', hK, hK', hf'⟩ := key ε hε
    set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc
    have hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) *
        (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c) := by
      have h1 := ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_one, mul_one] at h2
      exact h2
    rw [hL, ← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    have hA0 := (hΩ0 n).ne'
    have hAt := (hΩt n).ne
    have hmain := lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n)
      {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c
      (fun s hs s' hs' => hf' n s s' hs hs')
    rw [measure_inv_preimage hinv, measure_inv_preimage hinv'] at hmain
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]
    calc c * (μS (folInt (Ω n) K) * (μS (Ω n))⁻¹ *
          (μS' (folInt (Ω' n) K') * (μS' (Ω' n))⁻¹))
        = (μS (Ω n))⁻¹ * (μS' (Ω' n))⁻¹ *
          (c * μS' (folInt (Ω' n) K') * μS (folInt (Ω n) K)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hmain
  have hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h := by
    rw [sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]
  have hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal h)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)

end Formalism.L2.S.Pv.EnergyAbs
end
end
