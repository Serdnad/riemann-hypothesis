module

public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Bundle003
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Bundle001
public import Formalism.UnipotentAdelicQuotients.EllRegStep
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

lemma exists_smooth_ext {d : ℕ} {U : Set (E d)} {a : E d → ℂ} {x0 : E d} (hU : IsOpen U) (hx0 : x0 ∈ U)
    (ha : ContDiffOn ℝ ∞ a U) :
    ∃ r0 > 0, ball x0 (2 * r0) ⊆ U ∧ ∃ b : E d → ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      ∀ x ∈ closedBall x0 (2 * r0), b x = a x := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x0 hx0
  let χ : ContDiffBump x0 := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  refine ⟨R / 4, by positivity, ?_, fun x => ((χ x : ℝ) : ℂ) * a x, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith)).trans hRU
  · have hsub : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact (Metric.closedBall_subset_ball (by show 3 * R / 4 < R; linarith)).trans hRU
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt).mul
        ((ha x hx).contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hsub h)
      have hev : (fun x => ((χ x : ℝ) : ℂ) * a x) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro x hx
    have hx' : x ∈ Metric.closedBall x0 χ.rIn := by
      show x ∈ Metric.closedBall x0 (R / 2)
      exact Metric.closedBall_subset_closedBall (by linarith) hx
    simp [χ.one_of_mem_closedBall hx']

lemma norm_lt_of_psi_ne {d : ℕ} {ψ0 : E d → ℝ} (hψ0s : tsupport ψ0 ⊆ ball 0 2) {r : ℝ} (hr : 0 < r)
    {x x0 : E d} (hz : ψ0 (r⁻¹ • (x - x0)) ≠ 0) : ‖x - x0‖ < 2 * r := by
  have hmem : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2 := hψ0s (subset_tsupport _ hz)
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
  rw [inv_mul_lt_iff₀ hr] at hmem
  linarith

theorem frozenKernelSmall : KernelSmall := by
  intro d U a x0 ψ0 hU hx0 ha hψ hψc hψs
  obtain ⟨r0, hr0, hball, b, hb, hbc, hab⟩ := exists_smooth_ext hU hx0 ha
  have hψC : ContDiff ℝ ∞ (fun y : E d => ((ψ0 y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hψCc : HasCompactSupport (fun y : E d => ((ψ0 y : ℝ) : ℂ)) := hψc.comp_left Complex.ofReal_zero
  set n := Module.finrank ℝ (E d) + 1 with hn
  obtain ⟨K, hK⟩ := derivL1Norm_rescaled_difference_le (fun y => ((ψ0 y : ℝ) : ℂ)) hψC hψCc b hb hbc x0 r0 n
  set I := ∫⁻ w : E d, ENNReal.ofReal ((1 + ‖w‖) ^ (-((n : ℕ) : ℝ))) with hIdef
  have hI : I < ⊤ := finite_integral_one_add_norm (by rw [hn]; push_cast; linarith)
  let c : ℝ → E d → ℂ := fun r y => ((ψ0 y : ℝ) : ℂ) * (b (x0 + r • y) - b x0)
  have hcs : ∀ r, ContDiff ℝ ∞ (c r) := fun r =>
    hψC.mul ((hb.comp (contDiff_const.add (contDiff_id.const_smul r))).sub contDiff_const)
  have hcc : ∀ r, HasCompactSupport (c r) := fun r => hψCc.mul_right
  have hf_eq : ∀ r : ℝ, 0 < r → r ≤ r0 →
      (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) = fun x => c r (r⁻¹ • (x - x0)) := by
    intro r hr hrr
    funext x
    have hx : x0 + r • (r⁻¹ • (x - x0)) = x := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    simp only [c, hx]
    by_cases hz : ψ0 (r⁻¹ • (x - x0)) = 0
    · simp [hz]
    · have hlt := norm_lt_of_psi_ne hψs hr hz
      have hxm : x ∈ closedBall x0 (2 * r0) := by
        rw [mem_closedBall, dist_eq_norm]; linarith
      rw [hab x hxm, hab x0 (mem_closedBall_self (by linarith))]
  refine ⟨r0, hr0, (2 ^ n * (1 + 2 ^ n)) * K * I.toReal, hball, fun r hr hrr => ⟨?_, fun N => ?_⟩⟩
  · rw [hf_eq r hr hrr]
    have h2 := hK r hr hrr
    have hKr : 0 ≤ K * r := (derivL1Norm_nonneg _ _).trans h2
    have hA : (0 : ℝ) ≤ 2 ^ n * (1 + 2 ^ n) := by positivity
    have hAKr : 0 ≤ 2 ^ n * (1 + 2 ^ n) * K * r := by
      rw [mul_assoc]; exact mul_nonneg hA hKr
    have hpt : ∀ ζ : E d, ‖𝓕 (fun x => c r (r⁻¹ • (x - x0))) ζ‖ₑ ≤
        ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) *
          ENNReal.ofReal (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by
      intro ζ
      rw [← ofReal_norm, norm_fourier_comp_dil _ r hr x0 ζ, ← ENNReal.ofReal_mul hAKr]
      apply ENNReal.ofReal_le_ofReal
      have h1 := norm_fourier_le_rpow (hcs r) (hcc r) n (r • ζ)
      have hW : 0 ≤ (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
      have hrd : 0 ≤ r ^ Module.finrank ℝ (E d) := by positivity
      calc r ^ Module.finrank ℝ (E d) * ‖𝓕 (c r) (r • ζ)‖
          ≤ r ^ Module.finrank ℝ (E d) *
              (2 ^ n * (1 + 2 ^ n) * derivL1Norm (c r) n * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hrd
        _ ≤ r ^ Module.finrank ℝ (E d) *
              (2 ^ n * (1 + 2 ^ n) * (K * r) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by
            gcongr
        _ = 2 ^ n * (1 + 2 ^ n) * K * r *
              (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by ring
    calc (∫⁻ ζ, ‖𝓕 (fun x => c r (r⁻¹ • (x - x0))) ζ‖ₑ)
        ≤ ∫⁻ ζ : E d, ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) *
          ENNReal.ofReal (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) * I := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_dil_weight r hr _ (by rw [hn]; push_cast; linarith)]
      _ = ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * I.toReal * r) := by
          rw [← ENNReal.ofReal_toReal hI.ne, ← ENNReal.ofReal_mul hAKr, ENNReal.toReal_ofReal
            ENNReal.toReal_nonneg]
          ring_nf
  · rw [hf_eq r hr hrr]
    have hsm : ContDiff ℝ ∞ (fun x => c r (r⁻¹ • (x - x0))) :=
      (hcs r).comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
    have hsc : HasCompactSupport (fun x => c r (r⁻¹ • (x - x0))) :=
      (hcc r).comp_homeomorph ((Homeomorph.subRight x0).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')))
    refine lt_of_le_of_lt (lintegral_mono fun ζ => ?_) (lintegral_weight_fourier_lt_top hsm hsc ⌈N + 1⌉₊)
    gcongr
    have h1 : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
    calc ‖ζ‖ * (1 + ‖ζ‖) ^ N ≤ (1 + ‖ζ‖) ^ (1 : ℝ) * (1 + ‖ζ‖) ^ N := by
          rw [Real.rpow_one]; gcongr; linarith
      _ = (1 + ‖ζ‖) ^ (N + 1) := by rw [← Real.rpow_add (by linarith)]; ring_nf
      _ ≤ (1 + ‖ζ‖) ^ ((⌈N + 1⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
      _ = (1 + ‖ζ‖) ^ ⌈N + 1⌉₊ := Real.rpow_natCast _ _

end

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma om_nonneg {d : ℕ} (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om
  exact mul_nonneg (Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) _)
    (Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _))) _)

lemma om_continuous_eps {d : ℕ} (s M : ℝ) (ξ : E d) : Continuous fun ε : ℝ => om s M ε ξ := by
  unfold om
  exact continuous_const.mul
    ((continuous_const.add ((continuous_pow 2).mul continuous_const)).rpow_const
      fun ε => Or.inl (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne')

lemma om_eps_zero {d : ℕ} (s M : ℝ) (ξ : E d) : om s M 0 ξ = om s 0 0 ξ := by
  unfold om
  simp

lemma om_continuous {d : ℕ} (s M ε : ℝ) : Continuous fun ξ : E d => om s M ε ξ := by
  unfold om
  exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').mul
    ((continuous_const.add (continuous_const.mul (continuous_norm.pow 2))).rpow_const
      fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne')

theorem weightedNormLimit : EpsLimit := by
  unfold EpsLimit
  intro d s M F B hM hF hB
  unfold nrm at hB ⊢
  have he0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : ∀ ξ : E d, Tendsto
      (fun n : ℕ => ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop
      (𝓝 (ENNReal.ofReal (om s 0 0 ξ) ^ 2 * ‖F ξ‖ₑ ^ 2)) := by
    intro ξ
    have h1 : Tendsto (fun n : ℕ => om s M (1 / ((n : ℝ) + 1)) ξ) atTop
        (𝓝 (om s 0 0 ξ)) := by
      rw [← om_eps_zero s M ξ]
      exact ((om_continuous_eps s M ξ).tendsto 0).comp he0
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2) atTop
        (𝓝 (ENNReal.ofReal (om s 0 0 ξ) ^ 2)) := by
      exact ((ENNReal.continuous_pow 2).tendsto _).comp ((ENNReal.continuous_ofReal.tendsto _).comp h1)
    have hfin : ‖F ξ‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
    exact ENNReal.Tendsto.mul_const h2 (Or.inr hfin)
  have hmeas : ∀ n : ℕ, Measurable fun ξ : E d =>
      ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2 := fun n => by
    have hc := om_continuous (d := d) s M (1 / ((n : ℝ) + 1))
    exact ((ENNReal.measurable_ofReal.comp hc.measurable).pow_const 2).mul
      (hF.measurable.enorm.pow_const 2)
  calc ∫⁻ ξ, ENNReal.ofReal (om s 0 0 ξ) ^ 2 * ‖F ξ‖ₑ ^ 2
      = ∫⁻ ξ, liminf (fun n : ℕ =>
          ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop :=
        lintegral_congr fun ξ => ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ ξ,
          ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ B := by
        refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hB _ (hpos n) (hle1 n))

private theorem rpow_le_rpow_of_le_of_exponent_nonpos {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  exact Real.rpow_le_rpow_of_nonpos hx hxy hz

private theorem sq_one_add_rpow_mul_rpow_le_max_mul_rpow (s M ε t : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) :
    ((1 + t) ^ (s / 2) * (1 + ε ^ 2 * t) ^ (-(M / 2))) ^ 2 ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (s - M) := by
  have hA : 0 < 1 + t := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hB : 0 < 1 + ε ^ 2 * t := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hε2.le ht)
  have ha : 0 < min 1 (ε ^ 2) := lt_min one_pos hε2
  have hb : 0 < max 1 (ε ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : ((1 + t) ^ (s / 2)) ^ 2 = (1 + t) ^ s := by
    rw [sq ((1 + t) ^ (s / 2)), ← Real.rpow_add hA]
    congr 1
    ring
  have h2 : ((1 + ε ^ 2 * t) ^ (-(M / 2))) ^ 2 = (1 + ε ^ 2 * t) ^ (-M) := by
    rw [sq ((1 + ε ^ 2 * t) ^ (-(M / 2))), ← Real.rpow_add hB]
    congr 1
    ring
  have hAp : 0 ≤ (1 + t) ^ (-M) := Real.rpow_nonneg hA.le _
  have key : (1 + ε ^ 2 * t) ^ (-M) ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) := by
    rcases le_total 0 M with hM | hM
    · have hle : min 1 (ε ^ 2) * (1 + t) ≤ 1 + ε ^ 2 * t := by
        have e1 : min 1 (ε ^ 2) ≤ 1 := min_le_left _ _
        have e2 : min 1 (ε ^ 2) * t ≤ ε ^ 2 * t := mul_le_mul_of_nonneg_right (min_le_right _ _) ht
        nlinarith
      calc (1 + ε ^ 2 * t) ^ (-M) ≤ (min 1 (ε ^ 2) * (1 + t)) ^ (-M) :=
            rpow_le_rpow_of_le_of_exponent_nonpos (mul_pos ha hA) hle (by linarith)
        _ = (min 1 (ε ^ 2)) ^ (-M) * (1 + t) ^ (-M) := Real.mul_rpow ha.le hA.le
        _ ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hAp
    · have hle : 1 + ε ^ 2 * t ≤ max 1 (ε ^ 2) * (1 + t) := by
        have e1 : 1 ≤ max 1 (ε ^ 2) := le_max_left _ _
        have e2 : ε ^ 2 * t ≤ max 1 (ε ^ 2) * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht
        nlinarith
      calc (1 + ε ^ 2 * t) ^ (-M) ≤ (max 1 (ε ^ 2) * (1 + t)) ^ (-M) :=
            Real.rpow_le_rpow hB.le hle (by linarith)
        _ = (max 1 (ε ^ 2)) ^ (-M) * (1 + t) ^ (-M) := Real.mul_rpow hb.le hA.le
        _ ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hAp
  rw [mul_pow, h1, h2, sub_eq_add_neg, Real.rpow_add hA]
  calc (1 + t) ^ s * (1 + ε ^ 2 * t) ^ (-M)
      ≤ (1 + t) ^ s * (max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M)) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg hA.le _)
    _ = max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * ((1 + t) ^ s * (1 + t) ^ (-M)) := by
        ring

lemma om_sq_le {d : ℕ} (s M ε : ℝ) (hε : 0 < ε) (ξ : E d) :
    om s M ε ξ ^ 2 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) := by
  unfold om
  exact sq_one_add_rpow_mul_rpow_le_max_mul_rpow s M ε _ hε (by positivity)

theorem weightedNormFinite : FiniteWeighted := by
  unfold FiniteWeighted
  intro d g hg hgc s M ε hε hsM
  unfold nrm
  have hint0 : Integrable (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * (M - s)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  have hexp : -(2 * (M - s)) / 2 = s - M := by ring
  rw [hexp] at hint0
  have hint_r := (hint0.const_mul (max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)))).mul_const
    ((∫ x, ‖g x‖) ^ 2)
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hint_r.lintegral_lt_top
  have hK : 0 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) :=
    le_max_of_le_right (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hw := om_nonneg s M ε ξ
  have hreal : om s M ε ξ ^ 2 * ‖𝓕 g ξ‖ ^ 2 ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) *
        (∫ x, ‖g x‖) ^ 2 := by
    refine mul_le_mul (om_sq_le s M ε hε ξ) ?_ (sq_nonneg _)
      (mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
    rw [sq, sq]
    exact mul_self_le_mul_self (norm_nonneg _) (norm_fourier_le_integral_norm g ξ)
  have heq : ENNReal.ofReal (om s M ε ξ) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2 =
      ENNReal.ofReal (om s M ε ξ ^ 2 * ‖𝓕 g ξ‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hw, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  exact heq.trans_le (ENNReal.ofReal_le_ofReal hreal)

end ZetaZeros.D.EllReg
end
