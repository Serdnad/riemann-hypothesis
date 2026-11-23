module

public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle027
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Bundle001
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernGr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace ZetaZeros.D.EllReg

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

private lemma conv_sq_le (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) (ξ : E d) :
    (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := by
  first | exact UpperTheory.Reformulated.B.Qj8.conv_sq_le .. | (apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg ξ | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d

private lemma conv_young (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) :
    ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η ^ 2) :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := lintegral_mono fun ξ => conv_sq_le k g hk hg ξ
    _ = (∫⁻ ζ, k ζ) * ∫⁻ ξ, ∫⁻ η, k (ξ - η) * g η ^ 2 :=
      lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, ∫⁻ ξ, k (ξ - η) * g η ^ 2 := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, (∫⁻ ζ, k ζ) * g η ^ 2 := by
      congr 1
      refine lintegral_congr fun η => ?_
      rw [lintegral_mul_const _ (show Measurable fun ξ => k (ξ - η) from hk.comp (measurable_id.sub measurable_const)),
        lintegral_sub_right_eq_self k η]
    _ = (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
      rw [lintegral_const_mul _ (hg.pow_const 2)]; ring

private lemma om_measurable (s M ε : ℝ) : Measurable (om (d := d) s M ε) := by
  unfold om; fun_prop

private lemma om_nonneg (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om; positivity

theorem convolution_bound : ConvBound := by
  intro d s M ε C N hC hom K F hK hF
  have hKm : Measurable K := hK.measurable
  have hFm : Measurable F := hF.measurable
  obtain ⟨k1, hk1e⟩ : ∃ k1 : E d → ℝ≥0∞, k1 = fun ζ => ‖K ζ‖ₑ := ⟨_, rfl⟩
  obtain ⟨k3, hk3e⟩ : ∃ k3 : E d → ℝ≥0∞, k3 = fun ζ => ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ :=
    ⟨_, rfl⟩
  obtain ⟨k2, hk2e⟩ : ∃ k2 : E d → ℝ≥0∞, k2 = fun ζ => ENNReal.ofReal C * k3 ζ := ⟨_, rfl⟩
  obtain ⟨g1, hg1e⟩ : ∃ g1 : E d → ℝ≥0∞, g1 = fun η => ENNReal.ofReal (om s M ε η) * ‖F η‖ₑ := ⟨_, rfl⟩
  obtain ⟨g2, hg2e⟩ : ∃ g2 : E d → ℝ≥0∞, g2 = fun η => ENNReal.ofReal (om (s - 1) M ε η) * ‖F η‖ₑ :=
    ⟨_, rfl⟩
  have hk1 : Measurable k1 := by rw [hk1e]; exact hKm.enorm
  have hk3 : Measurable k3 := by
    rw [hk3e]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hKm.enorm
  have hk2 : Measurable k2 := by rw [hk2e]; exact measurable_const.mul hk3
  have hg1 : Measurable g1 := by
    rw [hg1e]; exact (ENNReal.measurable_ofReal.comp (om_measurable s M ε)).mul hFm.enorm
  have hg2 : Measurable g2 := by
    rw [hg2e]; exact (ENNReal.measurable_ofReal.comp (om_measurable (s - 1) M ε)).mul hFm.enorm
  have hprod : ∀ k g : E d → ℝ≥0∞, Measurable k → Measurable g →
      Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η) := fun k g hk hg =>
    (hk.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
  have hT1 : Measurable fun ξ => ∫⁻ η, k1 (ξ - η) * g1 η := (hprod k1 g1 hk1 hg1).lintegral_prod_right'
  have hT2 : Measurable fun ξ => ∫⁻ η, k2 (ξ - η) * g2 η := (hprod k2 g2 hk2 hg2).lintegral_prod_right'

  have hpt : ∀ ξ, ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ ≤
      (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := by
    intro ξ
    have h1 : ‖conv K F ξ‖ₑ ≤ ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by
      unfold conv
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun η => ?_
      rw [enorm_mul]
    have hmeas : Measurable fun η => k1 (ξ - η) * g1 η :=
      (hk1.comp (measurable_const.sub measurable_id)).mul hg1
    calc ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ
        ≤ ENNReal.ofReal (om s M ε ξ) * ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by gcongr
      _ = ∫⁻ η, ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, (k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η) := by
        refine lintegral_mono fun η => ?_
        have hr : om s M ε ξ ≤ om s M ε η + C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η := by
          have h := hom ξ η
          have h' := le_abs_self (om s M ε ξ - om s M ε η)
          linarith
        have hX : 0 ≤ ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N := by positivity
        have hY := om_nonneg (s - 1) M ε η
        have he : ENNReal.ofReal (om s M ε ξ) ≤ ENNReal.ofReal (om s M ε η) +
            ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η)) := by
          rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_add (om_nonneg s M ε η) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_le_of_eq hr (by ring))
        calc ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ)
            ≤ (ENNReal.ofReal (om s M ε η) + ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η))) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) := by gcongr
          _ = k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η := by
            rw [hk1e, hk2e, hk3e, hg1e, hg2e]; ring
      _ = (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := lintegral_add_left hmeas _
  have hn : nrm s M ε (conv K F) ≤
      ∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ) := by
    unfold nrm
    refine lintegral_mono fun ξ => ?_
    rw [ENNReal.rpow_two, ← mul_pow]
    gcongr
    exact hpt ξ
  have hY : ∀ (k g : E d → ℝ≥0∞), Measurable k → Measurable g →
      (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
    intro k g hk hg
    have h := conv_young k g hk hg
    simp only [← ENNReal.rpow_two] at h ⊢
    calc (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ((∫⁻ ζ, k ζ) ^ (2 : ℝ) * ∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
  have e1 : ∫⁻ η, g1 η ^ 2 = nrm s M ε F := by
    unfold nrm; rw [hg1e]; simp only [mul_pow]
  have e2 : ∫⁻ η, g2 η ^ 2 = nrm (s - 1) M ε F := by
    unfold nrm; rw [hg2e]; simp only [mul_pow]
  have e3 : ∫⁻ ζ, k2 ζ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ := by
    rw [hk2e, lintegral_const_mul _ hk3, hk3e]
  have e4 : ∫⁻ ζ, k1 ζ = ∫⁻ ζ, ‖K ζ‖ₑ := by rw [hk1e]
  have hMk := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2) hT1.aemeasurable hT2.aemeasurable
    (by norm_num)
  simp only [Pi.add_apply] at hMk
  calc nrm s M ε (conv K F) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hn (by norm_num)
    _ ≤ (∫⁻ ξ, (∫⁻ η, k1 (ξ - η) * g1 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        (∫⁻ ξ, (∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hMk
    _ ≤ (∫⁻ ζ, k1 ζ) * (∫⁻ η, g1 η ^ 2) ^ (1 / 2 : ℝ) + (∫⁻ ζ, k2 ζ) * (∫⁻ η, g2 η ^ 2) ^ (1 / 2 : ℝ) :=
        add_le_add (hY k1 g1 hk1 hg1) (hY k2 g2 hk2 hg2)
    _ = _ := by rw [e1, e2, e3, e4]

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section



lemma derivL1Norm_rescaled_difference_le {d : ℕ} (ψ : E d → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (x0 : E d) (r0 : ℝ) (n : ℕ) :
    ∃ K : ℝ, ∀ r : ℝ, 0 < r → r ≤ r0 →
      derivL1Norm (fun y => ψ y * (b (x0 + r • y) - b x0)) n ≤ K * r := by
  classical
  have hinf : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun m => by exact_mod_cast le_top
  have hbnd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := (hb.continuous_iteratedFDeriv (hinf k)).norm.bddAbove_range_of_hasCompactSupport
      (hbc.iteratedFDeriv (𝕜 := ℝ) k).norm
    exact ⟨max M 0, le_max_right _ _, fun x => (hM ⟨x, rfl⟩).trans (le_max_left _ _)⟩
  choose M hM0 hM using hbnd
  obtain ⟨L0, hL0⟩ := (hb.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hbc.fderiv (𝕜 := ℝ)).norm
  have hL : ∀ x, ‖fderiv ℝ b x‖ ≤ max L0 0 := fun x => (hL0 ⟨x, rfl⟩).trans (le_max_left _ _)
  have hLn : 0 ≤ max L0 0 := le_max_right _ _
  have hR1 : 1 ≤ max 1 r0 := le_max_left _ _
  have hsumn : 0 ≤ ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hM0 k) (by positivity)
  have hAL : max L0 0 ≤ max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k :=
    le_add_of_nonneg_right hsumn
  have hAk : ∀ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k ≤
      max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k := fun k hk =>
    (Finset.single_le_sum (f := fun k => M k * (max 1 r0) ^ k)
      (fun k _ => mul_nonneg (hM0 k) (by positivity)) hk).trans (le_add_of_nonneg_left hLn)
  have hA0 : 0 ≤ max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k := hLn.trans hAL
  set A := max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k with hA
  let h : ℕ → E d → ℝ := fun j y =>
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)
  have hhi : ∀ j, Integrable (h j) := by
    intro j
    show Integrable (fun y =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖))
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    have h0 := integrable_iteratedFDeriv hψ hψc 0 i
    have h1 := integrable_iteratedFDeriv hψ hψc 1 i
    have he : (fun y => (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)) = fun y =>
        (j.choose i : ℝ) * (‖y‖ ^ 0 * ‖iteratedFDeriv ℝ i ψ y‖ + ‖y‖ ^ 1 * ‖iteratedFDeriv ℝ i ψ y‖) := by
      funext y
      ring
    rw [he]
    exact (h0.add h1).const_mul _
  refine ⟨A * ∑ j ∈ Finset.range (n + 1), ∫ y, h j y, fun r hr hr0 => ?_⟩
  have hg : ContDiff ℝ ∞ (fun y => b (x0 + r • y) - b x0) := by
    have h1 : ContDiff ℝ ∞ (fun y : E d => x0 + r • y) := by fun_prop
    exact (hb.comp h1).sub contDiff_const
  have hgb : ∀ k ∈ Finset.range (n + 1), ∀ y,
      ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ r * A * (1 + ‖y‖) := by
    intro k hk y
    have hy : 0 ≤ ‖y‖ := norm_nonneg _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [norm_iteratedFDeriv_zero]
      have h1 := gr_zero b hb (max L0 0) hL x0 y r hr
      nlinarith [mul_le_mul_of_nonneg_left hAL (mul_nonneg hr.le hy), mul_nonneg hr.le hA0]
    · have h1 := gr_pos b hb k hk0 (M k) (hM k) x0 y r hr
      have hrk : r ^ k ≤ r * (max 1 r0) ^ k := by
        calc r ^ k = r * r ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk0]
          _ ≤ r * (max 1 r0) ^ (k - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (hr0.trans (le_max_right _ _)) _) hr.le
          _ ≤ r * (max 1 r0) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (Nat.sub_le _ _)) hr.le
      have h2 : M k * r ^ k ≤ r * A := by
        calc M k * r ^ k ≤ M k * (r * (max 1 r0) ^ k) := mul_le_mul_of_nonneg_left hrk (hM0 k)
          _ = r * (M k * (max 1 r0) ^ k) := by ring
          _ ≤ r * A := mul_le_mul_of_nonneg_left (hAk k hk) hr.le
      nlinarith [mul_nonneg (mul_nonneg hr.le hA0) hy]
  have hpt : ∀ j ∈ Finset.range (n + 1), ∀ y,
      ‖iteratedFDeriv ℝ j (fun y => ψ y * (b (x0 + r • y) - b x0)) y‖ ≤ r * A * h j y := by
    intro j hj y
    refine (norm_iteratedFDeriv_mul_le hψ hg y (hinf j)).trans ?_
    simp only [h, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hji : j - i ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
    have h3 := hgb (j - i) hji y
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ := by positivity
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => b (x0 + r • y) - b x0) y‖
        ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (r * A * (1 + ‖y‖)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = r * A * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)) := by ring
  unfold derivL1Norm
  calc ∑ j ∈ Finset.range (n + 1), ∫ y, ‖iteratedFDeriv ℝ j (fun y => ψ y * (b (x0 + r • y) - b x0)) y‖
      ≤ ∑ j ∈ Finset.range (n + 1), ∫ y, r * A * h j y := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          ((hhi j).const_mul _) (Filter.Eventually.of_forall fun y => hpt j hj y)
    _ = (A * ∑ j ∈ Finset.range (n + 1), ∫ y, h j y) * r := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        ring

end

end ZetaZeros.D.EllReg
end
