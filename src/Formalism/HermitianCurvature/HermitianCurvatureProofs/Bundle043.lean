module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle039
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle035
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.HermitianCurvature.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section



namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

open Formalism.FourierDecayAlt.ThreeDimData

theorem smooth_admissible_form_one_side : AtFormAdmOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hZD hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => DDSmoothness.fdeg_eq hd hSd hx
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hAs : ∀ v : H, IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro v hv
    rcases hv with hv | hv
    · exact DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 v hv
    · exact hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    have hI : ∀ v : H, IsAdm σ w0 v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
      intro v hv x hx
      rcases hv with hv | hv
      · exact hid x hx v hv
      · exact hK v hv x hx
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v hv, hI v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv (l v)).1
    rw [hI v hv v (hAs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine DDSmoothness.l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hI v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have h0D := hZD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, DDSmoothness.bessel_zero, fun x hx v hv => ⟨hBC1 x hx v hv, ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    have hz0 : be z c π σ μW μN x v = 0 := by
      rcases hv with hv | hv
      · exact h0D v hv x hx
      · exact h0 v hv x hx
    rw [hz0]
    ext ξ; simp

end UnipotentHaarMeasurability

theorem admissible_atomic_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOneOfSteps := UnipotentHaarMeasurability.smooth_admissible_form_one_side

end Formalism.FourierDecayAlt.P
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section



namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

end Formalism.FourierDecayAlt.P.DDSmoothness

namespace Formalism.FourierDecayAlt.P

theorem discrete_series_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.DDFormOneOfSteps := DDSmoothness.discrete_form_one_side

end Formalism.FourierDecayAlt.P
end
end

section

open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBB.K8

noncomputable section

def dw (c : ℂ) : ℝ := ((1 + ‖c‖) ^ 3)⁻¹

theorem dw_cont : Continuous dw :=
  ((continuous_const.add continuous_norm).pow 3).inv₀ fun c => pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg c)).ne'

theorem dw_integrable : Integrable dw := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem bound_all {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ} (h : ∀ c, c ≠ 0 → ‖f c‖ ≤ C * dw c) (c : ℂ) :
    ‖f c‖ ≤ C * dw c := by
  have hs : IsClosed {c : ℂ | ‖f c‖ ≤ C * dw c} :=
    isClosed_le (continuous_norm.comp hf) (continuous_const.mul dw_cont)
  have hsub : ({0}ᶜ : Set ℂ) ⊆ {c | ‖f c‖ ≤ C * dw c} := fun c hc => h c hc
  have := hs.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at this
  exact this (Set.mem_univ c)

theorem fourier_cont {f : ℂ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem ae_ne_zero : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
  simp [ae_iff]

theorem limit_fourier (g : ℕ → ℂ → ℂ) (g0 : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) (C C' : ℝ)
    (hφc : ∀ n, Continuous (φ n)) (hφg : ∀ n c, c ≠ 0 → φ n c = g n c)
    (hconv : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (g0 c)))
    (hb : ∀ n c, c ≠ 0 → ‖g n c‖ ≤ C * dw c)
    (hT : ∀ n w, ‖𝓕 (φ n) w‖ ≤ C' * dw w) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ c, c ≠ 0 → ψ c = g0 c) ∧ (∀ c, ‖ψ c‖ ≤ C * dw c) ∧
      Tendsto (fun n => ∫ c, φ n c) atTop (𝓝 (∫ c, ψ c)) := by
  have hφb : ∀ n c, ‖φ n c‖ ≤ C * dw c := fun n =>
    bound_all (hφc n) fun c hc => by rw [hφg n c hc]; exact hb n c hc
  have hBi : Integrable (fun c => C * dw c) := dw_integrable.const_mul C
  have hB'i : Integrable (fun c => C' * dw c) := dw_integrable.const_mul C'
  have hφi : ∀ n, Integrable (φ n) := fun n =>
    hBi.mono' (hφc n).aestronglyMeasurable (Eventually.of_forall (hφb n))
  have hFt : ∀ w, Tendsto (fun n => 𝓕 (φ n) w) atTop (𝓝 (𝓕 g0 w)) := by
    intro w
    show Tendsto (fun n => ∫ v, 𝐞 (-⟪v, w⟫) • φ n v) atTop (𝓝 (∫ v, 𝐞 (-⟪v, w⟫) • g0 v))
    refine tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => ?_) hBi (fun n => ?_) ?_
    · exact ((Real.fourierIntegral_convergent_iff w).mpr (hφi n)).aestronglyMeasurable
    · exact Eventually.of_forall fun c => by rw [Circle.norm_smul]; exact hφb n c
    · filter_upwards [ae_ne_zero] with c hc
      simp only [hφg _ c hc]
      exact (hconv c).const_smul _
  have hGm : AEStronglyMeasurable (𝓕 g0) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (fourier_cont (hφi n)).aestronglyMeasurable)
      (ae_of_all _ hFt)
  have hGb : ∀ w, ‖𝓕 g0 w‖ ≤ C' * dw w := fun w => le_of_tendsto' (hFt w).norm fun n => hT n w
  have hGi : Integrable (𝓕 g0) := hB'i.mono' hGm (Eventually.of_forall hGb)
  have hinv : ∀ n, 𝓕⁻ (𝓕 (φ n)) = φ n := fun n =>
    (hφc n).fourierInv_fourier_eq (hφi n)
      (hB'i.mono' (fourier_cont (hφi n)).aestronglyMeasurable (Eventually.of_forall (hT n)))
  set ψ : ℂ → ℂ := 𝓕⁻ (𝓕 g0) with hψ
  have hψlim : ∀ c, Tendsto (fun n => φ n c) atTop (𝓝 (ψ c)) := by
    intro c
    have : (fun n => φ n c) = fun n => 𝓕⁻ (𝓕 (φ n)) c := funext fun n => by rw [hinv n]
    rw [this, hψ]
    simp only [Real.fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun w => C' * dw w) (fun n => ?_) hB'i (fun n => ?_) ?_
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (fourier_cont (hφi n))).aestronglyMeasurable
    · exact Eventually.of_forall fun w => by rw [Circle.norm_smul]; exact hT n w
    · exact ae_of_all _ fun w => (hFt w).const_smul _
  refine ⟨ψ, ?_, fun c hc => ?_, fun c => le_of_tendsto' (hψlim c).norm fun n => hφb n c, ?_⟩
  · have : ψ = fun c => 𝓕 (𝓕 g0) (-c) := funext fun c => Real.fourierInv_eq_fourier_neg _ c
    rw [this]
    exact (fourier_cont hGi).comp continuous_neg
  · refine tendsto_nhds_unique (hψlim c) ?_
    have : (fun n => φ n c) = fun n => g n c := funext fun n => hφg n c hc
    rw [this]
    exact hconv c
  · exact tendsto_integral_of_dominated_convergence (fun c => C * dw c)
      (fun n => (hφc n).aestronglyMeasurable) hBi (fun n => ae_of_all _ (hφb n)) (ae_of_all _ hψlim)

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def Lm (g : ℕ) (l : ℂ) : ℂ := -(((2 / (g : ℝ) : ℝ)) : ℂ) * conj l

theorem psiL_eq (S : C.HidaSetting E Wp Wq) (l c z : ℂ) :
    z * KB.psiL S l c = 𝐞 (-⟪c, Lm S.g l⟫) • z := by
  rw [Circle.smul_def, Real.fourierChar_apply, KB.psiL, mul_comm z]
  congr 2
  have hi : ⟪c, Lm S.g l⟫ = -(2 / (S.g : ℝ)) * (l * c).re := by
    simp [Lm, Complex.inner, Complex.mul_re]
    ring
  rw [hi]
  push_cast
  ring

theorem Lm_inv (g : ℕ) (hg : (g : ℝ) ≠ 0) (w : ℂ) : Lm g ((((-(g : ℝ) / 2 : ℝ)) : ℂ) * conj w) = w := by
  simp only [Lm, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  have : (-(2 / (g : ℝ)) * (-(g : ℝ) / 2)) = 1 := by field_simp
  rw [this]
  simp

theorem decay_scale (g : ℝ) (hg : 1 ≤ g) (w : ℂ) :
    ((1 + ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖) ^ 3)⁻¹ ≤ 8 * dw w := by
  have hn : ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖ = g / 2 * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < g)]
    norm_num
  rw [hn]
  have h0 : 0 < (1 + ‖w‖) / 2 := by positivity
  have h1 : (1 + ‖w‖) / 2 ≤ 1 + g / 2 * ‖w‖ := by nlinarith [norm_nonneg w]
  calc ((1 + g / 2 * ‖w‖) ^ 3)⁻¹ ≤ (((1 + ‖w‖) / 2) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h1 3)
    _ = 8 * dw w := by unfold dw; field_simp; ring

theorem g_ge_one (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : (1 : ℝ) ≤ S.g := by
  have : 1 ≤ S.g := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg1.ne' hg2.ne')
  exact_mod_cast this

theorem gramLoc_tendsto (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : C.LPt) :
    Tendsto (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) p q) atTop
      (𝓝 (S.gramLoc v ε i (w.1 v) p q)) :=
  (hconv v ε hε i _ ⟨w, rfl⟩ p q).const_mul _

theorem intAll_limit (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hB : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 →
      ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
          ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c‖ ≤
          C * ((1 + ‖l‖) ^ 3)⁻¹) :
    KB.IntAll S := by
  intro v ε hε i hi1 hi2 w h h' hh hh'
  obtain ⟨C, hC⟩ := hB v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ h h' hh hh'
  have hC0 : 0 ≤ C := by
    have := ((hC 0).2 0).trans' (norm_nonneg _)
    simpa using this
  have H := fun n => hInt n v ε hε i hi1 hi2 w h h' hh hh'
  choose φ hφc hφe hφb hφi using H
  have hg := g_ge_one S hg1 hg2
  have hT : ∀ n w', ‖𝓕 (φ n) w'‖ ≤ 8 * C * dw w' := by
    intro n w'
    set l : ℂ := (((-(S.g : ℝ) / 2 : ℝ)) : ℂ) * conj w' with hl
    have hLm : Lm S.g l = w' := Lm_inv S.g (by linarith) w'
    have he : 𝓕 (φ n) w' = ∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) *
        KB.psiL S l c := by
      rw [Real.fourier_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero] with c hc
      rw [psiL_eq, hLm, hφe n c hc]
    rw [he]
    have h8 := mul_le_mul_of_nonneg_left (decay_scale S.g hg w') hC0
    calc _ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹ := (hC n).2 l
      _ ≤ C * (8 * dw w') := h8
      _ = 8 * C * dw w' := by ring
  obtain ⟨ψ, hψc, hψe, hψb, hψi⟩ := limit_fourier
    (fun n c => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]))
    (fun c => S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) φ C (8 * C) hφc hφe
    (fun c => gramLoc_tendsto S RR hconv v hε i w _ _) (fun n c hc => (hC n).1 c hc) hT
  refine ⟨ψ, hψc, hψe, ⟨C, hψb⟩, ?_⟩
  have h1 : Tendsto (fun n => ∫ c, φ n c) atTop
      (𝓝 (((KB.dlB S i 1 : ℝ) : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h')) := by
    have : (fun n => ∫ c, φ n c) =
        fun n => ((KB.dlB S i 1 : ℝ) : ℂ) * (KB.withRR S (RR n)).gramLoc v ε (i - 1) (w.1 v) h h' :=
      funext fun n => hφi n
    rw [this]
    exact (gramLoc_tendsto S RR hconv v hε (i - 1) w h h').const_mul _
  exact tendsto_nhds_unique hψi h1

end setting

end

end Formalism.FourierDecayAlt.P.PBB.K8
end

section

open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem pair_prob {W : Type} {s t : Finset W} {a b : W → ℝ} (ha : TB.IsProb s a) (hb : TB.IsProb t b) :
    TB.IsProb (s ×ˢ t) (fun x => a x.1 * b x.2) := by
  refine ⟨fun x => mul_nonneg (ha.1 _) (hb.1 _), fun x hx => ?_, ?_⟩
  · rw [Finset.mem_product, not_and_or] at hx
    rcases hx with h | h
    · simp [ha.2.1 _ h]
    · simp [hb.2.1 _ h]
  · rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum, hb.2.2, mul_one]
    exact ha.2.2

theorem sum_pair {W : Type} (s t : Finset W) (a b f g : W → ℝ) (hb : ∑ y ∈ t, b y = 1)
    (ha : ∑ x ∈ s, a x = 1) :
    ∑ x ∈ s ×ˢ t, a x.1 * b x.2 * ((f x.1 + g x.2) / 2) =
      ((∑ x ∈ s, a x * f x) + ∑ y ∈ t, b y * g y) / 2 := by
  have key : ∀ x, ∑ y ∈ t, a x * b y * ((f x + g y) / 2) =
      (a x * f x + a x * ∑ y ∈ t, b y * g y) / 2 := by
    intro x
    have split : ∀ y, a x * b y * ((f x + g y) / 2) =
        (a x * f x / 2) * b y + (a x / 2) * (b y * g y) := by
      intro y; ring
    simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_product]
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ha]
  ring

theorem mix_sum {X W : Type} (Y : Finset X) (Ws : Finset W) (κ : X → X → ℂ) (c : ℂ) (p : W → ℂ)
    (G : W → X → X → ℂ) :
    ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (c * ∑ w ∈ Ws, p w * G w h h') =
      c * ∑ w ∈ Ws, p w * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G w h h' := by
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun h' _ => ?_
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

theorem av_eq (v : Fin S.f) (x : E) : S.base.av v x = ‖S.σ v x‖ := by
  show (S.pl v) x = ‖S.emb v x‖
  rw [← S.hemb v]
  rfl

theorem loc_join (σ : E →+* ℂ) (h : TB.Pt E) (s : ℕ) (t : E) :
    C.loc σ (TB.join h s t) = C.loc σ h ++ [(s, σ t)] := by
  simp only [C.loc, TB.join, List.map_append, List.map_cons, List.map_nil]

theorem ptSize_loc (σ : E →+* ℂ) (h : TB.Pt E) : D.ptSize (C.loc σ h) = TB.level h := by
  simp only [D.ptSize, C.loc, TB.level, List.map_map]
  rfl

theorem sizeAt_nonneg (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem gN_psd (hpos : C.ThmPPos S) (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) {i : ℕ} (hi : i ≤ S.G.r + 1) (w0 : S.W)
    (Y : Finset C.LPt) : TB.PSDOn Y (KB.gN S v ε i (w0.1 v)) := by
  have h := hpos v ε hε i hi w0 Y
  unfold TB.PSDOn at h ⊢
  have heq : (Matrix.of fun x y : Y => KB.gN S v ε i (w0.1 v) x y) =
      (((S.sizeAt v (w0.1 v))⁻¹ : ℝ) : ℂ) • Matrix.of fun x y : Y => S.gramLoc v ε i (w0.1 v) x y := by
    ext x y
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, KB.gN, div_eq_inv_mul,
      Complex.ofReal_inv]
  rw [heq]
  exact h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (sizeAt_nonneg S v _)))

theorem Nst_eq {ε : ℝ} {i : ℕ} (hi : i ≤ S.G.r + 1) (s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    S.base.Nst ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, KB.gN S v ε i (w.1 v)
      (C.loc (S.σ v) h ++ [(s, S.σ v t)]) (C.loc (S.σ v) h' ++ [(s, S.σ v t')]) := by
  have hsz : ((C.Word.size S.P w.1 : ℝ) : ℂ) = ∏ v, ((S.sizeAt v (w.1 v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    rfl
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) /
      ((C.Word.size S.P w.1 : ℝ) : ℂ) = _
  simp only [C.HidaSetting.gram, if_pos hi, loc_join, KB.gN, Finset.prod_div_distrib, hsz,
    Finset.sum_div, mul_div_assoc]

end

end Formalism.FourierDecayAlt.P.PBA
end

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def Good {f : ℕ} (x : crystallineComparison.V f) : Prop := ∀ v, x v ≠ 0

def blk {α : Type} (a w b : α → α → ℂ) : α ⊕ α → α ⊕ α → ℂ := fun x y =>
  match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff {α : Type} (Y : Finset α) (a w b : α → α → ℂ) :
    KB.BlockPSD Y Y a w b ↔ TB.PSDOn (Y.disjSum Y) (blk a w b) := by
  unfold KB.BlockPSD
  constructor <;> intro h <;> convert h using 1 <;> funext x y <;>
    rcases x with p | p <;> rcases y with q | q <;> rfl

variable {H : Type} {f : ℕ}

def phi (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, K v (h, x v) (h', x' v)

def phiR (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  phi Y κ U x x' - phi Y κ P x x' - conj (phi Y κ P x' x) + phi Y κ Q x x'

def hd : (H × crystallineComparison.V f) ⊕ (H × crystallineComparison.V f) → H := Sum.elim (fun p => p.1) (fun p => p.1)

end

end Formalism.FourierDecayAlt.P.PBC
end
