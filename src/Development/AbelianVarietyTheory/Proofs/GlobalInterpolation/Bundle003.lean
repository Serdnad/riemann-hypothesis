module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

open MeasureTheory FourierTransform

namespace GlobalTheory


open MeasureTheory FourierTransform in
theorem _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : V ≃L[ℝ] E) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ a : ℝ, 0 < a ∧ (∀ g : E → ℂ, ∫ x, g (T x) ∂μ = (a : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (T x)) μ ↔ Integrable g := by
  let e : V ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have : (μ.map e).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  set c := (μ.map e).addHaarScalarFactor volume
  have hpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hpos, fun g => ?_, fun g => ?_⟩
  · change ∫ x, g (e x) ∂μ = _
    rw [← integral_map_equiv e, hmap, integral_smul_nnreal_measure]
    simp [NNReal.smul_def, Complex.real_smul]
  · change Integrable (g ∘ e) μ ↔ _
    rw [← integrable_map_equiv e, hmap,
      show c • (volume : Measure E) = (c : ENNReal) • volume from rfl, integrable_smul_measure]
    · simpa using hpos.ne'
    · simp


open MeasureTheory FourierTransform in
theorem _root_.GlobalTheory.exists_equiv_inner_eq_form {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : V ≃L[ℝ] E) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ R : V ≃L[ℝ] E, ∀ x y, B x y = inner ℝ (T x) (R y) := by
  let φ : V → StrongDual ℝ E := fun y =>
    LinearMap.toContinuousLinearMap ((B.flip y).comp (T.symm : E →L[ℝ] V).toLinearMap)
  have hφ : ∀ y e, φ y e = B (T.symm e) y := fun _ _ => rfl
  let L : V →ₗ[ℝ] E :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm (φ y)
      map_add' := fun y z => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ]
      map_smul' := fun r y => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ] }
  have hL : ∀ x y, inner ℝ (T x) (L y) = B x y := by
    intro x y
    rw [real_inner_comm]
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (φ y)) (T x) = _
    rw [InnerProductSpace.toDual_symm_apply, hφ, T.symm_apply_apply]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hn y
    intro x
    rw [hs, ← hL, hy, inner_zero_right]
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E := T.toLinearEquiv.finrank_eq
  refine ⟨(LinearMap.linearEquivOfInjective L hinj hdim).toContinuousLinearEquiv, fun x y => ?_⟩
  rw [← hL]
  rfl


open MeasureTheory FourierTransform in
theorem _root_.GlobalTheory.fourier_inversion_haar_symm_form :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ x y, B x y = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∃ c : ℝ, 0 < c ∧ ∀ Φ : V → ℂ, Continuous Φ → Integrable Φ μ → Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ → ∀ z, ∫ y, (∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) * Complex.exp (2 * Real.pi * Complex.I * ((B y z : ℝ) : ℂ)) ∂μ = (c : ℂ) * Φ (-z)) ∧ ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ := by
  intro V _ _ _ _ _ B hs hn μ hμ
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let T : V ≃L[ℝ] E := (LinearEquiv.ofFinrankEq V E (by simp [E])).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, hint, hintg⟩ := _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  obtain ⟨b, hb, hint', hintg'⟩ := _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar R μ
  have hF : ∀ (g : E → ℂ) w, 𝓕⁻ g w =
      ∫ v, g v * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ v w : ℝ) : ℂ)) := by
    intro g w
    rw [Real.fourierInv_eq']
    congr 1
    ext v
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  have key : ∀ (Φ : V → ℂ) y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ
      = a * 𝓕⁻ (fun w => Φ (T.symm w)) (R y) := by
    intro Φ y
    rw [hF, ← hint]
    simp only [hR, ContinuousLinearEquiv.symm_apply_apply]
  have hFF : ∀ g : E → ℂ, Continuous g → Integrable g → Integrable (𝓕⁻ g) → ∀ w,
      𝓕⁻ (𝓕⁻ g) w = g (-w) := by
    intro g hc hg hg' w
    have h1 : 𝓕 g = fun w => 𝓕⁻ g (-w) := by
      ext w
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    have h2 : Integrable (𝓕 g) := by
      rw [h1]
      exact hg'.comp_neg
    rw [Real.fourierInv_eq_fourier_neg, hc.fourier_fourierInv_eq hg h2]
  refine ⟨⟨a * b, mul_pos ha hb, fun Φ hc hΦ hI z => ?_⟩, fun Φ => ?_⟩
  · set g : E → ℂ := fun w => Φ (T.symm w) with hg
    have hgc : Continuous g := hc.comp T.symm.continuous
    have hgi : Integrable g := by
      rw [← hintg]
      simpa [g] using hΦ
    have hgi' : Integrable (𝓕⁻ g) := by
      rw [← hintg']
      have := hI.const_mul ((a : ℂ)⁻¹)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [key, ← hg, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha.ne'), one_mul]
    simp only [key Φ, ← hg]
    have hB : ∀ y, B y z = inner ℝ (R y) (T z) := fun y => by rw [hs, hR, real_inner_comm]
    simp only [hB]
    rw [hint' (fun u => (a : ℂ) * 𝓕⁻ g u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)))]
    simp only [mul_assoc (a : ℂ)]
    rw [integral_const_mul, ← hF, hFF g hgc hgi hgi', hg]
    beta_reduce
    rw [← map_neg T z, ContinuousLinearEquiv.symm_apply_apply]
    push_cast
    ring
  · refine ⟨Φ.integrable, ?_⟩
    let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T.symm Φ
    have hψ : (fun w => Φ (T.symm w)) = ⇑ψ := by
      ext w
      simp [ψ]
    simp only [key, hψ, ← SchwartzMap.fourierInv_coe]
    refine Integrable.const_mul ?_ _
    rw [hintg' (⇑(𝓕⁻ ψ : SchwartzMap E ℂ))]
    exact (𝓕⁻ ψ : SchwartzMap E ℂ).integrable

end GlobalTheory
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real

namespace GlobalTheory.GallagherLemma

theorem continuous_fourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem fourier_ae_eq {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  refine ae_eq_of_integral_contDiff_smul_eq (continuous_fourier hf).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
  intro g hg hc
  have hc' : HasCompactSupport (fun x => (g x : ℂ)) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hg' := Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg' with hφ
  have hφx : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun D => D φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h3 : ∫ x, (𝓕 φ) x • f x = ∫ x, φ x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hf
  have h4 : ∫ x, (𝓕 φ) x • (h2.toLp f) x = ∫ x, (𝓕 φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [h4, h3] at h1
  simpa [hφx] using h1

theorem integral_norm_sq_Lp (F : Lp ℂ 2 (volume : Measure ℝ)) : ∫ x, ‖F x‖ ^ 2 = ‖F‖ ^ 2 := by
  have := L2.inner_def (𝕜 := ℂ) F F
  rw [inner_self_eq_norm_sq_to_K] at this
  simp only [inner_self_eq_norm_sq_to_K] at this
  have h : ((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact this.symm
  exact_mod_cast h

theorem plancherel {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖𝓕 f x‖ ^ 2) ∧ ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_ae_eq hf h2
  constructor
  · have h3 : MemLp (𝓕 f) 2 volume :=
      (memLp_congr_ae h).2 (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm h3.aestronglyMeasurable).1 h3
  · calc ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [h] with x hx
          rw [hx]
      _ = ∫ x, ‖(h2.toLp f) x‖ ^ 2 := by
          rw [integral_norm_sq_Lp, integral_norm_sq_Lp, Lp.norm_fourier_eq]
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]

theorem fourier_indicator (l δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (w : ℝ) :
    𝓕 ((Set.Ico (l - δ) l).indicator (fun _ => c)) w =
      c * cexp (-(2 * π * w * l : ℝ) * I) * ∫ u in (0 : ℝ)..δ, cexp ((2 * π * w * u : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, cexp (↑(-2 * π * v * w) * I) • (Set.Ico (l - δ) l).indicator (fun _ => c) v =
      (Set.Ico (l - δ) l).indicator (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) v := by
    intro v
    by_cases hv : v ∈ Set.Ico (l - δ) l <;> simp [hv]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := δ)
    (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) l
  rw [sub_zero] at h2
  rw [← h2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm _ c, mul_assoc c, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem kernel_lower (δ s : ℝ) (hδ : 0 ≤ δ) (hs : |s| * δ ≤ 1) :
    δ / 2 ≤ ‖∫ u in (0 : ℝ)..δ, cexp ((s * u : ℝ) * I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  have hc : Continuous fun u : ℝ => cexp ((s * u : ℝ) * I) := by fun_prop
  have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable (μ := volume) 0 δ)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  calc δ / 2 = ∫ u in (0 : ℝ)..δ, (1 / 2 : ℝ) := by simp; ring
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hδ (by simp)
        ((Complex.continuous_re.comp hc).intervalIntegrable _ _) fun u hu => ?_
      rw [exp_ofReal_mul_I_re]
      have h1 : |s * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hu.1]
        exact le_trans (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)) hs
      have h2 := Real.one_sub_sq_div_two_le_cos (x := s * u)
      have h3 : (s * u) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (s * u)]
      linarith

theorem exp_sum (S : Finset ℕ) (a : ℕ → ℂ) (l : ℕ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2) ≤
      8 * π * T ^ 2 *
        ∫ v : ℝ, ‖∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v‖ ^ 2 := by
  set f : ℝ → ℂ := fun v => ∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v
    with hf
  have hmem : ∀ (p : ENNReal) (n : ℕ),
      MemLp ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) p volume := fun p n =>
    memLp_indicator_const p measurableSet_Ico.nullMeasurableSet _ (Or.inr (by simp))
  have hint : ∀ n, Integrable ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) volume :=
    fun n => memLp_one_iff_integrable.1 (hmem 1 n)
  have hf1 : Integrable f := integrable_finsetSum _ fun n _ => hint n
  have hf2 : MemLp f 2 := memLp_finsetSum _ fun n _ => hmem 2 n
  obtain ⟨hI, hP⟩ := plancherel hf1 hf2
  have hδ : 0 ≤ 1 / T := by positivity
  have hF : ∀ w : ℝ, 𝓕 f w = (∑ n ∈ S, a n * cexp (-(2 * π * w * l n : ℝ) * I)) *
      ∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I) := by
    intro w
    rw [Finset.sum_mul]
    simp_rw [← fourier_indicator _ _ hδ]
    simp_rw [Real.fourier_real_eq, hf, Finset.smul_sum]
    refine integral_finsetSum _ fun n _ => ?_
    simpa [mul_comm] using (Real.fourierIntegral_convergent_iff w).2 (hint n)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set D : ℝ → ℝ := fun t => ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2 with hD
  have hDc : Continuous D := by fun_prop
  have h1 : ∫ t in (-T)..T, D t = (2 * π) * ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) := by
    have := intervalIntegral.mul_integral_comp_mul_left (f := D) (a := -T / (2 * π))
      (b := T / (2 * π)) (2 * π)
    rw [this, mul_div_cancel₀ _ hpi.ne', mul_div_cancel₀ _ hpi.ne']
  have hle : -T / (2 * π) ≤ T / (2 * π) := by gcongr; linarith
  have h2 : ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) ≤
      ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hle
      ((hDc.comp (by fun_prop : Continuous fun w : ℝ => 2 * π * w)).intervalIntegrable _ _)
      ((hI.const_mul _).intervalIntegrable) fun w hw => ?_
    have hw' : |2 * π * w| ≤ T := by
      rw [abs_le]
      constructor
      · have := (div_le_iff₀ hpi).1 hw.1
        linarith
      · have := (le_div_iff₀ hpi).1 hw.2
        linarith
    have hk := kernel_lower (1 / T) (2 * π * w) hδ (by rw [mul_one_div, div_le_one hT]; exact hw')
    rw [hF, norm_mul, mul_pow]
    set k := ‖∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I)‖
    have hk1 : 1 ≤ 2 * T * k := by
      have : 2 * T * (1 / T / 2) = 1 := by field_simp
      rw [← this]; gcongr
    have hk2 : 1 ≤ 4 * T ^ 2 * k ^ 2 := by nlinarith
    have hD0 : 0 ≤ D (2 * π * w) := by positivity
    change D (2 * π * w) ≤ 4 * T ^ 2 * (D (2 * π * w) * k ^ 2)
    nlinarith
  have h3 : ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 ≤
      4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, ← hP, intervalIntegral.integral_of_le hle]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hI (Filter.Eventually.of_forall fun w => by positivity))
      (by positivity)
  rw [h1]
  calc _ ≤ (2 * π) * (4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2) := by
        gcongr; exact h2.trans h3
    _ = _ := by ring

theorem gallagher : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
    (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n‖ ^ 2 / x := by
  refine ⟨8 * π, by positivity, fun N a T hT => ?_⟩
  have h := exp_sum (Finset.Icc 1 N) a (fun n => Real.log n) T (by linarith)
  convert h using 2
  · funext t
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 2
    push_cast
    ring
  · rw [← Real.range_exp, ← Set.image_univ,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [abs_of_pos (Real.exp_pos v), mul_div_cancel₀ _ (Real.exp_pos v).ne', Finset.sum_filter]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : 0 < n)
    rw [Set.indicator_apply, ← Real.exp_add]
    refine if_congr ?_ rfl rfl
    rw [Set.mem_Ico, ← Real.lt_log_iff_exp_lt hn0, ← Real.log_le_iff_le_exp hn0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end GlobalTheory.GallagherLemma
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.logDerivativeThreeFourOne

lemma comb_nonneg {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at e
    nlinarith
  have e2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq]
  rw [e2]
  nlinarith [sq_nonneg (z.re + 1)]

lemma neg_logDeriv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ))) s n).re)
      (-(deriv (LFunction χ) s / LFunction χ s).re) := by
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  simpa [neg_div] using h'

lemma term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) n) *
          (fun n : ℕ => (vonMangoldt n : ℂ))) σ n).re
      + 4 * (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + t * I) n).re
      + (LSeries.term ((fun n : ℕ => (χ ^ 2) n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hA : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) σ
  set A : ℝ := (n : ℝ) ^ σ with hAdef
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  set b : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hbdef
  have ha : (n : ℂ) ^ (σ : ℂ) = (A : ℂ) := by
    rw [hAdef, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast
  have hb : ‖b‖ = 1 := by
    rw [hbdef, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hb0 : b ≠ 0 := by
    rintro h
    simp [h] at hb
  have e1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = A * b := by
    rw [cpow_add _ _ hn', ha]
  have e2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) = A * b ^ 2 := by
    rw [cpow_add _ _ hn', ha, hbdef, ← cpow_nat_mul]
    push_cast
    ring_nf
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  rw [e1, e2, ha]
  set c : ℝ := vonMangoldt n / A with hcdef
  have hc : 0 ≤ c := div_nonneg vonMangoldt_nonneg hA.le
  by_cases hu : IsUnit (n : ZMod q)
  · have hz : ‖χ n / b‖ = 1 := by
      rw [norm_div, hb, div_one]
      simpa using χ.unit_norm_eq_one hu.unit
    have k1 : (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / (A : ℂ) = (c : ℂ) := by
      rw [MulChar.one_apply hu, one_mul, hcdef, Complex.ofReal_div]
    have k2 : χ n * (vonMangoldt n : ℂ) / ((A : ℂ) * b) = (c : ℂ) * (χ n / b) := by
      rw [hcdef, Complex.ofReal_div]
      field_simp
    have k3 : (χ ^ 2) n * (vonMangoldt n : ℂ) / ((A : ℂ) * b ^ 2) = (c : ℂ) * (χ n / b) ^ 2 := by
      rw [MulChar.pow_apply' χ two_ne_zero, hcdef, Complex.ofReal_div]
      field_simp
    rw [k1, k2, k3, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hcomb := comb_nonneg hz
    nlinarith [mul_nonneg hc hcomb]
  · simp [MulChar.map_nonunit _ hu]

theorem three_four_one : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 < σ → 0 ≤ -(3 * (deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + 4 * (deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re + (deriv (LFunction (χ ^ 2)) (σ + 2 * t * I) / LFunction (χ ^ 2) (σ + 2 * t * I)).re) := by
  intro q _ χ σ t hσ
  have h1 := neg_logDeriv_eq (1 : DirichletCharacter ℂ q) (s := (σ : ℂ)) (by simpa using hσ)
  have h2 := neg_logDeriv_eq χ (s := (σ : ℂ) + t * I) (by simpa using hσ)
  have h3 := neg_logDeriv_eq (χ ^ 2) (s := (σ : ℂ) + 2 * t * I) (by simpa using hσ)
  have h := ((h1.mul_left 3).add (h2.mul_left 4)).add h3
  have hnn := h.nonneg (fun n => term_nonneg χ σ t n)
  linarith

end GlobalTheory.logDerivativeThreeFourOne
end
