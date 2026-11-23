module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
import Aesop.Main
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Nullstellensatz
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem periodic_comp_ofComplex_of_vadd' {f : ℍ → ℂ} {M : ℝ} (hper : ∀ τ : ℍ, f (M +ᵥ τ) = f τ) :
    Function.Periodic (f ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem qParam_add_period {M : ℝ} (hM : M ≠ 0) (z : ℂ) :
    Function.Periodic.qParam M (z + M) = Function.Periodic.qParam M z := by
  unfold Function.Periodic.qParam
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [show 2 * π * Complex.I * (z + M) / M = 2 * π * Complex.I * z / M + 2 * π * Complex.I by field_simp,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem isBoundedAtImInfty_of_periodic_of_polyBound :
    ∀ (f : ℍ → ℂ) (h : ℕ) (C : ℝ) (A : ℕ), 0 < h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, f ((h : ℝ) +ᵥ τ) = f τ) →
      (∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ h → ‖f τ‖ ≤ C * τ.im ^ A) → IsBoundedAtImInfty f := by
  intro f h C A hh hf hper hbd
  set M : ℝ := (h : ℝ) with hMdef
  have hM : 0 < M := by simp [hMdef, hh]
  have hperF : Function.Periodic (f ∘ ofComplex) M := periodic_comp_ofComplex_of_vadd' hper

  have hbd' : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * τ.im ^ A := by
    intro τ hτ
    set n : ℤ := ⌊τ.re / M⌋
    have h1 : (n : ℝ) ≤ τ.re / M := Int.floor_le _
    have h2 : τ.re / M < n + 1 := Int.lt_floor_add_one _
    have hw : 0 < ((τ : ℂ) - n * M).im := by simpa using τ.im_pos
    set σ : ℍ := ⟨(τ : ℂ) - n * M, hw⟩
    have hσ : f σ = f τ := by
      have := hperF.sub_int_mul_eq (x := (τ : ℂ)) n
      simp only [Function.comp_apply, ofComplex_apply] at this
      rw [← this, ofComplex_apply_of_im_pos hw]
    have hσim : σ.im = τ.im := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).im = τ.im
      simp
    have hσre : σ.re = τ.re - n * M := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).re = τ.re - n * M
      simp
    have hre1 : n * M ≤ τ.re := by rwa [le_div_iff₀ hM] at h1
    have hre2 : τ.re < (n + 1) * M := by rwa [div_lt_iff₀ hM] at h2
    have habs : |σ.re| ≤ h := by
      rw [hσre, abs_le]
      constructor <;> nlinarith
    rw [← hσ, ← hσim]
    exact hbd σ (hσim ▸ hτ) habs

  set g : ℍ → ℂ := fun τ ↦ f τ * Function.Periodic.qParam M τ with hg
  have hnormg : ∀ τ : ℍ, ‖g τ‖ = ‖f τ‖ * Real.exp (-2 * π * τ.im / M) := by
    intro τ
    simp [hg, norm_mul, Function.Periodic.norm_qParam]
  have hgdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    hf.mul ((Function.Periodic.differentiable_qParam (h := M)).comp_mdifferentiable
      UpperHalfPlane.mdifferentiable_coe)
  have hgper : ∀ τ : ℍ, g (M +ᵥ τ) = g τ := by
    intro τ
    simp only [hg, hper, coe_vadd]
    rw [add_comm, qParam_add_period hM.ne']
  have hgzero : IsZeroAtImInfty g := by
    set c : ℝ := 2 * π / M with hc
    have hcpos : 0 < c := by positivity
    have hT : Tendsto (fun y : ℝ ↦ C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y)))) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp
        (tendsto_id.const_mul_atTop hcpos)).const_mul (C * (c⁻¹) ^ A)
    have heq : ∀ y : ℝ, C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y))) =
        C * y ^ A * Real.exp (-2 * π * y / M) := by
      intro y
      have : -(c * y) = -2 * π * y / M := by rw [hc]; ring
      rw [this, mul_pow, ← mul_assoc, ← mul_assoc, mul_assoc C, ← mul_pow, inv_mul_cancel₀ hcpos.ne',
        one_pow, mul_one]
    simp_rw [heq] at hT
    have hT' : Tendsto (fun τ : ℍ ↦ C * τ.im ^ A * Real.exp (-2 * π * τ.im / M)) atImInfty (𝓝 0) :=
      hT.comp tendsto_comap
    refine squeeze_zero_norm' ?_ hT'
    refine (atImInfty_mem _).2 ⟨1, fun τ hτ ↦ ?_⟩
    rw [Set.mem_setOf_eq, hnormg]
    exact mul_le_mul_of_nonneg_right (hbd' τ hτ) (Real.exp_pos _).le
  have hgbdd : IsBoundedAtImInfty g := hgzero.boundedAtFilter
  have hdecay := hgzero.exp_decay_atImInfty hM (periodic_comp_ofComplex_of_vadd' hgper) hgdiff hgbdd
  obtain ⟨K, hK⟩ := hdecay.bound
  obtain ⟨B, hB⟩ := (atImInfty_mem _).1 hK
  refine isBoundedAtImInfty_iff.2 ⟨K, B, fun τ hτ ↦ ?_⟩
  have h1 := hB τ hτ
  simp only [Set.mem_setOf_eq, hnormg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact le_of_mul_le_mul_right h1 (Real.exp_pos _)

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem hasSum_integral_smul_of_partition {X Γ E : Type} [MeasurableSpace X] [Countable Γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) (w : Γ → X → ℝ)
    (hw : ∀ γ, Measurable (w γ)) (hw0 : ∀ γ x, 0 ≤ w γ x)
    (hw1 : ∀ x, HasSum (fun γ => w γ x) 1) (F : X → E) (hF : Integrable F μ) :
    (∀ γ, Integrable (fun x => w γ x • F x) μ) ∧
      HasSum (fun γ => ∫ x, w γ x • F x ∂μ) (∫ x, F x ∂μ) := by
  have hle : ∀ γ x, w γ x ≤ 1 := fun γ x =>
    le_hasSum (hw1 x) γ (fun j _ => hw0 j x)
  have hnorm : ∀ γ x, ‖w γ x • F x‖ = w γ x * ‖F x‖ := fun γ x => by
    rw [norm_smul, Real.norm_of_nonneg (hw0 γ x)]
  have hmeas : ∀ γ, AEStronglyMeasurable (fun x => w γ x • F x) μ := fun γ =>
    (hw γ).aestronglyMeasurable.smul hF.aestronglyMeasurable
  refine ⟨fun γ => hF.mono (hmeas γ) (Eventually.of_forall fun x => ?_), ?_⟩
  · rw [hnorm]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle γ x)
  refine hasSum_integral_of_dominated_convergence (fun γ x => w γ x * ‖F x‖) hmeas
    (fun γ => Eventually.of_forall fun x => (hnorm γ x).le)
    (Eventually.of_forall fun x => ((hw1 x).mul_right ‖F x‖).summable) ?_ ?_
  · have : (fun x => ∑' γ, w γ x * ‖F x‖) = fun x => ‖F x‖ := by
      funext x
      rw [((hw1 x).mul_right ‖F x‖).tsum_eq, one_mul]
    rw [this]
    exact hF.norm
  · exact Eventually.of_forall fun x => by simpa using (hw1 x).smul_const (F x)

theorem integrable_tsum_of_summable_norm_integral {ι Y : Type} [Countable ι]
    [MeasurableSpace Y] (μ : Measure Y) (F : ι → Y → ℂ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ := by
  have hm : AEStronglyMeasurable (fun y => ∑' i, F i y) μ :=
    (AEMeasurable.tsum fun i => (hF i).aemeasurable).aestronglyMeasurable
  have hle : ∫⁻ y, ‖∑' i, F i y‖ₑ ∂μ ≤ ENNReal.ofReal (∑' i, ∫ y, ‖F i y‖ ∂μ) := by
    calc ∫⁻ y, ‖∑' i, F i y‖ₑ ∂μ ≤ ∫⁻ y, ∑' i, ‖F i y‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ y, ‖F i y‖ₑ ∂μ := lintegral_tsum fun i => (hF i).aemeasurable.enorm
      _ = ∑' i, ENNReal.ofReal (∫ y, ‖F i y‖ ∂μ) :=
          tsum_congr fun i => (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg
          (fun i => integral_nonneg fun y => norm_nonneg _) hs).symm
  exact ⟨hm, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩

theorem abstract_double_coset_adjoint : ∀ (G X Γ ι κ : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ] [Group Γ] [Countable Γ] [Fintype ι] [Fintype κ] (φ : Γ →* G) (ρ : X → ℝ) (β : ι → G) (α : κ → G) (e : Γ × ι ≃ κ × Γ) (P : ι → X → ℂ) (Q : κ → X → ℂ), Measurable ρ → (∀ x, 0 ≤ ρ x) → (∀ x, HasSum (fun γ : Γ => ρ (φ γ • x)) 1) → (∀ p, φ p.1 * β p.2 = α (e p).1 * φ (e p).2) → (∀ p x, P p.2 x = Q (e p).1 (φ (e p).2 • x)) → (∀ i, Integrable (fun x => (ρ x : ℂ) * P i x) μ) → (∀ j, AEStronglyMeasurable (Q j) μ) → (∀ j, Integrable (fun x => (ρ x : ℂ) * Q j ((α j)⁻¹ • x)) μ) ∧ ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ := by
  intro G X Γ ι κ _ _ _ _ μ _ _ _ _ _ φ ρ β α e P Q hρm hρ0 hρ1 he hPQ hPi _

  set wP : ι → Γ → X → ℝ := fun i γ x => ρ (φ γ • β i • x) with hwP
  set wQ : κ → Γ → X → ℝ := fun j γ y => ρ ((φ γ)⁻¹ • (α j)⁻¹ • y) with hwQ
  set FP : ι → X → ℂ := fun i x => (ρ x : ℂ) * P i x with hFP
  set FQ : κ → X → ℂ := fun j y => (ρ y : ℂ) * Q j ((α j)⁻¹ • y) with hFQ
  have hwPm : ∀ i γ, Measurable (wP i γ) := fun i γ =>
    hρm.comp ((measurable_id.const_smul (β i)).const_smul (φ γ))
  have hwQm : ∀ j γ, Measurable (wQ j γ) := fun j γ =>
    hρm.comp ((measurable_id.const_smul (α j)⁻¹).const_smul (φ γ)⁻¹)
  have hwP0 : ∀ i γ x, 0 ≤ wP i γ x := fun _ _ _ => hρ0 _
  have hwQ0 : ∀ j γ x, 0 ≤ wQ j γ x := fun _ _ _ => hρ0 _
  have hwP1 : ∀ i x, HasSum (fun γ => wP i γ x) 1 := fun i x => hρ1 (β i • x)
  have hwQ1 : ∀ j y, HasSum (fun γ => wQ j γ y) 1 := fun j y => by
    have h := (Equiv.inv Γ).hasSum_iff.2 (hρ1 ((α j)⁻¹ • y))
    simpa [Function.comp_def, map_inv] using h

  have hpt : ∀ (q : κ × Γ) (x : X),
      wQ q.1 q.2 ((α q.1 * φ q.2) • x) • FQ q.1 ((α q.1 * φ q.2) • x) =
        wP (e.symm q).2 (e.symm q).1 x • FP (e.symm q).2 x := by
    intro q x
    have h1 := he (e.symm q)
    have h2 := hPQ (e.symm q) x
    simp only [Equiv.apply_symm_apply] at h1 h2
    have hx1 : (φ q.2)⁻¹ • (α q.1)⁻¹ • (α q.1 * φ q.2) • x = x := by
      rw [smul_smul, smul_smul, ← mul_assoc, mul_assoc _ (α q.1)⁻¹, inv_mul_cancel, mul_one,
        inv_mul_cancel, one_smul]
    have hx2 : (α q.1)⁻¹ • (α q.1 * φ q.2) • x = φ q.2 • x := by
      rw [smul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hx3 : (α q.1 * φ q.2) • x = φ (e.symm q).1 • β (e.symm q).2 • x := by
      rw [← h1, mul_smul]
    simp only [hwQ, hwP, hFQ, hFP, hx1, hx2, h2, inv_smul_smul]
    rw [hx3, Complex.real_smul, Complex.real_smul]
    ring

  have hPpart := fun i => hasSum_integral_smul_of_partition μ (wP i) (hwPm i) (hwP0 i) (hwP1 i)
    (FP i) (hPi i)
  have hPnorm := fun i => hasSum_integral_smul_of_partition μ (wP i) (hwPm i) (hwP0 i) (hwP1 i)
    (fun x => ‖FP i x‖) (hPi i).norm
  have hnP : ∀ i γ x, ‖wP i γ x • FP i x‖ = wP i γ x • ‖FP i x‖ := fun i γ x => by
    rw [norm_smul, Real.norm_of_nonneg (hwP0 i γ x), smul_eq_mul]
  let a : Γ × ι → ℝ := fun p => ∫ x, ‖wP p.2 p.1 x • FP p.2 x‖ ∂μ
  let t : Γ × ι → ℂ := fun p => ∫ x, wP p.2 p.1 x • FP p.2 x ∂μ
  have ha0 : 0 ≤ a := fun p => integral_nonneg fun x => norm_nonneg _
  have haP : ∀ i, HasSum (fun γ => a (γ, i)) (∫ x, ‖FP i x‖ ∂μ) := fun i => by
    simpa only [a, hnP] using (hPnorm i).2
  have hsa : Summable a := by
    rw [summable_prod_of_nonneg ha0]
    refine ⟨fun γ => Summable.of_finite, ?_⟩
    simp only [tsum_fintype]
    exact summable_sum fun i _ => (haP i).summable
  have hst : Summable t :=
    Summable.of_norm_bounded hsa fun p => norm_integral_le_integral_norm _

  have hcv : ∀ q : κ × Γ, (fun x => wQ q.1 q.2 ((α q.1 * φ q.2) • x) •
      FQ q.1 ((α q.1 * φ q.2) • x)) = fun x => wP (e.symm q).2 (e.symm q).1 x • FP (e.symm q).2 x :=
    fun q => funext (hpt q)
  have hta : ∀ q : κ × Γ, t (e.symm q) = ∫ y, wQ q.1 q.2 y • FQ q.1 y ∂μ := fun q => by
    rw [← integral_smul_eq_self (fun y => wQ q.1 q.2 y • FQ q.1 y) (g := α q.1 * φ q.2)]
    exact congrArg (fun f => ∫ x, f x ∂μ) (hcv q).symm
  have haa : ∀ q : κ × Γ, a (e.symm q) = ∫ y, ‖wQ q.1 q.2 y • FQ q.1 y‖ ∂μ := fun q => by
    rw [← integral_smul_eq_self (fun y => ‖wQ q.1 q.2 y • FQ q.1 y‖) (g := α q.1 * φ q.2)]
    exact congrArg (fun f => ∫ x, ‖f x‖ ∂μ) (hcv q).symm
  have hintQ : ∀ q : κ × Γ, Integrable (fun y => wQ q.1 q.2 y • FQ q.1 y) μ := fun q => by
    have hemb := (MeasurableEquiv.smul (α q.1 * φ q.2) : X ≃ᵐ X).measurableEmbedding
    rw [← (measurePreserving_smul (α q.1 * φ q.2) μ).integrable_comp_emb hemb]
    have := (hPpart (e.symm q).2).1 (e.symm q).1
    rw [← hcv q] at this
    exact this
  have hsb : Summable fun q => a (e.symm q) := e.symm.summable_iff.2 hsa
  obtain ⟨hfib, -⟩ := (summable_prod_of_nonneg fun q => ha0 (e.symm q)).1 hsb
  have hsQ : ∀ j, Summable fun γ => ∫ y, ‖wQ j γ y • FQ j y‖ ∂μ := fun j => by
    simpa only [haa] using hfib j
  have hFQsum : ∀ j, (fun y => ∑' γ, wQ j γ y • FQ j y) = FQ j := fun j => by
    funext y
    simpa using ((hwQ1 j y).smul_const (FQ j y)).tsum_eq
  have hQint : ∀ j, Integrable (FQ j) μ := fun j => by
    have h := integrable_tsum_of_summable_norm_integral μ (fun γ y => wQ j γ y • FQ j y)
      (fun γ => hintQ (j, γ)) (hsQ j)
    rwa [hFQsum j] at h
  refine ⟨hQint, ?_⟩
  have hQpart := fun j => hasSum_integral_smul_of_partition μ (wQ j) (hwQm j) (hwQ0 j)
    (hwQ1 j) (FQ j) (hQint j)
  have hstb : Summable fun q => t (e.symm q) := e.symm.summable_iff.2 hst
  calc ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ i, ∑' γ, t (γ, i) :=
        Finset.sum_congr rfl fun i _ => ((hPpart i).2.tsum_eq).symm
    _ = ∑' γ, ∑ i, t (γ, i) := (Summable.tsum_finsetSum fun i _ => (hPpart i).2.summable).symm
    _ = ∑' γ, ∑' i, t (γ, i) := by simp only [tsum_fintype]
    _ = ∑' p, t p := hst.tsum_prod.symm
    _ = ∑' q, t (e.symm q) := (e.symm.tsum_eq t).symm
    _ = ∑' j, ∑' γ, t (e.symm (j, γ)) := hstb.tsum_prod
    _ = ∑ j, ∑' γ, ∫ y, wQ j γ y • FQ j y ∂μ := by
        rw [tsum_fintype]; simp only [hta]
    _ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ :=
        Finset.sum_congr rfl fun j _ => (hQpart j).2.tsum_eq

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem fd_half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

theorem fd_volume_lt_top : volume ModularGroup.fd < ⊤ := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  set S : Set ℂ := Complex.re ⁻¹' Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ Complex.im ⁻¹' Set.Ici (1 / 2 : ℝ)
    with hS
  have hsub : ((↑) '' ModularGroup.fd : Set ℂ) ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨abs_le.1 hz.2, fd_half_le_im hz⟩
  have hSm : MeasurableSet S :=
    (Complex.measurable_re measurableSet_Icc).inter (Complex.measurable_im measurableSet_Ici)
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [← lintegral_indicator hSm]
  set g : ℂ → ENNReal := fun z => ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) with hg
  have e := (Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (S.indicator g)
  rw [← e]
  have hle : ∀ p : ℝ × ℝ, S.indicator g (Complex.measurableEquivRealProd.symm p) ≤
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ENNReal)) p.1 *
      (Set.Ici (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2 := by
    rintro ⟨x, y⟩
    have hsy : Complex.measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := rfl
    rw [hsy]
    by_cases hm : (⟨x, y⟩ : ℂ) ∈ S
    · obtain ⟨hx, hy⟩ := id hm
      have hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx
      have hy' : y ∈ Set.Ici (1 / 2 : ℝ) := hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hx', Set.indicator_of_mem hy', one_mul]
      apply le_of_eq
      simp only [hg]
      rw [ENNReal.ofReal]
      congr 1
      ext
      simp [sq_abs]
      positivity
    · rw [Set.indicator_of_notMem hm]
      exact bot_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [Measure.volume_eq_prod, lintegral_prod_mul (aemeasurable_const.indicator measurableSet_Icc)
    ((by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (1 / y ^ 2)).aemeasurable.indicator
      measurableSet_Ici)]
  rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ici,
    setLIntegral_const, one_mul, Real.volume_Icc]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Set.Ici (1 / 2 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

theorem fd_measurableSet : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

theorem pow_mul_exp_neg_le (δ : ℝ) (A : ℕ) (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ A * Real.exp (-δ * y) ≤ (A.factorial : ℝ) / δ ^ A := by
  have h := Real.pow_div_factorial_le_exp (δ * y) (mul_nonneg hδ.le hy) A
  have hf : (0 : ℝ) < A.factorial := by exact_mod_cast A.factorial_pos
  have hδA : 0 < δ ^ A := pow_pos hδ A
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ hδA, neg_mul, Real.exp_neg]
  have he := Real.exp_pos (δ * y)
  calc y ^ A * (Real.exp (δ * y))⁻¹ * δ ^ A = δ ^ A * y ^ A * (Real.exp (δ * y))⁻¹ := by ring
    _ ≤ Real.exp (δ * y) * A.factorial * (Real.exp (δ * y))⁻¹ := by gcongr
    _ = A.factorial := by field_simp

theorem integrableOn_fd_im_pow_mul_exp :
    ∀ (δ : ℝ) (A : ℕ), 0 < δ →
      IntegrableOn (fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)) ModularGroup.fd := by
  intro δ A hδ
  refine Measure.integrableOn_of_bounded (M := (A.factorial : ℝ) / δ ^ A) fd_volume_lt_top.ne
    (by fun_prop : Continuous fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)).aestronglyMeasurable
    ((ae_restrict_iff' fd_measurableSet).2 (Filter.Eventually.of_forall fun τ _ => ?_))
  have hy := τ.im_pos.le
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_mul_exp_neg_le δ A hδ hy

end GlobalTheory.EisM
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem exists_ne_zero_common_zero_of_constantCoeff_eq_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, MvPolynomial.constantCoeff (f i) = 0) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  classical
  set m : Ideal (MvPolynomial (Fin n) k) := RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) with hm
  have hsurj : Function.Surjective (MvPolynomial.eval (0 : Fin n → k)) :=
    fun c => ⟨MvPolynomial.C c, by simp⟩
  haveI hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((Finset.univ.image f : Finset _) : Set (MvPolynomial (Fin n) k)) with hI
  have hIm : I ≤ m := by
    rw [hI, Ideal.span_le]
    intro g hg
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hg
    obtain ⟨i, rfl⟩ := hg
    simp [hm, RingHom.mem_ker, MvPolynomial.eval_zero, hf i]
  have hItop : I ≠ ⊤ := fun h => hmax.ne_top (top_le_iff.mp (h ▸ hIm))
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hItop
  haveI hPp : P.IsPrime := hP.1.1
  have hht : P.height ≤ r := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
    refine h1.trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hmh : m.height = n := (ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n m).2
  have hPne : P ≠ m := by
    intro h
    rw [h, hmh] at hht
    exact absurd (by exact_mod_cast hht : n ≤ r) (not_le.mpr hrn)
  by_contra hcon
  push_neg at hcon
  apply hPne
  have hsub : MvPolynomial.zeroLocus k P ⊆ {0} := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (hP.1.2 (Ideal.subset_span (by simp)))
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  have hle : m ≤ P := by
    intro p hp
    have h2 : p ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) := by
      intro x hx
      rw [Set.mem_singleton_iff.mp (hsub hx)]
      exact hp
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hPp.radical] at h2
  exact (hmax.eq_of_le hPp.ne_top hle).symm

end GlobalTheory
end
