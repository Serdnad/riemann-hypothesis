module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SmoothCut

theorem exists_smooth_antitone_cut :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧
      (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  have hanti : Antitone (fun x : ℝ => Real.smoothTransition (1 - x)) := fun a b hab =>
    Real.smoothTransition.monotone (by linarith)
  refine ⟨fun x => Real.smoothTransition (1 - x),
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id), ?_,
    fun x => Real.smoothTransition.nonneg _,
    fun x hx => Real.smoothTransition.one_of_one_le (by linarith),
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  intro x
  have hneg : Monotone (fun x : ℝ => -Real.smoothTransition (1 - x)) := fun a b hab =>
    neg_le_neg (hanti hab)
  have h := hneg.deriv_nonneg (x := x)
  rw [deriv.fun_neg] at h
  linarith

end GlobalTheory.CompanionTheory.SmoothCut
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.GronwallZero

theorem eq_zero_of_deriv_le_mul :
    ∀ (e e' : ℝ → ℝ) (K t : ℝ), 0 ≤ t → (∀ s, HasDerivAt e (e' s) s) →
      (∀ s, e' s ≤ K * e s) → (∀ s, 0 ≤ e s) → e 0 = 0 → e t = 0 := by
  intro e e' K t ht hd hle hnn h0
  have hg : ∀ s, HasDerivAt (fun s => e s * Real.exp (-K * s))
      ((e' s - K * e s) * Real.exp (-K * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s := by
      have h2 : HasDerivAt (fun s : ℝ => -K * s) (-K) s := by
        simpa using (hasDerivAt_id s).const_mul (-K)
      exact h2.exp
    have h5 : HasDerivAt (fun s => e s * Real.exp (-K * s))
        (e' s * Real.exp (-K * s) + e s * (Real.exp (-K * s) * (-K))) s := (hd s).mul h1
    exact h5.congr_deriv (by ring)
  have hanti : Antitone (fun s => e s * Real.exp (-K * s)) := by
    apply antitone_of_deriv_nonpos
    · exact fun s => (hg s).differentiableAt
    · intro s
      rw [(hg s).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle s]) (Real.exp_pos _).le
  have h3 : e t * Real.exp (-K * t) ≤ e 0 * Real.exp (-K * 0) := hanti ht
  rw [h0, zero_mul] at h3
  have h4 : e t ≤ 0 := by
    by_contra hc
    exact absurd h3 (not_le.mpr (mul_pos (not_le.mp hc) (Real.exp_pos _)))
  exact le_antisymm h4 (hnn t)

end GlobalTheory.CompanionTheory.WaveSpd.GronwallZero
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.OneParam

theorem hasDerivAt_zero_of_continuous_oneParam
    {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸)
    (hc : Continuous Φ) (h0 : Φ 0 = 1) (hadd : ∀ s t, Φ (s + t) = Φ s * Φ t) :
    ∃ B, HasDerivAt Φ B 0 := by

  set F : ℝ → 𝔸 := fun x => ∫ s in (0 : ℝ)..x, Φ s with hF
  have hFd : ∀ x, HasDerivAt F (Φ x) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hF0 : F 0 = 0 := by simp [hF]

  have hsl : Filter.Tendsto (slope F 0) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 : 𝔸)) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hFd 0)
    rwa [h0] at this
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, ‖slope F 0 ε - 1‖ < 1 := by
    have := hsl.eventually (Metric.ball_mem_nhds (1 : 𝔸) one_pos)
    filter_upwards [this] with ε hε
    simpa [dist_eq_norm] using hε
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : ε ≠ 0 := hε0

  set u : 𝔸 := slope F 0 ε with hu
  have huF : u = ε⁻¹ • F ε := by
    simp [hu, slope_def_module, hF0]
  have hone : ‖1 - u‖ < 1 := by rwa [norm_sub_rev]
  have huU : IsUnit u := by
    have := (Units.oneSub (1 - u) hone).isUnit
    simpa using this
  obtain ⟨U, hU⟩ := huU
  set v : 𝔸 := ((U⁻¹ : 𝔸ˣ) : 𝔸) with hv
  have huv : u * v = 1 := by rw [← hU, hv]; exact U.mul_inv

  have hmul : ∀ t, Φ t * F ε = F (t + ε) - F t := by
    intro t
    have h1 : Φ t * F ε = ∫ s in (0 : ℝ)..ε, Φ (t + s) := by
      have := (ContinuousLinearMap.mul ℝ 𝔸 (Φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable (μ := volume) 0 ε)
      simp only [ContinuousLinearMap.mul_apply'] at this
      rw [hF]
      simp only [hadd]
      exact this.symm
    have h2 : (∫ s in (0 : ℝ)..ε, Φ (t + s)) = ∫ s in (t + 0)..(t + ε), Φ s :=
      intervalIntegral.integral_comp_add_left (a := 0) (b := ε) Φ t
    rw [h1, h2, add_zero]
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 _) (hc.intervalIntegrable 0 _)).symm

  have hrec : ∀ t, Φ t = (ε⁻¹ • (F (t + ε) - F t)) * v := by
    intro t
    rw [← hmul, ← mul_smul_comm, ← huF, mul_assoc, huv, mul_one]

  have hshift : HasDerivAt (fun t => F (t + ε)) (Φ (0 + ε)) 0 :=
    (hFd (0 + ε)).comp_add_const 0 ε
  have hd : HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v)
      ((ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v) 0 :=
    ((hshift.sub (hFd 0)).const_smul ε⁻¹).mul_const v
  have hfun : Φ = fun t => (ε⁻¹ • (F (t + ε) - F t)) * v := funext hrec
  exact ⟨(ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v, by rw [show HasDerivAt Φ = HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v) from congrArg _ hfun]; exact hd⟩

end GlobalTheory.CompanionTheory.OneParam
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem pointwise_energy_ineq : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  intro W ι _ _ _ w v Y L A C₁ C c φ hC₁ hC hc hφ hL
  have hS0 : 0 ≤ ∑ p, ‖Y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ p, ‖Y p‖ ^ 2 := ⟨_, rfl⟩
  rw [← hS] at hS0 ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ‖w‖ ^ 2 + (1 / 4) * S + ‖v‖ ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hwD : ‖w‖ ^ 2 ≤ D := by rw [hD]; linarith
  have hSD : (1 / 4) * S ≤ D := by rw [hD]; linarith

  have hterm : ∀ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
    intro p
    have hin : |⟪Y p, w⟫_ℝ| ≤ ‖Y p‖ * ‖w‖ := abs_real_inner_le_norm _ _
    have hmul : |L p * ⟪Y p, w⟫_ℝ| ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
      rw [abs_mul]
      have h2 : ‖Y p‖ * ‖w‖ ≤ (1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Y p‖ - ‖w‖)]
      exact mul_le_mul (hL p) (hin.trans h2) (abs_nonneg _) hC₁
    have hle : L p * ⟪Y p, w⟫_ℝ ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      (le_abs_self _).trans hmul
    have := mul_le_mul_of_nonneg_left hle (neg_nonneg.2 hc)
    calc -(c * L p * ⟪Y p, w⟫_ℝ) = (-c) * (L p * ⟪Y p, w⟫_ℝ) := by ring
      _ ≤ (-c) * (C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))) := this
      _ = (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by ring
  have hsum : -(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      ≤ (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2) := by
    have h1 : ∑ p, -(c * L p * ⟪Y p, w⟫_ℝ)
        ≤ ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      Finset.sum_le_sum fun p _ => hterm p
    have h2 : ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))
        = (-c) * C₁ * ((1 / 2) * (S + (Fintype.card ι : ℝ) * ‖w‖ ^ 2)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← hS]
      simp [Finset.card_univ]
    rw [Finset.sum_neg_distrib, h2] at h1
    linarith
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hbr : (1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2
      ≤ (1 + (Fintype.card ι : ℝ)) * D := by
    nlinarith [mul_le_mul_of_nonneg_left hwD hN0, mul_nonneg hN0 hw2]
  have hcC : (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
      ≤ (-c) * C * D := by
    have hnc : 0 ≤ -c := neg_nonneg.2 hc
    calc (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
        ≤ (-c) * C₁ * ((1 + (Fintype.card ι : ℝ)) * D) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hnc hC₁)
      _ = (-c) * (C₁ * (1 + (Fintype.card ι : ℝ))) * D := by ring
      _ ≤ (-c) * C * D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hnc) hD0

  have hAv : ⟪A v, w⟫_ℝ ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))
  have hwv : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
  have hvw : 2 * (‖v‖ * ‖w‖) ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v‖ - ‖w‖)]
  have hvwD : 2 * (‖v‖ * ‖w‖) ≤ D := by rw [hD] at *; linarith
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hbrack : 2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ ≤ (‖A‖ + 1) * D := by
    have h3 : ‖A‖ * (2 * (‖v‖ * ‖w‖)) ≤ ‖A‖ * D := mul_le_mul_of_nonneg_left hvwD hA0
    nlinarith
  have hφ' := mul_le_mul_of_nonneg_left hbrack hφ
  have hrew : (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      = -(-(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ) := by ring
  rw [hrew]
  nlinarith

end GlobalTheory.CompanionTheory.WaveSpd
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Flag

theorem exists_frame_extension {n D : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (h1 : Cᴴ * C = 1)
    (U : Submodule ℂ (Fin n → ℂ)) (hU : ∀ v, C *ᵥ v ∈ U) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ Cᴴ * B = 0 ∧
      ∀ y, y ∈ U ↔ ∃ u w, y = C *ᵥ u + B *ᵥ w := by
  classical
  let W' : Submodule ℂ (Fin n → ℂ) := U ⊓ LinearMap.ker (Matrix.mulVecLin Cᴴ)
  obtain ⟨r, B, hB1, hBW⟩ := GlobalTheory.IsoTorus.exists_frame W'
  have hmemW' : ∀ y, y ∈ W' ↔ y ∈ U ∧ Cᴴ *ᵥ y = 0 := fun y => by
    simp [W', Submodule.mem_inf]
  have hBin : ∀ w, B *ᵥ w ∈ W' := fun w => (hBW _).mpr (by
    rw [Matrix.mulVec_mulVec w (B * Bᴴ) B, Matrix.mul_assoc, hB1, Matrix.mul_one])
  have hCB : Cᴴ * B = 0 := by
    ext i j
    have h := congrFun ((hmemW' _).mp (hBin (Pi.single j 1))).2 i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa using h
  refine ⟨r, B, hB1, hCB, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨z, hzdef⟩ : ∃ z, z = y - C *ᵥ (Cᴴ *ᵥ y) := ⟨_, rfl⟩
    have hCC : Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ y)) = Cᴴ *ᵥ y := by
      rw [Matrix.mulVec_mulVec (Cᴴ *ᵥ y) Cᴴ C, h1, Matrix.one_mulVec]
    have hz : z ∈ W' := (hmemW' z).mpr ⟨hzdef ▸ U.sub_mem hy (hU _), by
      rw [hzdef, Matrix.mulVec_sub, hCC, sub_self]⟩
    have hz' := (hBW z).mp hz
    refine ⟨Cᴴ *ᵥ y, Bᴴ *ᵥ z, ?_⟩
    rw [Matrix.mulVec_mulVec z B Bᴴ, hz', hzdef]
    abel
  · rintro ⟨u, w, rfl⟩
    exact U.add_mem (hU u) ((hmemW' _).mp (hBin w)).1

private theorem append_cols_mulVec_eq_add {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (v : Fin (D + r) → ℂ) :
    (Matrix.of fun i => Fin.append (C i) (B i)) *ᵥ v =
      C *ᵥ (fun j => v (Fin.castAdd r j)) + B *ᵥ (fun j => v (Fin.natAdd D j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

private theorem append_cols_conjTranspose_mul_eq_one {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (h1 : Cᴴ * C = 1) (h2 : Bᴴ * B = 1) (h3 : Cᴴ * B = 0) :
    (Matrix.of fun i => Fin.append (C i) (B i))ᴴ * (Matrix.of fun i => Fin.append (C i) (B i)) = 1 := by
  have h4 : Bᴴ * C = 0 := by simpa using congrArg Matrix.conjTranspose h3
  ext c c'
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;> refine Fin.addCases (fun j' => ?_) (fun j' => ?_) c'
  · have h := congrFun (congrFun h1 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · have hne : Fin.castAdd r j ≠ Fin.natAdd D j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h3 j) j'
    simpa [Matrix.mul_apply] using h
  · have hne : Fin.natAdd D j ≠ Fin.castAdd r j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h4 j) j'
    simpa [Matrix.mul_apply] using h
  · have h := congrFun (congrFun h2 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem exists_flag_frame : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧
      Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  intro n a
  induction a with
  | zero =>
    intro W hW0 _
    refine ⟨0, 0, fun _ => 0, ?_, fun x _ _ => x.elim0, fun c => c.elim0, fun i y => ?_⟩
    · ext i j
      exact i.elim0
    · have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      rw [hW0, Submodule.mem_bot]
      constructor
      · rintro rfl
        exact ⟨0, by simp, fun c => c.elim0⟩
      · rintro ⟨v, rfl, -⟩
        simp
  | succ a ih =>
    intro W hW0 hWm
    obtain ⟨D, C, τ, hC1, hτm, hτa, hCW⟩ := ih (fun i => W i.castSucc) (by simpa using hW0)
      (fun i j hij => hWm (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hU : ∀ v, C *ᵥ v ∈ W (Fin.last (a + 1)) := fun v =>
      hWm (Fin.castSucc_lt_last (Fin.last a)).le
        ((hCW (Fin.last a) _).mpr ⟨v, rfl, fun c h => absurd h (not_le.mpr (hτa c))⟩)
    obtain ⟨r, B, hB1, hCB, hBU⟩ := exists_frame_extension C hC1 (W (Fin.last (a + 1))) hU
    refine ⟨D + r, Matrix.of fun i => Fin.append (C i) (B i), Fin.append τ (fun _ => a),
      append_cols_conjTranspose_mul_eq_one C B hC1 hB1 hCB, ?_, ?_, ?_⟩
    · intro c c' hcc'
      induction c using Fin.addCases with
      | left j =>
        induction c' using Fin.addCases with
        | left j' =>
          simp only [Fin.append_left]
          exact hτm (Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hcc'))
        | right j' =>
          simp only [Fin.append_left, Fin.append_right]
          exact (hτa j).le
      | right j =>
        induction c' using Fin.addCases with
        | left j' =>
          exfalso
          have h := Fin.le_iff_val_le_val.mp hcc'
          have := j'.isLt
          simp at h
          omega
        | right j' =>
          simp only [Fin.append_right]
          exact le_refl _
    · intro c
      refine Fin.addCases (fun j => ?_) (fun j => ?_) c
      · simp only [Fin.append_left]
        exact (hτa j).trans (Nat.lt_succ_self a)
      · simp only [Fin.append_right]
        exact Nat.lt_succ_self a
    · intro i y
      induction i using Fin.lastCases with
      | last =>
        rw [hBU]
        constructor
        · rintro ⟨u, w, rfl⟩
          refine ⟨Fin.append u w, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp
          · exfalso
            revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro h
              simp only [Fin.append_left, Fin.val_last] at h
              have := hτa j
              omega
            · intro h
              simp only [Fin.append_right, Fin.val_last] at h
              omega
        · rintro ⟨v, rfl, -⟩
          exact ⟨_, _, append_cols_mulVec_eq_add C B v⟩
      | cast i' =>
        refine (hCW i' y).trans ?_
        constructor
        · rintro ⟨v, rfl, hv⟩
          refine ⟨Fin.append v 0, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
            rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, Matrix.mulVec_zero, add_zero]
          · revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro hc
              simp only [Fin.append_left, Fin.val_castSucc] at hc ⊢
              exact hv j hc
            · intro _
              simp
        · rintro ⟨v, rfl, hv⟩
          refine ⟨fun j => v (Fin.castAdd r j), ?_, fun c hc => hv (Fin.castAdd r c) (by simpa using hc)⟩
          rw [append_cols_mulVec_eq_add]
          have hz : (fun j => v (Fin.natAdd D j)) = 0 := funext fun j => hv _ (by
            have := i'.isLt
            simp only [Fin.append_right, Fin.val_castSucc]
            omega)
          rw [hz, Matrix.mulVec_zero, add_zero]

end GlobalTheory.CompanionTheory.Flag
end
