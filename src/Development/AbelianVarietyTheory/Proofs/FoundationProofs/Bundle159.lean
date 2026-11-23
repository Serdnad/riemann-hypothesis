module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogCoordsUnitValueTwoVariableIntegralExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle098

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem summable_norm_mul_pow_of_polyB {a : ℕ → ℂ} (ha : PolyB a) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖a n * q ^ n‖ := by
  obtain ⟨C, A, hC⟩ := ha
  rcases eq_or_ne q 0 with rfl | hq0
  · exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
  · have hr0 : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hr : ‖‖q‖‖ < 1 := by rwa [norm_norm]
    have h := (summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * ‖q‖ ^ m)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (h.mul_left (C * ‖q‖⁻¹))
    rw [norm_mul, norm_pow]
    have hq' : ‖q‖ ≠ 0 := hr0.ne'
    have e : C * ‖q‖⁻¹ * (((n + 1 : ℕ) : ℝ) ^ A * ‖q‖ ^ (n + 1)) = C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n := by
      push_cast
      rw [pow_succ]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)

theorem qs_term_eq (a : ℕ → ℂ) (τ : ℍ) (n : ℕ) :
    a n * cexp (2 * π * Complex.I * n * τ) = a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n := by
  simp only [smul_eq_mul, Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hasSum_qs {a : ℕ → ℂ} (ha : PolyB a) (τ : ℍ) :
    HasSum (fun n : ℕ => a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n) (qs a τ) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hs : Summable fun n => a n • Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
    simpa only [smul_eq_mul] using (summable_norm_mul_pow_of_polyB ha hq).of_norm
  convert hs.hasSum using 1
  show ∑' n, a n * cexp (2 * π * Complex.I * n * τ) = _
  exact tsum_congr fun n => qs_term_eq a τ n

private theorem mdifferentiable_qs_of_polyB {a : ℕ → ℂ} (ha : PolyB a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0def
  have hy0 : 0 < y0 := by positivity
  set U : Set ℂ := {w | y0 < w.im} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    show y0 < z.im
    linarith
  set r : ℝ := Real.exp (-(2 * π * y0)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hrdef, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_norm_mul_pow_of_polyB ha hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU ?_
    intro n w hw
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, hrdef, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.exp_le_exp]
    have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hw' : y0 < w.im := hw
    have := mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_pos.2 hw').le
    nlinarith
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

private theorem periodic_qs_comp_ofComplex_one (a : ℕ → ℂ) :
    Function.Periodic (qs a ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    show ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (w + 1))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)
    refine tsum_congr fun n => ?_
    congr 1
    rw [show 2 * π * Complex.I * n * (w + 1) = 2 * π * Complex.I * n * w + n * (2 * π * Complex.I) by ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · push_neg at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_qs {a : ℕ → ℂ} (ha : PolyB a) :
    AnalyticAt ℂ (cuspFunction 1 (qs a)) 0 := by
  exact analyticAt_cuspFunction_zero one_pos (periodic_qs_comp_ofComplex_one a)
    (mdifferentiable_qs_of_polyB ha) (isBoundedAtImInfty_of_hasSum_qExpansion one_pos (hasSum_qs ha))

theorem coef_qs : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  intro a ha n
  have hb := analyticAt_cuspFunction_qs ha
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hb (hasSum_qs ha)).hasFPowerSeriesAt
  have h2 := hb.hasFPowerSeriesAt
  have e := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at e
  show (qExpansion 1 (qs a)).coeff n = a n
  rw [qExpansion_coeff, e, div_eq_inv_mul]

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qs_coef_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (f : F) : qs (coef f) = ⇑f := by
  funext τ
  have h := ModularForm.hasSum_qExpansion f one_pos (by simp) τ
  rw [qs, ← h.tsum_eq]
  congr 1
  funext n
  rw [coef, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem polyB_of_isBigO {a : ℕ → ℂ} {k : ℕ}
    (h : (fun n => a n) =O[atTop] fun n : ℕ => (n : ℝ) ^ k) : PolyB a := by
  obtain ⟨c, hc⟩ := h.bound
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  have hS : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨|c| + ∑ n ∈ Finset.range N, ‖a n‖, k, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith)
  by_cases hn : N ≤ n
  · have h2 := hN n hn
    rw [Real.norm_of_nonneg (by positivity)] at h2
    calc ‖a n‖ ≤ c * (n : ℝ) ^ k := h2
      _ ≤ |c| * ((n : ℝ) + 1) ^ k :=
          mul_le_mul (le_abs_self c) (pow_le_pow_left₀ hn0 (by linarith) k) (by positivity) (abs_nonneg c)
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h2 : ‖a n‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ :=
      Finset.single_le_sum (f := fun n => ‖a n‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    calc ‖a n‖ ≤ |c| + ∑ n ∈ Finset.range N, ‖a n‖ := by linarith [abs_nonneg c]
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          le_mul_of_one_le_right (by positivity) h1

theorem inv_of_hasChar {k M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (hf : HasChar k χ f) :
    Inv k M (ch χ) f := by
  intro γ hγ τ
  have hmem : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hγ
  have h := congrFun (hf γ hmem) τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul] at h
  have hd : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hne : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  rw [← hd, ch]
  rw [zpow_neg, zpow_natCast] at h
  have hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0 := pow_ne_zero _ hne
  field_simp at h
  rw [h]
  ring

theorem mf_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (χ : DirichletCharacter ℂ M) (f : F) (hf : HasChar k χ f) :
    qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f) := by
  have hq := qs_coef_of_mfc (k := k) f
  refine ⟨hq, ?_, ?_⟩
  · have h := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) f
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at h
    exact polyB_of_isBigO h
  · rw [hq]; exact inv_of_hasChar χ f hf

theorem gamma1_char_elementary : ∀ (k M : ℕ) (χ : DirichletCharacter ℂ M), 0 < M →
    (∀ f : ModularForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f)) ∧
    ∀ f : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ CF k M (ch χ) (coef f) := by
  intro k M χ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨fun f hf => mf_of_mfc χ f hf, fun f hf => ?_⟩
  obtain ⟨hq, hmf⟩ := mf_of_mfc χ f hf
  refine ⟨hq, hmf, ?_⟩
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  rw [hq]
  simp only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
    zpow_natCast, norm_pow, Real.norm_of_nonneg τ.im_pos.le] at h
  calc ‖f τ‖ ^ 2 * τ.im ^ k = ‖f τ‖ * ‖f τ‖ * τ.im ^ k := by ring
    _ ≤ C := h

end GlobalTheory.EisM
end
end

section

open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LambdaValuationPowers

theorem pieceT_unitSet_muModel_smoothedSb : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (GlobalTheory.LambdaValuationPowers.coPtSb N p m k ψ c d a b) r := by
  intro p _ N m k K _ _ ψ c d a b t ζ hp2 hζ hN hpN hm hk hψ hc hd ht
  have hS : ∀ r : ℕ, pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m) r = _ := fun r =>
    GlobalTheory.TameSmoothing.pieceT_unitSet_eq_four_pieceTRaw p N m m k K ψ c d (a * t, 0) (b * t, 0) ζ hζ hN hpN hm le_rfl hk hc hd r
  have e1 : ((c * (a * t), c * 0) : ℤ × ℤ) = (c * a * t, 0) := by ext <;> simp [mul_assoc]
  have e2 : ((d * (b * t), d * 0) : ℤ × ℤ) = (d * b * t, 0) := by ext <;> simp [mul_assoc]
  simp only [e1, e2] at hS
  obtain ⟨I1, T1⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ a b t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I2, T2⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ (c * a) b t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I3, T3⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ a (d * b) t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I4, T4⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ (c * a) (d * b) t ζ hp2 hζ hN hpN hm hk hψ ht
  refine ⟨fun n hn => ?_, fun r => ?_⟩
  · rw [hS n, I1 n hn, I2 n hn, I3 n hn, I4 n hn]; ring
  · simp only [toQ, up] at T1 T2 T3 T4 ⊢
    rw [hS, T1, T2, T3, T4]
    simp only [coPtSb]
    ring

end GlobalTheory.LambdaValuationPowers
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.logCoords_unit_value_twoVariableIntegralExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (L : ℕ) (ψ : O0 p →+* Ωl) (ι : On p L →ₐ[O0 p] Ωl), 1 ≤ L → IsReb T L ψ → IsEmb T L ι →
  ∀ (A₁ g : ℤ) (θ : ℤ → ℤ → ℤ) (cU cE : ℤ → Ωl) (x x' : Ωl),
  (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) →
  (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) →
  (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) →
  (∀ r : ℤ, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k)) →
  (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i)) →
  (∀ r : ℤ, r < 0 → cE r = 0) → (∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L}) →
  Ev ψ cU x x' → x ≠ 0 → IsInt (p := p) x⁻¹ →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = x ∧ Ev ψ cE z z' ∧
    Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
    Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro p hp Ω _ _ hc T L ψ ι hL hψ hι A₁ g θ cU cE x x' hB ⟨r0, h0⟩ hdiv hU hE hE0 hEm hx hx0 hxi
  have cong_sum : ∀ {L : ℕ} (S : Finset ℤ) (v : ℤ → ℤ) (e : ℤ → Ω) (he : ∀ k, IsInt (p := p) (e k)) (hv : ∀ k, (p : ℤ) ^ L ∣ v k),
      Cong (p := p) L (∑ k ∈ S, (v k : Ω) * e k) 0 := by
    intro L S v e he hv
    choose c hc using hv
    refine ⟨∑ k ∈ S, (c k : Ω) * e k, IsIntegral.sum _ fun k _ => IsIntegral.mul (Basic.isInt_intCast _) (he k), ?_⟩
    rw [sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc k]
    push_cast
    ring

  have cong_val : ∀ (hc : IsClo p Ω) {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (g A : ℤ)
      (θ v : ℤ → ℤ → ℤ) (S : ℤ → Finset ℤ) (cU cE : ℤ → Ω) (x x' z z' y y' : Ω)
      (hv : ∀ k r, θ k r ≠ 0 → (p : ℤ) ^ L ∣ v k r - A * k)
      (hE : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i))
      (hx : Ev ψ cU x x') (hz : Ev ψ cE z z')
      (hy : Ev ψ (fun r => ∑ k ∈ S r, (v k r : Ω) * (θ k r : Ω) * T.ζ L ^ (g * k)) y y'),
      Cong (p := p) L (y + A * (z * x)) 0 := by
    intro hc T L ψ hψ g A θ v S cU cE x x' z z' y y' hv hE hx hz hy
    have hN : 0 < p ^ L := pow_pos hp.out.pos L
    have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
    obtain ⟨R1, R2⟩ := EvRing.ev_ring p Ω hc T L ψ hψ
    obtain ⟨U, rfl⟩ := (R2 _ _ _ hx).2.2.1
    obtain ⟨E, rfl⟩ := (R2 _ _ _ hz).2.2.1
    obtain ⟨Y, hY⟩ := (R2 _ _ _ hy).2.2.1
    have h1 := (R2 _ _ _ (R1 E U _ _ _ _ hz hx).1).2.2.2.2.1 (A : Ω) (Basic.isInt_intCast _) (GlobalTheory.Glue.SiegLoc.isAlgZp_int _)
    obtain ⟨V, hV⟩ := (R2 _ _ _ h1).2.2.1
    rw [← hV] at h1
    rw [← hY] at hy
    refine ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T L ψ hψ L _ _ _ (R1 Y V _ _ _ _ hy h1).2.1).1).2 fun r => ?_
    have e : (Y + V).coeff r = ∑ k ∈ S r, (((v k r - A * k) * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) := by
      rw [HahnSeries.coeff_add, hY, hV]
      simp only
      rw [GlobalTheory.Glue.SiegLoc.coeff_mul_finsum, ← neg_eq_iff_eq_neg.2 (hE r), mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [e]
    refine cong_sum _ (fun k => (v k r - A * k) * θ k r) _ (fun k => ?_) fun k => ?_
    · rw [GlobalTheory.Glue.SiegLoc.zpow_emod hN hζ]
      exact IsIntegral.pow (EvTwist.isInt_of_pow hN hζ) _
    · by_cases h : θ k r = 0
      · simp [h]
      · exact Dvd.dvd.mul_right (hv k r h) _
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  choose B hB using hB
  let S : ℤ → Finset ℤ := fun r => Finset.Icc (-(B r : ℤ)) (B r)
  have hS : ∀ (r : ℤ) (f : ℤ → Ω), (∀ k, θ k r = 0 → f k = 0) → ∑ᶠ k, f k = ∑ k ∈ S r, f k := fun r f hf =>
    finsum_eq_sum_of_support_subset _ fun k hk => by
      rw [Finset.mem_coe, Finset.mem_Icc, ← abs_le]
      exact not_lt.1 fun h => hk (hf k (hB r k h))
  have hE' : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ (m + 1) ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := fun r => by
    rw [← hE r, hS r _ fun k hk => by simp [hk]]
  obtain ⟨z, z', hz⟩ := GlobalTheory.Glue.SiegLoc.ev_cyc T (m + 1) ψ cE hE0 hEm
  obtain ⟨a, ha⟩ := GlobalTheory.Glue.SiegLoc.rep hψ g θ S r0 h0
  obtain ⟨y0, e0⟩ := ha fun _ _ => 1
  obtain ⟨y1, e1⟩ := ha fun _ j => j
  obtain ⟨y2, e2⟩ := ha fun i _ => i
  have hN : (0 : ℤ) < ((p ^ (m + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos _
  have hmod : ∀ r : ℤ, (p : ℤ) ^ (m + 1) ∣ ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ) - r := fun r => by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg r hN.ne')]
    have := Int.emod_add_mul_ediv r ((p ^ (m + 1) : ℕ) : ℤ)
    push_cast at this ⊢
    exact ⟨-(r / (p : ℤ) ^ (m + 1)), by linarith⟩
  obtain ⟨c1, hc1, k1⟩ := cong_val hc hψ g A₁ θ (fun _ r => ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
    (fun k r h => by simpa using dvd_add (hmod r) (hdiv k r h)) hE' hx hz e1
  obtain ⟨c2, hc2, k2⟩ := cong_val hc hψ g g θ (fun k _ => ((g * k % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
    (fun k r _ => hmod _) hE' hx hz e2
  have hcU : cU = fun r => ∑ k ∈ S r, ((1 : ℤ) : Ω) * (θ k r : Ω) * T.ζ (m + 1) ^ (g * k) := funext fun r => by
    rw [hU r, hS r _ fun k hk => by simp [hk]]
    simp
  rw [← hcU] at e0
  have hxe := (GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients p Ω hc T (m + 1) ψ hψ _ _ _ _ _ hx e0).1
  set w0 : On p (m + 1) := ∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
    algebraMap (O0 p) (On p (m + 1)) (a i j) * xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ) with hw0
  have hw : ι w0 = x := by
    rw [hxe, hw0]

    simp only [map_sum, map_mul, map_pow, AlgHom.commutes, hι.1, hι.2, Int.cast_one, one_mul]
  obtain ⟨w, hwu⟩ := GlobalTheory.Glue.SiegLoc.isUnit_of_inv ι (GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hc T (m + 1) hL ι hι).1 w0 (hw ▸ hx0) (hw ▸ hxi)
  obtain ⟨α, β, hd⟩ := GlobalTheory.K5.exists_isDlog p (m + 1) w
  obtain ⟨d1, d2⟩ := GlobalTheory.Glue.SiegLoc.coef m a w α β (hwu.trans hw0) hd
  obtain ⟨f1, d1⟩ := Ideal.mem_span_singleton'.1 d1
  obtain ⟨f2, d2⟩ := Ideal.mem_span_singleton'.1 d2
  replace d1 := congrArg ι d1
  replace d2 := congrArg ι d2

  simp only [map_sum, map_mul, map_pow, map_sub, map_natCast, map_one, AlgHom.commutes, hι.1, hι.2, hwu, hw, GlobalTheory.Glue.SiegLoc.zeta_one] at d1 d2
  simp only [Int.cast_natCast] at k1 k2
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  refine ⟨w, α, β, z, z', hd, hwu ▸ hw, hz, ⟨(ι f1 + c1) * x⁻¹,
    IsIntegral.mul (IsIntegral.add (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hc1) hxi, ?_⟩, ?_⟩
  · linear_combination x⁻¹ * k1 - x⁻¹ * d1 - (ι α + A₁ * z) * hinv
  · have hζ1 : T.ζ 1 - 1 ≠ 0 := sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using hp.out.one_lt))
    have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (pow_pos hp.out.pos _))
    rw [pow_one, div_eq_mul_inv] at hpd
    have hinv2 : (T.ζ 1 - 1) * (T.ζ 1 - 1)⁻¹ = 1 := mul_inv_cancel₀ hζ1
    have hpi : IsInt (p := p) (p : Ω) := by simpa using Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    refine ⟨(ι f2 * ((p : Ω) * (T.ζ 1 - 1)⁻¹) + p * c2) * x⁻¹,
      IsIntegral.mul (IsIntegral.add (IsIntegral.mul (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hpd) (IsIntegral.mul hpi hc2)) hxi, ?_⟩
    generalize (∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
      ((i : ℕ) : Ω) * algebraMap (O0 p) Ω (a i j) * T.ζ (m + 1) ^ (i : ℕ) * T.qq (m + 1) ^ (j : ℕ)) = Y at k2 d2
    linear_combination (p * x⁻¹) * k2 - (p * x⁻¹ * (T.ζ 1 - 1)⁻¹) * d2 - (p * x⁻¹ * (x * ι β - Y)) * hinv2
      - (p * (ι β + g * z)) * hinv
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P → (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) → (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  first | exact @GlobalTheory.primCan | exact GlobalTheory.primCan | (intros; apply GlobalTheory.primCan <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.coef_of_inv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  intro Ω _ _ ε X l _ _ N w b c hb γ _ hinv
  obtain ⟨hslP, -, -, hev, -⟩ := mon_expand ℤ_[l] w
  have hk : ∀ (u : Fin 2 → ℤ_[l]) (k : Fin (w + 1)),
      (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 ^ (k : ℕ) * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 ^ (w - (k : ℕ)) =
        ∑ i, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) * (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) := by
    intro u k

    rw [← hev, mZl, ← Betti.eval_slP, hslP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hev]
  have key : ∀ u : Fin 2 → ℤ_[l], b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) •
      ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
    intro u
    rw [← congrFun hinv u]
    show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) = _

    rw [Betti.toGQ_sl, hb, map_sum]
    simp_rw [map_smul, hk, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hz := GlobalTheory.homogeneous_poly_coeff_eq_zero l (X.Khat l)
    (fun a x ha hx => GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree Ω ε X l a x ha hx) w
    (fun i => c i - ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
    (by intro u; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, ← hb u, ← key u, sub_self])
  intro i
  exact sub_eq_zero.1 (congrFun hz i)
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.colemanNormOperator_iterate_succ_congr_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R, (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  first | exact @GlobalTheory.normOp_iterate_congr | exact GlobalTheory.normOp_iterate_congr | (intros; apply GlobalTheory.normOp_iterate_congr <;> assumption)
end
