module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem slzDen_ne_zero (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h0 | h0
  · rw [h0] at hre
    simp at hre
    rw [Matrix.det_fin_two, h0, hre] at hδ
    simp at hδ
  · exact absurd h0 τ.im_pos.ne'

theorem slzMob_im (δ : M2) (τ : ℍ) :
    ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im
      = (δ.det : ℝ) * τ.im / Complex.normSq (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [Complex.div_im, Matrix.det_fin_two]
  simp
  push_cast
  ring

theorem slzMob_im_pos (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    0 < ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im := by
  rw [slzMob_im]
  apply div_pos
  · exact mul_pos (by exact_mod_cast hδ) τ.im_pos
  · exact Complex.normSq_pos.2 (slzDen_ne_zero δ hδ τ)

theorem slzMob_coe (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) : ℍ) : ℂ)
      = (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [ofComplex_apply_of_im_pos (slzMob_im_pos δ hδ τ)]

theorem automorphyFactor_mobius_cocycle_complex (a b c d a' b' c' d' t : ℂ) (h1 : c' * t + d' ≠ 0)
    (h2 : c * ((a' * t + b') / (c' * t + d')) + d ≠ 0) :
    (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') ∧
    ((a * a' + b * c') * t + (a * b' + b * d')) / ((c * a' + d * c') * t + (c * b' + d * d'))
      = (a * ((a' * t + b') / (c' * t + d')) + b) / (c * ((a' * t + b') / (c' * t + d')) + d) := by
  have e1 : (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') := by
    field_simp
    ring
  refine ⟨e1, ?_⟩
  rw [e1]
  field_simp
  ring

theorem slz_mul (k : ℕ) (f : ℍ → ℂ) (δ δ' : M2) (hδ : 0 < δ.det) (hδ' : 0 < δ'.det) :
    slz k (δ * δ') f = slz k δ' (slz k δ f) := by
  funext τ
  have h2 := slzDen_ne_zero δ hδ (ofComplex ((((δ' 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 0 1 : ℤ) : ℂ)) / (((δ' 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 1 1 : ℤ) : ℂ))))
  rw [slzMob_coe δ' hδ' τ] at h2
  obtain ⟨e1, e2⟩ := automorphyFactor_mobius_cocycle_complex ((δ 0 0 : ℤ) : ℂ) ((δ 0 1 : ℤ) : ℂ) ((δ 1 0 : ℤ) : ℂ) ((δ 1 1 : ℤ) : ℂ)
    ((δ' 0 0 : ℤ) : ℂ) ((δ' 0 1 : ℤ) : ℂ) ((δ' 1 0 : ℤ) : ℂ) ((δ' 1 1 : ℤ) : ℂ) (τ : ℂ) (slzDen_ne_zero δ' hδ' τ) h2
  simp only [slz]
  rw [slzMob_coe δ' hδ' τ, Matrix.det_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [e2, e1]
  simp only [mul_pow, mul_inv]
  ring

theorem slz_SL (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ) := by
  have hdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hg : ofComplex (((((γ : M2) 0 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 0 1 : ℤ) : ℂ)) / ((((γ : M2) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 1 1 : ℤ) : ℂ))) = γ • τ := by
    ext
    rw [slzMob_coe _ (by rw [hdet]; exact one_pos) τ, coe_specialLinearGroup_apply]
    simp
  simp only [slz]
  rw [hg, hdet]
  simp

theorem slzDen_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 :=
  slzDen_ne_zero (γ : M2) (by rw [Matrix.SpecialLinearGroup.det_coe γ]; exact one_pos) τ

theorem slz_continuous (k : ℕ) (f : ℍ → ℂ) (δ : M2) (hδ : 0 < δ.det) (hf : Continuous f) :
    Continuous (slz k δ f) := by
  have hw : Continuous (fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) :=
    ((continuous_const.mul continuous_coe).add continuous_const).div
      ((continuous_const.mul continuous_coe).add continuous_const) (slzDen_ne_zero δ hδ)
  have hg : Continuous (fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))) := by
    rw [isOpenEmbedding_coe.isInducing.continuous_iff]
    have : (UpperHalfPlane.coe ∘ fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))))
        = fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
      funext τ
      exact slzMob_coe δ hδ τ
    rw [this]
    exact hw
  have hj : Continuous (fun τ : ℍ => ((((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) :=
    (((continuous_const.mul continuous_coe).add continuous_const).pow k).inv₀
      (fun τ => pow_ne_zero k (slzDen_ne_zero δ hδ τ))
  exact (continuous_const.mul hj).mul (hf.comp hg)

theorem slz_scalar (k : ℕ) (f : ℍ → ℂ) (hk : 1 ≤ k) (n : ℕ) (τ : ℍ) (hn : 0 < n) :
    slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hτ : ofComplex ((((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ))) = τ := by
    have : (((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ)) = (τ : ℂ) := by
      simp only [Int.cast_zero, Int.cast_natCast, add_zero, zero_mul, zero_add]
      exact mul_div_cancel_left₀ _ hn'
    rw [this]
    exact ofComplex_apply τ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of]
  rw [hτ]
  push_cast
  field_simp
  ring

theorem slz_props : ∀ (k : ℕ) (f : ℍ → ℂ), 1 ≤ k → (∀ δ δ' : M2, 0 < δ.det → 0 < δ'.det → slz k (δ * δ') f = slz k δ' (slz k δ f)) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ)) ∧ (∀ (L : ℕ) (χ : ℤ → ℂ), Inv k L χ f ↔ ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → slz k (γ : M2) f = fun τ => χ (γ 1 1) * f τ) ∧ (∀ δ : M2, 0 < δ.det → Continuous f → Continuous (slz k δ f)) ∧ ∀ (n : ℕ) (τ : ℍ), 0 < n → slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  intro k f hk
  refine ⟨fun δ δ' hδ hδ' => slz_mul k f δ δ' hδ hδ', fun γ τ => slz_SL k f γ τ, ?_,
    fun δ hδ hf => slz_continuous k f δ hδ hf, fun n τ hn => slz_scalar k f hk n τ hn⟩
  intro L χ
  constructor
  · intro h γ hγ
    funext τ
    have hne := pow_ne_zero k (slzDen_SL_ne_zero γ τ)
    rw [slz_SL, h γ hγ τ]
    field_simp
  · intro h γ hγ τ
    have := congrFun (h γ hγ) τ
    rw [slz_SL, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero k (slzDen_SL_ne_zero γ τ))] at this
    rw [this]
    ring

end GlobalTheory.EisM
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.CharTwist

lemma exists_coeffs {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) :
    ∃ c : ZMod M → ℂ, (∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) ∧
      ∀ d u : ZMod M, IsUnit d → c u = ψ d * c (d * u) := by
  refine ⟨fun u => (M : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩
  · have h := ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  · obtain ⟨d, rfl⟩ := hd
    have h := ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)
    simp only [map_mul] at h
    rw [ZMod.dft_const_mul, Units.inv_mul_cancel_left] at h
    simp only [← h]; ring

lemma summable_of_polyB {a : ℕ → ℂ} (h : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) := by
  obtain ⟨C, A, hC⟩ := h
  set q : ℂ := cexp (2 * π * Complex.I * τ) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 (Complex.exp_ne_zero _)
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ A * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rwa [norm_norm])
  have h2 := ((summable_nat_add_iff 1).2 h1).mul_left (C * ‖q‖⁻¹)
  refine Summable.of_norm_bounded h2 fun n => ?_
  have e : cexp (2 * π * Complex.I * n * τ) = q ^ n := by
    rw [hq, ← Complex.exp_nat_mul]; congr 1; ring
  rw [e, norm_mul, norm_pow]
  calc ‖a n‖ * ‖q‖ ^ n ≤ C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ = _ := by push_cast; field_simp; ring

lemma qs_twist {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) {c : ZMod M → ℂ}
    (hc : ∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) {g : ℕ → ℂ} (hg : PolyB g) (τ : ℍ) :
    qs (fun n => ψ n * g n) τ = ∑ u : ZMod M, c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) := by
  have a := hasSum_sum (s := Finset.univ) fun (u : ZMod M) _ =>
    (summable_of_polyB hg ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)).hasSum.mul_left (c u)
  unfold qs
  rw [← a.tsum_eq]
  refine tsum_congr fun m => ?_
  beta_reduce
  rw [← hc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : u * (m : ZMod M) = ((u.val * m : ℤ) : ZMod M) := by simp
  have e2 : ZMod.stdAddChar (u * (m : ZMod M)) * cexp (2 * π * Complex.I * m * τ) =
      cexp (2 * π * Complex.I * m * (((((u.val : ℤ) : ℝ) / M) +ᵥ τ : ℍ) : ℂ)) := by
    rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add, coe_vadd]
    congr 1
    push_cast
    ring
  rw [← e2]
  ring

lemma vadd_smul {N M : ℕ} [NeZero M] (γ : SL(2, ℤ)) (hγ : ((N * M ^ 2 : ℕ) : ℤ) ∣ γ 1 0) (u v : ℤ)
    (h : (v : ZMod M) = ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u) (τ : ℍ) :
    ∃ δ : SL(2, ℤ), (N : ℤ) ∣ δ 1 0 ∧ ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      ((u : ℝ) / M) +ᵥ (γ • τ) = δ • (((v : ℝ) / M) +ᵥ τ) ∧
      ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  obtain ⟨c, hc⟩ := hγ
  push_cast at hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hd' := congrArg (Int.cast : ℤ → ZMod M) hd
  push_cast at hd'
  rw [ZMod.natCast_self] at hd'
  have h1 : (M : ℤ) ∣ u * γ 1 1 - v * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    linear_combination (-(u : ZMod M) * ((γ 1 1 : ℤ) : ZMod M)) * hd'
  obtain ⟨e, he⟩ := h1
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * N * c * M ∧
      δ 0 1 = γ 0 1 + e - u * v * N * c ∧ δ 1 0 = N * M ^ 2 * c ∧ δ 1 1 = γ 1 1 - N * c * v * M := by
    refine ⟨⟨!![γ 0 0 + u * N * c * M, γ 0 1 + e - u * v * N * c; N * M ^ 2 * c, γ 1 1 - N * c * v * M], ?_⟩,
      rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    linear_combination hd + N * M * c * he
  have hden : ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    rw [d10, d11, hc, coe_vadd]
    push_cast
    field_simp
    ring
  refine ⟨δ, ⟨M ^ 2 * c, by rw [d10]; ring⟩, by rw [d11]; simp, ?_, hden⟩
  apply UpperHalfPlane.ext
  have e1 := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply δ (((v : ℝ) / M) +ᵥ τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e1 e2
  have hz := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hz
  simp at hz
  have he' : (u : ℂ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = M * e := by exact_mod_cast he
  have hc' : ((γ 1 0 : ℤ) : ℂ) = N * M ^ 2 * c := by exact_mod_cast hc
  rw [coe_vadd, e1, e2, hden, eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz, d00, d01, coe_vadd, hc']
  push_cast
  field_simp
  linear_combination he'

theorem cf_twist : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M →
    CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  intro k N M χ φ g hM ⟨⟨hp, hi⟩, B, hB⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, hc1, hc2⟩ := exists_coeffs φ
  refine ⟨⟨?_, ?_⟩, (∑ u, ‖c u‖ ^ 2) * ∑ _u : ZMod M, B, fun τ => ?_⟩
  · obtain ⟨C, A, hC⟩ := hp
    refine ⟨C, A, fun n => le_trans ?_ (hC n)⟩
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one φ _)
  · intro γ hγ τ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod M) := by
      obtain ⟨e, he⟩ := hγ
      have dγ := congrArg (Int.cast : ℤ → ZMod M) (γ.det_coe)
      rw [Matrix.det_fin_two, he] at dγ
      push_cast at dγ
      rw [ZMod.natCast_self] at dγ
      exact IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M) (by linear_combination dγ)
    have hb : Function.Bijective fun u : ZMod M => ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u :=
      ((hu.pow 2).unit.mulLeft).bijective
    rw [qs_twist φ hc1 hp, qs_twist φ hc1 hp,
      ← hb.sum_comp fun u : ZMod M => c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    obtain ⟨δ, h0, h1, h2, h3⟩ := vadd_smul γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod M) ^ 2 * u).val : ℤ)
      (by simp) τ
    rw [h2, hi δ h0, h3, hc2 _ u (hu.pow 2)]
    simp only [ch, h1, map_pow]
    ring
  · rw [qs_twist φ hc1 hp]
    have hy : 0 ≤ τ.im ^ k := pow_nonneg τ.im_pos.le k
    set x : ZMod M → ℂ := fun u => qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) with hx
    have h1 : ‖∑ u, c u * x u‖ ≤ ∑ u, ‖c u‖ * ‖x u‖ :=
      (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun u _ => norm_mul _ _)
    have h2 : ‖∑ u, c u * x u‖ ^ 2 ≤ (∑ u, ‖c u‖ ^ 2) * ∑ u, ‖x u‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    refine (mul_le_mul_of_nonneg_right h2 hy).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun u _ => sq_nonneg _)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => ?_
    have := hB ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)
    rwa [vadd_im] at this

end GlobalTheory.EisM.CharTwist

end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private lemma summable_poly_mul_geometric (C : ℝ) (A : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * r ^ n := by
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have h := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * r ^ m)
  refine (h.mul_left (C * r⁻¹)).congr fun n => ?_
  have hr' : r ≠ 0 := hr0.ne'
  push_cast
  rw [pow_succ]
  field_simp

private lemma qs_term_bound (a : ℕ → ℂ) (C : ℝ) (A : ℕ) (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (y0 : ℝ) (n : ℕ) (w : ℂ) (hw : y0 < w.im) :
    ‖a n * cexp (2 * π * Complex.I * n * w)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-(2 * π * y0)) ^ n := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hexp : Real.exp (-(2 * π * n * w.im)) ≤ Real.exp (-(2 * π * y0)) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hp : (0:ℝ) ≤ 2 * π * n := by positivity
    have := mul_le_mul_of_nonneg_left hw.le hp
    nlinarith
  exact mul_le_mul (hC n) hexp (Real.exp_pos _).le (le_trans (norm_nonneg _) (hC n))

theorem qs_mdifferentiable : ∀ a : ℕ → ℂ, PolyB a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rintro a ⟨C, A, hC⟩
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
  have hr0 : 0 < Real.exp (-(2 * π * y0)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * π * y0)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_poly_mul_geometric C A hr0 hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU (fun n w hw => qs_term_bound a C A hC y0 n w hw)
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory

theorem zs_iter_Uo {R : Type*} [CommRing R] (l r : ℕ) (a : ℕ → R) (n : ℕ) :
    (GlobalTheory.EisM.Uo l)^[r] a n = a (l ^ r * n) := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', GlobalTheory.EisM.Uo, ih]
    congr 1; ring

theorem zs_norm_char_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N)
    (θ : DirichletCharacter ℂ N) (z : ZMod N) : ‖ι.symm (θ z)‖ ≤ 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  by_cases hz : IsUnit z
  · obtain ⟨u, rfl⟩ := hz
    have h1 : (θ (u : ZMod N)) ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ι.symm (θ (u : ZMod N))‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2).le
  · rw [MulChar.map_nonunit θ hz, map_zero, norm_zero]; exact zero_le_one

theorem zs_norm_exp {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N) (y : ℕ) (d : ℤ) :
    ‖ι.symm (cexp (2 * π * Complex.I * (y * d) / N))‖ = 1 := by
  have h1 : (cexp (2 * π * Complex.I * (y * d) / N)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(y : ℤ) * d, ?_⟩
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have h2 : ‖ι.symm (cexp (2 * π * Complex.I * (y * d) / N))‖ ^ N = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h2

theorem zs_norm_hat_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N)
    (θ : DirichletCharacter ℂ N) (d : ℤ) : ‖ι.symm (GlobalTheory.EisM.hat (fun z => θ z) d)‖ ≤ 1 := by
  unfold GlobalTheory.EisM.hat

  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
  rw [map_mul, norm_mul, zs_norm_exp ι hN, mul_one]
  exact zs_norm_char_le_one ι hN θ _

end GlobalTheory

namespace GlobalTheory

end GlobalTheory

end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N → ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l), ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_isCoc | exact GlobalTheory.KZ.H3.exists_pot_of_isCoc | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_isCoc <;> assumption)
end
