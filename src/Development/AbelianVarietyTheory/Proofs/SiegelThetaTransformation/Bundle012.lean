module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

@[expose] public section

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  first | exact @GlobalTheory.SW.isSB_algebra_haar_linear | exact GlobalTheory.SW.isSB_algebra_haar_linear | (intros; apply GlobalTheory.SW.isSB_algebra_haar_linear <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.TransComp

theorem qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j
  simp [qm, Matrix.mul_apply]

theorem qm_add {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j
  simp [qm]

theorem qm_sub {α β : Type} (A B : Matrix α β ℚ) : qm (A - B) = qm A - qm B := by
  ext i j
  simp [qm]

theorem qm_transpose {α β : Type} (A : Matrix α β ℚ) : qm Aᵀ = (qm A)ᵀ := rfl

theorem qm_zero {α β : Type} : qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [qm]

theorem qm_one {α : Type} [DecidableEq α] : qm (1 : Matrix α α ℚ) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [qm, Matrix.one_apply, hij]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem blocks {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ) :
    σ.toBlocks₂₁ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₁ᵀ * σ.toBlocks₂₁ = 0 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₂ᵀ * σ.toBlocks₂₁ = 1 := by
  have h' := h
  rw [← Matrix.fromBlocks_toBlocks σ] at h'
  obtain ⟨h1, -, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h'
  refine ⟨sub_eq_zero.2 h1.symm, ?_⟩

  have h4 := congrArg Matrix.transpose h3
  simpa [Matrix.transpose_sub, Matrix.transpose_mul] using h4

theorem mul_block (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
    Fintype.sum_sum_type]

theorem key {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ)
    {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (hd : (spDen σ τ).det ≠ 0) (hs : (spAct σ τ).IsSymm) :
    qm σ.toBlocks₁₁ = spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ := by
  have hu : IsUnit (spDen σ τ).det := isUnit_iff_ne_zero.mpr hd

  have h1 : (spDen σ τ)ᵀ * spAct σ τ = (qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂)ᵀ := by
    have hs' : (spAct σ τ)ᵀ = spAct σ τ := hs
    rw [← hs']
    unfold spAct
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.one_mul]
  have hτ' : τᵀ = τ := hτ
  obtain ⟨b1, b2⟩ := blocks h
  have e1 := congrArg qm b1
  have e2 := congrArg qm b2
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_zero] at e1
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_one] at e2
  have h2 : (spDen σ τ)ᵀ * (qm σ.toBlocks₁₁ - spAct σ τ * qm σ.toBlocks₂₁) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h1]
    unfold spDen
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      hτ']
    calc (τ * (qm σ.toBlocks₂₁)ᵀ + (qm σ.toBlocks₂₂)ᵀ) * qm σ.toBlocks₁₁ -
          (τ * (qm σ.toBlocks₁₁)ᵀ + (qm σ.toBlocks₁₂)ᵀ) * qm σ.toBlocks₂₁
        = τ * ((qm σ.toBlocks₂₁)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₁)ᵀ * qm σ.toBlocks₂₁) +
          ((qm σ.toBlocks₂₂)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₂)ᵀ * qm σ.toBlocks₂₁) := by
          noncomm_ring
      _ = 1 := by rw [e1, e2, Matrix.mul_zero, zero_add]
  rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv h2]
  abel

end GlobalTheory.SW.TransComp


open GlobalTheory.SW.TransComp in
theorem GlobalTheory.SW.transS_comp : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  intro κ ι _ _ _ σ σ' hσ hσ' φ ψ χ h1 h2 τ hτ ζ
  obtain ⟨hd, hmem, -, -, hcomp⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ τ hτ
  obtain ⟨hden, hact⟩ := hcomp σ' hσ'
  have hd' := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ' hσ' _ hmem).1
  rw [hden, hact]

  have hk := key hσ hτ.1 hd hmem.1
  have hD' : qm σ'.toBlocks₂₂ = spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ := by
    rw [spDen, add_sub_cancel_left]
  have hinv' : (spDen σ' (spAct σ τ))⁻¹ * spDen σ' (spAct σ τ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd')

  have hM : (spDen σ τ)⁻¹ * ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) * ((spDen σ τ)⁻¹)ᵀ +
      (spDen σ τ)⁻¹ * qm σ.toBlocks₂₁ =
      (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁ := by
    rw [mul_block, qm_add, qm_mul, qm_mul, hk, hD', Matrix.mul_inv_rev]
    have inner : qm σ'.toBlocks₂₁ * (spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ) +
        (spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ) * qm σ.toBlocks₂₁ =
        qm σ'.toBlocks₂₁ * ((spDen σ τ)⁻¹)ᵀ + spDen σ' (spAct σ τ) * qm σ.toBlocks₂₁ := by
      noncomm_ring
    rw [inner, Matrix.mul_add, Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹,
      Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹, ← Matrix.mul_assoc
      (spDen σ' (spAct σ τ))⁻¹ (spDen σ' (spAct σ τ)), hinv', Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have hq : ∀ v : ι → ℂ, v ⬝ᵥ ((spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁) *ᵥ v =
      (v ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) *ᵥ (v ᵥ* (spDen σ τ)⁻¹) +
        v ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ v := by
    intro v
    rw [← hM, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hfun : (fun k => ζ k ᵥ* (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹) =
      fun k => (ζ k ᵥ* (spDen σ τ)⁻¹) ᵥ* (spDen σ' (spAct σ τ))⁻¹ := by
    funext k
    rw [Matrix.mul_inv_rev, Matrix.vecMul_vecMul]
  rw [hfun, h2 _ hmem, h1 τ hτ ζ, Matrix.det_mul, mul_pow]
  simp only [hq, Finset.sum_add_distrib, mul_add, Complex.exp_add]
  ring
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ.Row

variable {ι : Type} [Fintype ι]



open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.SW.FourierJ.Row.poisson_class : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : ℕ), 0 < R → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, -τ⁻¹ ∈ _root_.GlobalTheory.SW.Siegel ι →
    IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧
    ∀ (a : ι → ℚ) (ζ : ι → ℂ),
    (Summable fun m : ι → ℤ => ‖_root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    (Summable fun m : ι → ℤ =>
      ‖_root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) *
      ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
    c * ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
      _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) := by
  intro ι _ _ R hR τ hτ hτ' hdet
  have hτS : _root_.GlobalTheory.IsSiegel τ := hτ
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set Ω : Matrix ι ι ℂ := ((R ^ 2 : ℕ) : ℂ) • τ with hΩdef
  have hΩ : _root_.GlobalTheory.IsSiegel Ω := hτS.natCast_smul (pow_pos hR 2)
  have hΩinv : Ω⁻¹ = ((R : ℂ) ^ 2)⁻¹ • τ⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hΩdef, smul_mul_smul_comm, Matrix.nonsing_inv_mul τ hdet]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hRc), one_smul]
  have T1 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ) • fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ) := by
      funext i
      simp only [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      field_simp
      ring
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, _root_.GlobalTheory.SW.FourierJ.gs, hv, Pi.zero_apply, Complex.ofReal_zero,
      add_zero]
    generalize (fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)) = x
    congr 1
    simp only [hΩdef, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    push_cast
    ring
  have T2 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ)⁻¹ • fun i => ((m i : ℤ) : ℂ) := by
      funext i
      simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv]
    have hsymm : ζ ᵥ* τ⁻¹ = τ⁻¹ *ᵥ ζ := by
      rw [← Matrix.mulVec_transpose, hτS.isSymm.inv.eq]
    have hq : (((a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) : ℚ)) : ℂ) =
        (fun i => ((m i : ℤ) : ℂ)) ⬝ᵥ fun i => (((a i : ℝ) / R : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.smul_apply, _root_.GlobalTheory.SW.FourierJ.zv, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit : (fun i => (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) i + (((a i : ℝ) / R : ℝ) : ℂ)) =
        Ω⁻¹ *ᵥ ((R : ℂ) • ζ) + fun i => (((a i : ℝ) / R : ℝ) : ℂ) := rfl
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, Pi.zero_apply, Complex.ofReal_zero, add_zero, hsplit]
    rw [_root_.GlobalTheory.SW.FourierJ.gs, _root_.GlobalTheory.SW.FourierJ.ech, ← Complex.exp_add, hv, hsymm, hq]
    generalize (fun i => ((m i : ℤ) : ℂ)) = x
    congr 1
    simp only [hΩinv, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_neg, dotProduct_add, smul_eq_mul]
    first | (field_simp; ring) | field_simp | ring
  refine ⟨_root_.GlobalTheory.siegelGaussIntegral Ω, ?_, fun a ζ => ?_⟩
  · have h := hΩ.siegelGaussIntegral_sq_mul_det
    rw [hΩdef, smul_smul, Matrix.det_smul] at h
    rw [show ((-I) * (R : ℂ) ^ 2) = -I * ((R ^ 2 : ℕ) : ℂ) by push_cast; ring]
    exact h
  have hS1 := hΩ.summable_norm_riemannThetaTerm (fun i => (a i : ℝ) / R) 0 ((R : ℂ) • ζ)
  have hS2 := hΩ.neg_inv.summable_norm_riemannThetaTerm 0 (fun i => (a i : ℝ) / R)
    (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))
  refine ⟨?_, ?_, ?_⟩
  · exact hS1.congr fun m => by rw [T1]
  · refine hS2.congr fun m => ?_
    rw [← T2, norm_mul, _root_.GlobalTheory.SW.FourierJ.norm_ech, one_mul]
  · have e1 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T1 a ζ m
    have e2 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T2 a ζ m
    have hw : (R : ℂ) • ζ ⬝ᵥ Ω⁻¹ *ᵥ ((R : ℂ) • ζ) = ζ ⬝ᵥ τ⁻¹ *ᵥ ζ := by
      rw [hΩinv]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      first | (field_simp; ring) | field_simp
    rw [e1, e2, hΩ.riemannTheta_eq_neg_inv, hw]
    have hexp : cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * cexp (-(π * I) * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    linear_combination (_root_.GlobalTheory.siegelGaussIntegral Ω *
      _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))) * hexp

end GlobalTheory.SW.FourierJ.Row
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → Summable (fun x => φ x * F x) → ∑' x, φ x * F x = ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ∑' m : κ → ι → ℤ, F (rep R n + (R : ℚ) • zm m) := by
  first | exact @GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets | exact GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets | (intros; apply GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → haar φ = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ * ∑ n : κ → ι → Fin (R * R), φ (rep R n) := by
  first | exact @GlobalTheory.SW.FourierJ.haar_eq_sum_rep | exact GlobalTheory.SW.FourierJ.haar_eq_sum_rep | (intros; apply GlobalTheory.SW.FourierJ.haar_eq_sum_rep <;> assumption)
end
