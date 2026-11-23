module

import Development.WeilBound.ThetaLifts.LatticeBasics.RealInvL
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.EvXTemperate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle014

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI


open Complex in
theorem tg_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  apply GlobalTheory.ThK.Dbl.Dense.temperate_exp <;> assumption

section admitted

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def rhoL (ψ : AddChar (AF F) ℂ) (p : (κ → AF F) × (κ → AF F)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun := schr ψ p
  map_add' φ φ' := by funext x; simp [schr, mul_add]
  map_smul' a φ := by funext x; simp [schr]; ring

def arc (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1

def phz (p : (κ → AF F) × (κ → AF F)) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (∑ i, y i * arc F p.2 i + InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1) : ℝ) : ℂ))

theorem phz_tg (p : (κ → AF F) × (κ → AF F)) : (phz F p).HasTemperateGrowth := by
  have hlin : Function.HasTemperateGrowth (fun y : κ → mixedEmbedding.mixedSpace F =>
      ∑ i, y i * arc F p.2 i + InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1) := by
    have hi : ∀ i, Function.HasTemperateGrowth (fun y : κ → mixedEmbedding.mixedSpace F => y i * arc F p.2 i) :=
      fun i => ((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace F)).flip (arc F p.2 i) ∘L
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth
    fun_prop
  have hT : Function.HasTemperateGrowth (fun z : mixedEmbedding.mixedSpace F =>
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) :=
    (LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).hasTemperateGrowth
  have hg : Function.HasTemperateGrowth (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (s : ℂ))) := by
    have h := tg_exp.comp (((-(2 * Real.pi)) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth)
    convert h using 1
    funext s
    simp only [Function.comp_apply, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id',
      Pi.smul_apply, id_eq, smul_eq_mul]
    push_cast
    congr 1 <;> ring
  exact hg.comp (hT.comp hlin)

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (p : (κ → AF F) × (κ → AF F))
    (hp : ∀ i, (p.1 i).2 = 0 ∧ (p.2 i).2 = 0) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    schr ψ p (pureA F f g) = pureA F (fun y => phz F p y * f (y + arc F p.1)) g := by
  funext x
  obtain ⟨-, -, hinf⟩ := hψ
  have hs1 : ∀ y z : κ → AF F, (y ⬝ᵥ z).1 = ∑ i, (y i).1 * (z i).1 := fun y z =>
    map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (fun i => y i * z i) Finset.univ
  have hs2 : ∀ y z : κ → AF F, (y ⬝ᵥ z).2 = ∑ i, (y i).2 * (z i).2 := fun y z =>
    map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (fun i => y i * z i) Finset.univ
  have hsnd : (fun i => ((x + p.1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (p.1 i).2 = (x i).2
    rw [(hp i).1, add_zero]
  have hfst : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p.1) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + arc F p.1 := by
    funext i
    exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (p.1 i).1
  have ha2 : (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).2 = 0 := by
    show (x ⬝ᵥ p.2).2 + (⅟(2 : AF F)).2 * (p.1 ⬝ᵥ p.2).2 = 0
    rw [hs2, hs2]
    simp [(hp _).2]
  have hat : At (evI F) (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) := by
    intro u hu
    have hu1 : u.1 = 0 :=
      (map_eq_zero_iff (InfiniteAdeleRing.ringEquiv_mixedSpace F) (RingEquiv.injective _)).mp hu
    rw [smul_eq_mul]
    refine Prod.ext ?_ ?_
    · show u.1 * (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).2 = 0
      rw [ha2, mul_zero]
  have htr : evI F (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) =
      ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * arc F p.2 i +
        InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x ⬝ᵥ p.2).1 + (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1) = _

    rw [map_add (f := _), hs1, map_sum]
    simp only [map_mul, arc]
  simp only [schr, pureA]
  rw [hinf _ hat, hsnd, hfst, htr]
  simp only [phz]
  ring

theorem rho_adm (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ)
    (p : (κ → AF F) × (κ → AF F)) (hp : ∀ i, (p.1 i).2 = 0 ∧ (p.2 i).2 = 0) :
    l ∘ₗ rhoL F ψ p ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T0, hT0⟩ := hl g hg
  have htr : Function.HasTemperateGrowth (fun y : κ → mixedEmbedding.mixedSpace F => y + arc F p.1) := by
    fun_prop
  have hanti : AntilipschitzWith 1 (fun y : κ → mixedEmbedding.mixedSpace F => y + arc F p.1) :=
    (IsometryEquiv.addRight (arc F p.1)).isometry.antilipschitz
  let S : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) →L[ℂ] 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (phz F p)).comp (SchwartzMap.compCLMOfAntilipschitz ℂ htr hanti)
  refine ⟨T0.comp S, fun f => ?_⟩
  have hf : (⇑(S f)) = fun y => phz F p y * f (y + arc F p.1) := by
    funext y
    simp [S, SchwartzMap.smulLeftCLM_apply_apply (phz_tg F p), smul_eq_mul]
  rw [LinearMap.comp_apply]
  show l (schr ψ p (pureA F f g)) = _
  rw [schr_pureA F ψ hψ p hp, ← hf, hT0]
  rfl

end admitted

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

def mob (M : M2 n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (M.toBlocks₁₁ * Z + M.toBlocks₁₂) * (M.toBlocks₂₁ * Z + M.toBlocks₂₂)⁻¹

theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem mob_mul (M N : M2 n) (Z : Matrix (Fin n) (Fin n) ℂ) (hV : IsUnit (N.toBlocks₂₁ * Z + N.toBlocks₂₂).det) :
    mob (M * N) Z = mob M (mob N Z) := by
  set V := N.toBlocks₂₁ * Z + N.toBlocks₂₂ with hVdef
  set W := N.toBlocks₁₁ * Z + N.toBlocks₁₂ with hWdef
  have h1 : (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = M.toBlocks₁₁ * W + M.toBlocks₁₂ * V := by
    rw [toBlocks₁₁_mul, toBlocks₁₂_mul, hVdef, hWdef]; noncomm_ring
  have h2 : (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = M.toBlocks₂₁ * W + M.toBlocks₂₂ * V := by
    rw [toBlocks₂₁_mul, toBlocks₂₂_mul, hVdef, hWdef]; noncomm_ring
  clear_value V W
  have hVV : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hV
  have hVV' : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hV
  have e1 : M.toBlocks₁₁ * (W * V⁻¹) + M.toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂ * V) * V⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have e2 : M.toBlocks₂₁ * (W * V⁻¹) + M.toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂ * V) * V⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  unfold mob
  rw [h1, h2, ← hWdef, ← hVdef, e1, e2, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv V hV, Matrix.mul_assoc,
    ← Matrix.mul_assoc V⁻¹, hVV', Matrix.one_mul]

theorem mob_nU (b Z : Matrix (Fin n) (Fin n) ℂ) : mob (nU b) Z = Z + b := by
  simp [mob, nU]

theorem mob_mLc (a Z : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : mob (mLc a) Z = a * Z * aᴴ := by
  have h : IsUnit (aᴴ).det := by rw [Matrix.det_conjTranspose]; exact ha.star
  simp [mob, mLc, Matrix.nonsing_inv_nonsing_inv _ h]

theorem mob_JJ_diag (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) :
    mob (JJ n) (Matrix.diagonal z) = Matrix.diagonal fun j => (-z j)⁻¹ := by
  simp only [mob, JJ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul, Matrix.neg_mul]
  rw [Matrix.diagonal_neg]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hz i]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

abbrev Z0 (sg : ℤˣ) : Matrix (Fin n) (Fin n) ℂ := (Complex.I * ((sg : ℤ) : ℂ)) • 1

theorem sg_sq (sg : ℤˣ) : ((sg : ℤ) : ℂ) * ((sg : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or sg with h | h <;> simp [h]

theorem mob_K (sg : ℤˣ) (M : M2 n) (hM : InK M) (hV : IsUnit (M.toBlocks₂₁ * Z0 sg + M.toBlocks₂₂).det) :
    mob M (Z0 sg) = Z0 sg := by
  obtain ⟨hG, hU⟩ := hM
  have hU' : M * Mᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * M = M * JJ n := by
    calc JJ n * M = (M * Mᴴ) * JJ n * M := by rw [hU', Matrix.one_mul]
      _ = M * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = M * JJ n := by rw [hG]
  have hM' := Matrix.fromBlocks_toBlocks M
  rw [← hM'] at hc
  simp only [JJ, Matrix.fromBlocks_multiply] at hc
  simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero] at hc
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hc
  set σ : ℂ := ((sg : ℤ) : ℂ)
  have hσ := sg_sq sg
  set X := M.toBlocks₂₁ * Z0 sg + M.toBlocks₂₂ with hX
  have hnum : M.toBlocks₁₁ * Z0 sg + M.toBlocks₁₂ = (Complex.I * σ) • X := by
    rw [hX, e1, e2]
    simp only [Z0, Matrix.mul_smul, Matrix.mul_one, smul_add, Matrix.neg_mul, smul_neg, smul_smul]
    rw [show Complex.I * σ * (Complex.I * σ) = -1 by rw [mul_mul_mul_comm, Complex.I_mul_I, hσ]; ring]
    simp [neg_smul]; abel
  unfold mob
  rw [hnum, ← hX, Matrix.smul_mul, Matrix.mul_nonsing_inv X hV]

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

theorem fP_add_smul (a : ℂ) (P Q : PX m n) : fP (a • P + Q) = a • fP P + fP Q := by
  funext u
  simp [fP, evX, MvPolynomial.eval_add, MvPolynomial.smul_eval, add_mul, mul_assoc]

theorem fP_zero : fP (0 : PX m n) = 0 := by
  funext u
  simp [fP, evX]

theorem fP_one_zero : fP (1 : PX m n) 0 = 1 := by
  simp [fP, evX, gs]

section Real

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (AddMonoidAlgebra.coeff p k).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (AddMonoidAlgebra.coeff p k).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : AddMonoidAlgebra.coeff (reP p) k = (AddMonoidAlgebra.coeff p k).re := by
  classical
  rw [reP, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_re]

theorem coeff_imP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : AddMonoidAlgebra.coeff (imaginary p) k = (AddMonoidAlgebra.coeff p k).im := by
  classical
  rw [imaginary, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_im]

theorem eval_map_real (q : MvPolynomial σ ℝ) (y : σ → ℝ) :
    MvPolynomial.eval (fun i => (y i : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) q) = ((MvPolynomial.eval y q : ℝ) : ℂ) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = MvPolynomial.map (algebraMap ℝ ℂ) (reP p) + MvPolynomial.C Complex.I * MvPolynomial.map (algebraMap ℝ ℂ) (imaginary p) := by
  ext k
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_reP,
    coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, MvPolynomial.eval (fun i => (y i : ℂ)) p = 0) :
    p = 0 := by
  have hre : ∀ y : σ → ℝ, MvPolynomial.eval y (reP p) = 0 ∧ MvPolynomial.eval y (imaginary p) = 0 := by
    intro y
    have h1 := h y
    rw [eq_map_re_add_im p, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C] at h1
    rw [eval_map_real, eval_map_real] at h1
    have hr := congrArg Complex.re h1
    have hi := congrArg Complex.im h1
    simp at hr hi
    exact ⟨hr, hi⟩
  have a1 : reP p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).1
  have a2 : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).2
  rw [eq_map_re_add_im p, a1, a2]
  simp

end Real

def subF (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)
  else MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)

def subG (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.C (2 * Complex.I)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.X (k.1, k.2.1, true))
  else MvPolynomial.C (2 : ℂ)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.X (k.1, k.2.1, true))

theorem subG_subF (P : PX m n) : MvPolynomial.bind₁ subG (MvPolynomial.bind₁ subF P) = P := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x _ = MvPolynomial.aeval x P
  rw [MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]
  have e : (fun i => MvPolynomial.aeval (fun i => MvPolynomial.aeval x (subG (m := m) (n := n) i)) (subF i)) = x := by
    funext k
    obtain ⟨a, j, b⟩ := k
    cases b <;> simp [subF, subG] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [e]

theorem evX_injective : Function.Injective (evX (m := m) (n := n)) := by
  intro P Q h
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : ∀ x, evX R x = 0 := fun x => by
    simp only [R, evX, map_sub]; exact sub_eq_zero.2 (congrFun h x)
  have h0 : MvPolynomial.bind₁ subF R = 0 := by
    apply eq_zero_of_eval_real
    intro y
    change MvPolynomial.aeval (fun i => (y i : ℂ)) _ = 0
    rw [MvPolynomial.aeval_bind₁]
    have := hR (fun a j => (y (a, j, false) : ℂ) + Complex.I * y (a, j, true))
    rw [evX] at this
    have e : (fun i => MvPolynomial.aeval (fun i => (y i : ℂ)) (subF (m := m) (n := n) i)) =
        fun k => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true))
          else (y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true) := by
      funext k
      obtain ⟨a, j, b⟩ := k
      cases b <;> simp [subF, Complex.ext_iff]
    rw [e]
    exact this
  rw [← subG_subF R, h0, map_zero]

theorem fP_injective : Function.Injective (fP (m := m) (n := n)) := by
  intro P Q h
  apply evX_injective
  funext u
  have e := congrFun h u
  simp only [fP] at e
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) e

theorem isSw_fP (P : PX m n) : IsSw (fP P) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_schwartz_poly_mul_gauss m n P
  exact ⟨φ, hφ⟩

theorem fP_eq_gZ (sg : ℤˣ) (P : PX m n) :
    fP P = fun u => evX P u * gZ sg ((Complex.I * ((sg : ℤ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) u := by
  funext u
  simp only [fP, gs, gZ]
  congr 2
  have htr : Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have hI : Complex.I * ((sg : ℤ) : ℂ) * (Complex.I * ((sg : ℤ) : ℂ)) = -1 := by
    rcases Int.units_eq_one_or sg with rfl | rfl <;> simp
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, htr, smul_eq_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (-2 * (Real.pi : ℂ) * ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ)) * hI

theorem fin_deg (d : ℕ) : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d) :=
  inferInstance

def evW (d : ℕ) : MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d →ₗ[ℂ] ((Fin m → Fin n → ℂ) → ℂ) where
  toFun Q u := evX Q.1 u
  map_add' Q Q' := by funext u; simp [evX]
  map_smul' a Q := by funext u; simp [evX]

theorem evW_injective (d : ℕ) : Function.Injective (evW (m := m) (n := n) d) := fun Q Q' h =>
  Subtype.ext (evX_injective (funext fun u => congrFun h u))

theorem continuousOn_of_evX {X : Type} [TopologicalSpace X] {S : Set X} (d : ℕ) (φ : X → PX m n)
    (hd : ∀ x ∈ S, (φ x).totalDegree ≤ d) (hc : ∀ u, ContinuousOn (fun x => evX (φ x) u) S) (l : PX m n →ₗ[ℂ] ℂ) :
    ContinuousOn (fun x => l (φ x)) S := by
  classical
  set W := MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d
  let e : W ≃ₗ[ℂ] LinearMap.range (evW (m := m) (n := n) d) := LinearEquiv.ofInjective _ (evW_injective d)
  haveI : FiniteDimensional ℂ (LinearMap.range (evW (m := m) (n := n) d)) := e.finiteDimensional
  let l' : LinearMap.range (evW (m := m) (n := n) d) →ₗ[ℂ] ℂ := l ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hl' : Continuous l' := LinearMap.continuous_of_finiteDimensional l'
  have hW : ∀ x ∈ S, φ x ∈ W := fun x hx => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hd x hx)
  rw [continuousOn_iff_continuous_restrict]
  let g : S → LinearMap.range (evW (m := m) (n := n) d) := fun x => e ⟨φ x, hW x x.2⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun u => ?_
    exact (hc u).restrict
  refine (hl'.comp hg).congr fun x => ?_
  simp [l', g]

theorem gramX_true (x : Fin m → Fin n → ℂ) : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
  ext i j
  simp [gramX, Qp, Qb, evX, Matrix.mul_apply, Matrix.conjTranspose_apply, MvPolynomial.eval_sum]

end PositivityTheory.SiegelWeilFormula.KLI

end
end
