module

import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA
public import ReciprocityTheory.SemistableReduction.LatSemiSt
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

namespace A2

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (h : I ≠ 0) : 0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I) (fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e.symm))

theorem absNorm_anti' {I J : FractionalIdeal (𝓞 K)⁰ K} (hIJ : I ≤ J) (hI : I ≠ 0) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact hI (FractionalIdeal.le_zero_iff.1 hIJ)
  have hX : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hIJ le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : I = J * (I * J⁻¹) := by
    rw [mul_comm I, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  have hIJ0 : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hX0 : X ≠ ⊥ := by
    rintro rfl
    apply hIJ0
    rw [← hX']
    exact FractionalIdeal.coeIdeal_bot
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hX', FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm X ≠ 0 := fun e => hX0 (Ideal.absNorm_eq_zero_iff.1 e)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  calc FractionalIdeal.absNorm J = FractionalIdeal.absNorm J * 1 := (mul_one _).symm
    _ ≤ FractionalIdeal.absNorm J * FractionalIdeal.absNorm (I * J⁻¹) :=
        mul_le_mul_of_nonneg_left hN (FractionalIdeal.absNorm_nonneg _)
    _ = FractionalIdeal.absNorm I := by rw [← map_mul, ← hdec]

theorem abs_norm_eq_prod (x : K) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun _ => rfl), ← h2]
  simp

theorem absNorm_span_real (x : K) :
    ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [FractionalIdeal.absNorm_span_singleton (𝓞 K), abs_norm_eq_prod]

theorem det_re_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.PosDef) : 0 < A.det.re := by
  simpa using (Complex.lt_def.1 h.det_pos).1

theorem exists_den {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K)) (hM : M.FG) :
    ∃ a ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (a • x i) := by
  have hc : ∀ i : Fin m, ∃ a ∈ (𝓞 K)⁰, ∀ b ∈ M.map (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K),
      IsLocalization.IsInteger (𝓞 K) (a • b) :=
    fun i => FractionalIdeal.isFractional_of_fg (hM.map _)
  choose a ha hb using hc
  refine ⟨∏ i, a i, prod_mem fun i _ => ha i, fun x hx i => ?_⟩
  have hxi := hb i (x i) (Submodule.mem_map_of_mem (f := (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K)) hx)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact IsLocalization.isInteger_smul hxi

theorem isInteger_det {m : ℕ} (x : Fin m → Fin m → K) (hx : ∀ i j, IsLocalization.IsInteger (𝓞 K) (x i j)) :
    IsLocalization.IsInteger (𝓞 K) (Matrix.of x).det := by
  have hx' : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i j := fun i j => hx i j
  choose y hy using hx'
  refine ⟨(Matrix.of y).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hy]

theorem detSub_isFractional {m : ℕ} (L : MLat K m) (hM : L.M.FG) : IsFractional (𝓞 K)⁰ L.detSub := by
  obtain ⟨a, ha, hint⟩ := exists_den L.M hM
  refine ⟨a ^ m, pow_mem ha m, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ m) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem detIdeal_coe {m : ℕ} (L : MLat K m) (h : IsFractional (𝓞 K)⁰ L.detSub) :
    (L.detIdeal : Submodule (𝓞 K) K) = L.detSub := by
  have e : L.detIdeal = ⟨L.detSub, h⟩ := dif_pos h
  rw [e]
  rfl

theorem det_mem {m : ℕ} (L : MLat K m) (x : Fin m → Fin m → K) (hx : ∀ i, x i ∈ L.M) :
    (Matrix.of x).det ∈ L.detSub :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem exists_det_ne {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K))
    (hM : Submodule.span K (M : Set (Fin m → K)) = ⊤) :
    ∃ x : Fin m → Fin m → K, (∀ i, x i ∈ M) ∧ (Matrix.of x).det ≠ 0 := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (M : Set (Fin m → K))
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan, hM]))
  let e := B.indexEquiv (Pi.basisFun K (Fin m))
  refine ⟨fun i => (e.symm i : Fin m → K), fun i => hs (e.symm i).2, ?_⟩
  have hli' : LinearIndependent K (fun i => (e.symm i : Fin m → K)) := hli.comp _ e.symm.injective
  have : IsUnit (Matrix.of fun i => (e.symm i : Fin m → K)) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

end A2


namespace A2
variable {K : Type} [Field K] [NumberField K]

end A2


namespace A2
variable {K : Type} [Field K] [NumberField K]

theorem detSub_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detSub = Submodule.span (𝓞 K) {(Matrix.of b).det} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro d ⟨x, hx, rfl⟩
    have : ∀ i, ∃ c : Fin m → 𝓞 K, ∑ j, c j • b j = x i := fun i => by
      have := hx i
      rw [hb] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using this
    have hx' : Matrix.of x = (Matrix.of c).map (algebraMap (𝓞 K) K) * Matrix.of b := by
      ext i j
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
      rw [← hc i]
      simp [Finset.sum_apply, Algebra.smul_def]
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det, hx', Matrix.det_mul]
    rfl
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨b, fun i => ?_, rfl⟩
    rw [hb]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem gramC_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC H σ b = ((Matrix.of b).map σ).transpose.conjTranspose * H * ((Matrix.of b).map σ).transpose := by
  ext i j
  simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, Matrix.mul_apply, dotProduct,
    Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem gramC_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    (ReciprocityTheory.MultiplicativeHeights.gramC H σ b).det = (Complex.normSq (σ (Matrix.of b).det) : ℂ) * H.det := by
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    RingHom.map_det σ (Matrix.of b), Complex.normSq_eq_conj_mul_self]
  simp only [RingHom.mapMatrix_apply, Complex.star_def]
  ring

end A2


theorem hadamardInequality : HadamardPD := by
  apply _root_.ReciprocityTheory.GeometryOfNumbersTheory.gramSt_hadamard <;> assumption

namespace A2
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise

end A2


end Formalism.L2.LamCM
