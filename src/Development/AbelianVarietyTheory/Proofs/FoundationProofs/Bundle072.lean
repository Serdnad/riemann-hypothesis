module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.NumberTheory.ModularForms.Basic
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
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

section

noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

lemma wOld_mul_ulFam (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) :
    wOld N l a b * !![1, (j : ℤ); 0, (l : ℤ)] = (l : ℤ) • mat (gaOld N l a b h j) := by
  ext i m
  fin_cases i <;> fin_cases m <;>
    simp [wOld, gaOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wOld_det (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma mat_det_pos (γ : SL(2, ℤ)) : 0 < (mat γ).det := by simp [mat]

theorem trOld_eq : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l →
    trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b h G hl
  have hW : 0 < (wOld N l a b).det := by rw [wOld_det N l a b h]; exact_mod_cast hl
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold trOld
  congr 1
  rw [UlF, hkF, Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (ulFam_det l hl j).ne']
  have e : wOld N l a b * ulFam l j = (l : ℤ) • mat (gaOld N l a b h j) := wOld_mul_ulFam N l a b h j
  rw [e, slash_toGL_smul k l hl _ (mat_det_pos _), smul_smul, ← zpow_add₀ hl', slash_SL_eq]
  simp

end GlobalTheory.HeckeFamilyMatrices
end
end

section

noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wSqOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : SL(2, ℤ) :=
  ⟨!![(l : ℤ) + a * N, a * (1 + b); (N : ℤ) * l * (1 + b), (N : ℤ) * a + l * b ^ 2], by
    rw [Matrix.det_fin_two_of]; linear_combination ((l : ℤ) * b - N * a + 1) * h⟩

lemma oldformLevelRaisingMatrix_det_eq_level (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma atkin_lehner_square_mul (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * wOld N l a b = (l : ℤ) • mat (wSqOld N l a b h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wOld, wSqOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wSqOld_mem (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wSqOld N l a b h ∈ Gamma0 (N * l) := by
  rw [Gamma0_mem]
  have : ((((wSqOld N l a b h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) = ((N * l : ℕ) : ℤ) * (1 + b) := by
    simp [wSqOld]
  rw [this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

lemma wSqOld_entry (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    ((mat (wSqOld N l a b h) 1 1 : ℤ) : ZMod N) = (b : ZMod N) := by
  have e : mat (wSqOld N l a b h) 1 1 = b + (N : ℤ) * (a * (1 + b)) := by
    simp [wSqOld, mat]; linear_combination b * h
  rw [e]; push_cast; simp

theorem wOld_slash_slash (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N)
    (G : ℍ → ℂ) (hl : 0 < l) (hG : ChiInv k N (N * l) χ G) :
    (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  have hd : (wOld N l a b).det ≠ 0 := by rw [oldformLevelRaisingMatrix_det_eq_level N l a b h]; exact_mod_cast hl.ne'
  have hM : 0 < (mat (wSqOld N l a b h)).det := by simp [mat]
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hd hd, atkin_lehner_square_mul N l a b h, slash_toGL_smul k l hl _ hM,
    ← slash_SL_eq, hG _ (wSqOld_mem N l a b h), wSqOld_entry, smul_smul]

end GlobalTheory.HeckeFamilyMatrices
end
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wConjMat (N l a b p q t s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![l * b * p + a * b * (N * l * t) - N * l * q - N * a * s, -a * p - a ^ 2 * N * t + l * q + a * s;
    N * l * (b * p + l * b ^ 2 * t - N * q - b * s), -N * a * p - a * b * (N * l * t) + N * l * q + l * b * s]

lemma wConjMat_det (N l a b p q t s : ℤ) (hab : l * b - N * a = 1) (hd : p * s - q * (N * l * t) = 1) :
    (wConjMat N l a b p q t s).det = 1 := by
  rw [wConjMat, Matrix.det_fin_two_of]
  linear_combination (l * b - N * a) ^ 2 * hd + (l * b - N * a + 1) * hab

lemma wOld_mul_eq (N l : ℕ) (a b p q t s : ℤ) (hab : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * !![p, q; (N : ℤ) * l * t, s] = wConjMat N l a b p q t s * wOld N l a b := by
  rw [wOld, wConjMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-((l : ℤ) * p + a * (N * l * t))) * hab
  · linear_combination (-((l : ℤ) * q + a * s)) * hab
  · linear_combination (-((N : ℤ) * l * p + l * b * (N * l * t))) * hab
  · linear_combination (-((N : ℤ) * l * q + l * b * s)) * hab

theorem chiInv_slash_wOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 →
    ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G →
      ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b hab χ G hl hG γ hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have ht' : mat γ 1 0 = (N : ℤ) * l * t := by rw [← Nat.cast_mul]; exact ht
  have hm : mat γ = !![mat γ 0 0, mat γ 0 1; (N : ℤ) * l * t, mat γ 1 1] := by
    rw [← ht']; exact Matrix.eta_fin_two _
  have hd : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * ((N : ℤ) * l * t) = 1 := by
    rw [← ht', ← Matrix.det_fin_two]; exact γ.2
  let δ : SL(2, ℤ) := ⟨wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1),
    wConjMat_det _ _ _ _ _ _ _ _ hab hd⟩
  have hδ : mat δ = wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1) := rfl
  have key : wOld N l a b * mat γ = mat δ * wOld N l a b := by
    rw [hδ, ← wOld_mul_eq N l a b _ _ t _ hab, ← hm]
  have hW : 0 < (wOld N l a b).det := by
    have : (wOld N l a b).det = l := by
      rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * hab
    rw [this]; exact_mod_cast hl
  have h1 : ∀ x : SL(2, ℤ), (mat x).det ≠ 0 := fun x => by simp [mat]
  have hδ0 : δ ∈ Gamma0 (N * l) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨b * mat γ 0 0 + l * b ^ 2 * t - N * mat γ 0 1 - b * mat γ 1 1, ?_⟩
    rw [Nat.cast_mul]; rfl
  have h11 : ((mat δ 1 1 : ℤ) : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
    have : mat δ 1 1 = mat γ 1 1 +
        N * (-a * mat γ 0 0 - a * b * l * t + l * mat γ 0 1 + a * mat γ 1 1) := by
      have e : mat δ 1 1 = -(N : ℤ) * a * mat γ 0 0 - a * b * (N * l * t) + N * l * mat γ 0 1 +
        l * b * mat γ 1 1 := rfl
      rw [e]; linear_combination (mat γ 1 1) * hab
    rw [this, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (h1 γ), key,
    toGL_mul _ _ (h1 δ) hW.ne', SlashAction.slash_mul, ← slash_SL_eq, hG δ hδ0,
    smul_slash_toGL k _ hW, h11]

end GlobalTheory.HeckeFamilyMatrices
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulF_eq_trOld (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) :
    0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) •
      (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  intro hl hB
  let ε : SL(2, ℤ) := ⟨!![(l : ℤ), a; (N : ℤ), b], by rw [Matrix.det_fin_two_of]; linear_combination h⟩
  have hε : ε ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [ε]
  have hεB : B ∣[k] toGL (mat ε) = χ (b : ZMod N) • B := by
    rw [← slash_SL_eq, hB ε hε]; rfl
  let u : ℕ → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]
  have hu : ∀ j, 0 < (u j).det := by
    intro j; simp [u, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hD : (dg (l : ℤ) 1).det ≠ 0 := by
    simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl.ne'
  have key : ∀ j : ℕ, (B ∣[k] toGL (dg l 1)) ∣[k] gaOld N l a b h j =
      χ (b : ZMod N) • (B ∣[k] toGL (u j)) := by
    intro j
    have hg : (mat (gaOld N l a b h j)).det ≠ 0 := by simp [mat]
    have hεd : (mat ε).det ≠ 0 := by simp [mat]
    have hm : dg (l : ℤ) 1 * mat (gaOld N l a b h j) = mat ε * u j := by
      ext i i' <;> fin_cases i <;> fin_cases i' <;>
        simp [dg, gaOld, mat, ε, u, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hg, hm, toGL_mul _ _ hεd (hu j).ne',
      SlashAction.slash_mul, hεB, smul_slash_toGL k _ (hu j)]
  have hsum : trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1) =
      χ (b : ZMod N) • UlF k l B := by
    rw [trOld, add_sub_cancel_left, UlF, hkF, Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    exact (Fin.sum_univ_eq_sum_range (fun j => χ (b : ZMod N) • (B ∣[k] toGL (u j))) l).symm
  have hlb : (l : ZMod N) * (b : ZMod N) = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod N)) h
    push_cast at this
    simpa [ZMod.natCast_self] using this
  rw [hsum, smul_smul, ← map_mul, hlb, map_one, one_smul]

end GlobalTheory.HeckeFamilyMatrices
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem chiInv_slash_dg (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) (hl : 0 < l)
    (hB : ChiInv k N N χ B) : ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  intro γ hγ
  rw [Gamma0_mem] at hγ
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (mat γ 1 0) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  obtain ⟨t, ht⟩ := hdvd
  have hdet : (mat γ).det = 1 := by simp [mat]
  rw [Matrix.det_fin_two] at hdet
  let γ' : SL(2, ℤ) := ⟨!![mat γ 0 0, (l : ℤ) * mat γ 0 1; (N : ℤ) * t, mat γ 1 1], by
    rw [Matrix.det_fin_two_of]; push_cast at ht; rw [ht] at hdet; linear_combination hdet⟩
  have hE : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [γ']
  have hD : (dg l 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of]; omega
  have hDpos : 0 < (dg l 1).det := by simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hγd : (mat γ).det ≠ 0 := by simp [mat]
  have hEd : (mat γ').det ≠ 0 := by simp [mat]
  have hmul : dg l 1 * mat γ = mat γ' * dg l 1 := by
    push_cast at ht
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dg, γ', mat, Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring
  have hs : mat γ' 1 1 = mat γ 1 1 := rfl
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hγd, hmul, toGL_mul _ _ hEd hD,
    SlashAction.slash_mul, ← slash_SL_eq, hB γ' hE, smul_slash_toGL k _ hDpos, hs]

end GlobalTheory.HeckeFamilyMatrices
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

private def toGLQ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℚ).mapMatrix M)
    (by rw [← RingHom.map_det]; simpa using hM)

private lemma toGL_eq_map (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    toGL M = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ M hM) := by
  ext i j
  rw [toGL_val M hM]
  simp [toGLQ, Matrix.GeneralLinearGroup.map]

lemma isCusp_SL2Z_toGL_smul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : IsCusp (toGL M • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  rw [toGL_eq_map M hM]
  exact ⟨toGLQ M hM • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspAll_slash_toGL : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det →
    CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  intro k M G hM hG
  refine ⟨MDifferentiable.slash hG.1 k (toGL M), fun c hc => ?_⟩
  rw [← OnePoint.IsZeroAt.smul_iff]
  exact hG.2 _ (isCusp_SL2Z_toGL_smul M hM.ne' hc)

end GlobalTheory.HeckeFamilyMatrices
end
end

section

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem free_mod_eq {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ)
    (a γ γ' : G) (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) (i j : ℕ)
    (h : γ * a * g ^ i = γ' * a * g ^ j) : i % m = j % m := by
  have key : ∀ (γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ i j : ℕ, i < j → j < m →
      γ * a * g ^ i ≠ γ' * a * g ^ j := by
    intro γ γ' hγ hγ' i j hij hj h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    apply hfree a (d + 1) (by omega) (by omega)
    have e : a * g ^ (d + 1) * a⁻¹ = γ'⁻¹ * γ := by
      have h2 : γ * a * g ^ i = (γ' * a * g ^ (d + 1)) * g ^ i := by
        rw [h, mul_assoc (γ' * a), ← pow_add]
        congr 2
        omega
      have h3 := mul_right_cancel h2
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, ← h3, mul_inv_cancel_right]
    rw [e]
    exact Γ.mul_mem (Γ.inv_mem hγ') hγ
  rw [pow_eq_pow_mod i hg, pow_eq_pow_mod j hg] at h
  rcases lt_trichotomy (i % m) (j % m) with hlt | heq | hlt
  · exact absurd h (key γ γ' hγ hγ' _ _ hlt (Nat.mod_lt _ hm))
  · exact heq
  · exact absurd h.symm (key γ' γ hγ' hγ _ _ hlt (Nat.mod_lt _ hm))

def freeSetoid {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) : Setoid G where
  r x y := ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k
  iseqv :=
    { refl := fun x => ⟨1, Γ.one_mem, 0, by simp⟩
      symm := by
        rintro x y ⟨γ, hγ, k, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k * (m - 1), ?_⟩
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
        have : g ^ k * g ^ (k * (0 + n + 1 - 1)) = 1 := by
          rw [← pow_add]
          have : k + k * (0 + n + 1 - 1) = (0 + n + 1) * k := by
            simp only [zero_add, Nat.add_sub_cancel]
            ring
          rw [this, pow_mul, hg, one_pow]
        rw [mul_assoc, mul_assoc, this, mul_one, inv_mul_cancel_left]
      trans := by
        rintro x y z ⟨γ, hγ, k, rfl⟩ ⟨δ, hδ, l, rfl⟩
        refine ⟨δ * γ, Γ.mul_mem hδ hγ, k + l, ?_⟩
        simp only [pow_add, mul_assoc] }

theorem twInv_apply_pow {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    {Γ : Subgroup G} {g : G} {A : E →ₗ[ℂ] E} {f : G → E} (hf : f ∈ twInv Γ g A) (x : G) (k : ℕ) :
    f (x * g ^ k) = (A ^ k) (f x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, hf.2, ih, pow_succ', Module.End.mul_apply]

theorem finrank_twInv_mul_of_free {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ) (hΓ : Γ.FiniteIndex)
    (hE : FiniteDimensional ℂ E) (hm : 0 < m) (hg : g ^ m = 1) (hA : A ^ m = 1)
    (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) :
    FiniteDimensional ℂ (twInv Γ g A) ∧
      Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  classical
  let s := freeSetoid Γ g m hm hg
  have hs : ∀ x y : G, s.r x y ↔ ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k := fun _ _ => Iff.rfl
  let R := Quotient s
  have hmk : ∀ γ ∈ Γ, ∀ (x : G) (k : ℕ), Quotient.mk s (γ * x * g ^ k) = Quotient.mk s x :=
    fun γ hγ x k => (Quotient.sound (s := s) ((hs _ _).2 ⟨γ, hγ, k, rfl⟩)).symm
  have hout : ∀ x : G, ∃ γ ∈ Γ, ∃ k : ℕ, x = γ * (Quotient.mk s x).out * g ^ k :=
    fun x => (hs _ _).1 (Quotient.mk_out (s := s) x)

  let F : R × Fin m → Quotient (QuotientGroup.rightRel Γ) :=
    fun p => Quotient.mk _ (p.1.out * g ^ (p.2 : ℕ))
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ h
      have h1 := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
      dsimp only at h1
      set γ := d.out * g ^ (j : ℕ) * (c.out * g ^ (i : ℕ))⁻¹ with hγ
      have h2 : 1 * d.out * g ^ (j : ℕ) = γ * c.out * g ^ (i : ℕ) := by
        rw [hγ, mul_assoc _ c.out, inv_mul_cancel_right, one_mul]
      have h3 : d = c := by
        have := congrArg (Quotient.mk s) h2
        rw [hmk 1 Γ.one_mem, hmk γ h1, Quotient.out_eq, Quotient.out_eq] at this
        exact this
      subst h3
      have h4 := free_mod_eq Γ g m hm hg hfree _ _ _ Γ.one_mem h1 _ _ h2
      rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at h4
      rw [Fin.ext h4]
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        obtain ⟨γ, hγ, k, hx⟩ := hout x
        refine ⟨(Quotient.mk s x, ⟨k % m, Nat.mod_lt _ hm⟩), ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.2
        dsimp only
        rw [← pow_eq_pow_mod k hg]
        have : x * ((Quotient.mk s x).out * g ^ k)⁻¹ = γ := by
          rw [mul_inv_eq_iff_eq_mul, ← mul_assoc]
          exact hx
        rw [this]
        exact hγ
  have hcard : Nat.card R * m = Γ.index := by
    have h1 := Nat.card_congr (Equiv.ofBijective F hF)
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)] at h1
    exact h1
  have hR : Finite R := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0, zero_mul] at hcard
    exact hΓ.index_ne_zero hcard.symm
  letI : Fintype R := Fintype.ofFinite R

  let ev : twInv Γ g A →ₗ[ℂ] (R → E) :=
    { toFun := fun f c => (f : G → E) c.out
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    constructor
    · intro f f' h
      apply Subtype.ext
      funext x
      obtain ⟨γ, hγ, k, hx⟩ := hout x
      have h1 : (f : G → E) (Quotient.mk s x).out = (f' : G → E) (Quotient.mk s x).out :=
        congrFun h (Quotient.mk s x)
      rw [hx, twInv_apply_pow f.2, twInv_apply_pow f'.2, f.2.1 γ hγ, f'.2.1 γ hγ, h1]
    · intro φ
      choose γ hγ κ hκ using hout
      have hval : ∀ (x δ : G) (k : ℕ), δ ∈ Γ → x = δ * (Quotient.mk s x).out * g ^ k →
          A ^ κ x = A ^ k := by
        intro x δ k hδ hx
        have := free_mod_eq Γ g m hm hg hfree _ _ _ (hγ x) hδ _ _ ((hκ x).symm.trans hx)
        rw [pow_eq_pow_mod _ hA, this, ← pow_eq_pow_mod _ hA]
      refine ⟨⟨fun x => (A ^ κ x) (φ (Quotient.mk s x)), ?_, ?_⟩, ?_⟩
      · intro δ hδ x
        have e : Quotient.mk s (δ * x) = Quotient.mk s x := by
          simpa using hmk δ hδ x 0
        have := hval (δ * x) (δ * γ x) (κ x) (Γ.mul_mem hδ (hγ x)) (by
          rw [e, mul_assoc, mul_assoc δ, ← mul_assoc (γ x), ← hκ x])
        dsimp only
        rw [this, e]
      · intro x
        have e : Quotient.mk s (x * g) = Quotient.mk s x := by
          simpa using hmk 1 Γ.one_mem x 1
        have := hval (x * g) (γ x) (κ x + 1) (hγ x) (by
          rw [e, pow_succ, ← mul_assoc, ← hκ x])
        dsimp only
        rw [this, e, pow_succ', Module.End.mul_apply]
      · funext c
        have := hval c.out 1 0 Γ.one_mem (by rw [Quotient.out_eq]; simp)
        change (A ^ κ c.out) (φ (Quotient.mk s c.out)) = φ c
        rw [this, Quotient.out_eq]
        simp
  let e := LinearEquiv.ofBijective ev hev
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, ← hcard]
  ring

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end
