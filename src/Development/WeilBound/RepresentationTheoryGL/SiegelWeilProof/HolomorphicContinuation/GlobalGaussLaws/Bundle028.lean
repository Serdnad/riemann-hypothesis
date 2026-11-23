module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle026

@[expose] public section

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

private theorem fromBlocks_unitary_and_conj_JJ_eq {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Xᴴ * X + Yᴴ * Y = 1)
    (h2 : Xᴴ * Y = Yᴴ * X) :
    (fromBlocks X (-Y) Y X)ᴴ * fromBlocks X (-Y) Y X = 1 ∧
      (fromBlocks X (-Y) Y X)ᴴ * JJ n * fromBlocks X (-Y) Y X = JJ n := by
  constructor
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    simp [h2]
    rw [h1, add_comm, h1, fromBlocks_one]
  · rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [h2]
    exact ⟨by rw [add_comm, h1], by rw [← neg_add, h1]⟩

private theorem exists_normalizing_factor_of_left_inverse {n : ℕ} (X Y A B : Matrix (Fin n) (Fin n) ℂ) (h : A * X + B * Y = 1) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1 := by
  classical
  set M := Xᴴ * X + Yᴴ * Y with hM
  have hpsd : M.PosSemidef :=
    (posSemidef_conjTranspose_mul_self X).add (posSemidef_conjTranspose_mul_self Y)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hq : star v ⬝ᵥ M *ᵥ v = 0 := by rw [hMv, dotProduct_zero]
    simp_rw [hM, add_mulVec, dotProduct_add, ← mulVec_mulVec, dotProduct_mulVec _ _ (X *ᵥ v),
      dotProduct_mulVec _ _ (Y *ᵥ v), vecMul_conjTranspose, star_star] at hq
    have h2 := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg _)
      (dotProduct_star_self_nonneg _)).mp hq
    have hx := dotProduct_star_self_eq_zero.mp h2.1
    have hy := dotProduct_star_self_eq_zero.mp h2.2
    apply hv
    rw [← one_mulVec v, ← h, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, mulVec_zero,
      mulVec_zero, add_zero]
  open scoped MatrixOrder in
  obtain ⟨S, hSS, hSa⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * S = M ∧ Sᴴ = S :=
    ⟨CFC.sqrt M, CFC.sqrt_mul_sqrt_self M hpsd.nonneg, (CFC.sqrt_nonneg M).isSelfAdjoint⟩
  have hS : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    rw [← hSS, det_mul, h0, zero_mul]
  refine ⟨S⁻¹, ?_⟩
  simp only [conjTranspose_mul, conjTranspose_nonsing_inv, hSa]
  calc S⁻¹ * Xᴴ * (X * S⁻¹) + S⁻¹ * Yᴴ * (Y * S⁻¹) = S⁻¹ * (S * S) * S⁻¹ := by
        rw [hSS, hM]; noncomm_ring
    _ = 1 := by rw [← mul_assoc, nonsing_inv_mul _ hS, one_mul, mul_nonsing_inv _ hS]

private theorem exists_mul_lower_zero_and_inK_of_normalized (n : ℕ) (y : GR n) (X Y C D R : Matrix (Fin n) (Fin n) ℂ)
    (hb : C * X + D * Y = 0) (hR : (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1)
    (hiso' : (X * R)ᴴ * (Y * R) = (Y * R)ᴴ * (X * R)) (hC : toBlocks₂₁ (mR y) = C)
    (hD : toBlocks₂₂ (mR y) = D) :
    ∃ (p : ↥(GR n)) (k : ↥(GR n)), y = p * k ∧ toBlocks₂₁ (mR p) = 0 ∧ InK (mR k) := by
  obtain ⟨hU, hS⟩ := fromBlocks_unitary_and_conj_JJ_eq (X * R) (Y * R) hR hiso'
  generalize hkv : fromBlocks (X * R) (-(Y * R)) (Y * R) (X * R) = kv at hU hS
  have hU' : kv * kvᴴ = 1 := mul_eq_one_comm.mp hU
  have hu : (⟨kv, kvᴴ, hU', hU⟩ : GL (Fin n ⊕ Fin n) ℂ) ∈ GR n := hS
  refine ⟨y * ⟨_, hu⟩, (⟨_, hu⟩ : GR n)⁻¹, (mul_inv_cancel_right y _).symm, ?_, ?_⟩
  · have hm : mR (y * ⟨_, hu⟩) = mR y * kv := rfl
    rw [hm, ← hkv, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply, toBlocks_fromBlocks₂₁, hC, hD,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hb, Matrix.zero_mul]
  · refine ⟨(⟨_, hu⟩ : GR n)⁻¹.2, ?_⟩
    have hm : mR (⟨_, hu⟩ : GR n)⁻¹ = kvᴴ := rfl
    rw [hm, conjTranspose_conjTranspose]
    exact hU'

theorem iwaGR : IwaGR := by
  intro n y
  classical
  have hprod : mR y * mR y⁻¹ = 1 := by simp [mR]
  have hG : InG (mR y⁻¹) := (y⁻¹).2
  have hiso : (toBlocks₁₁ (mR y⁻¹))ᴴ * toBlocks₂₁ (mR y⁻¹) =
      (toBlocks₂₁ (mR y⁻¹))ᴴ * toBlocks₁₁ (mR y⁻¹) := by
    have h := congrArg toBlocks₁₁ hG
    rw [← fromBlocks_toBlocks (mR y⁻¹), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at h
    simp at h
    exact (neg_add_eq_zero.mp h).symm
  have hb := hprod
  rw [← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR y⁻¹), fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at hb
  obtain ⟨R, hR⟩ := exists_normalizing_factor_of_left_inverse _ _ _ _ hb.1
  have hiso' : (toBlocks₁₁ (mR y⁻¹) * R)ᴴ * (toBlocks₂₁ (mR y⁻¹) * R) =
      (toBlocks₂₁ (mR y⁻¹) * R)ᴴ * (toBlocks₁₁ (mR y⁻¹) * R) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ _ R, hiso, Matrix.mul_assoc]
  exact exists_mul_lower_zero_and_inK_of_normalized n y _ _ _ _ R hb.2.2.1 hR hiso' rfl rfl

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem cocycleZ : CocycleZ := by
  intro n e p q y y' Z hZ
  have hg := inG_mR y'
  have hnonzero {v : Fin n → ℂ} (hv : v ≠ 0) : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) ≠ 0 := by
    intro hz
    have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
    rw [smul_mulVec, dotProduct_smul, hz, smul_zero] at hpos
    exact (lt_irrefl (0 : ℂ)) hpos
  have hden (X : Matrix (Fin n) (Fin n) ℂ) :
      ¬ IsUnit ((mR y').toBlocks₂₁ * X + (mR y').toBlocks₂₂).det →
        ∃ v : Fin n → ℂ, v ≠ 0 ∧ star v ⬝ᵥ ((Xᴴ - X) *ᵥ v) = 0 := by
    rw [isUnit_iff_ne_zero, not_not]
    intro hdet
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨v, hv, ?_⟩
    rw [← identG hg X X, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero,
      dotProduct_sub, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have hD : IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂).det := by
    by_contra h
    obtain ⟨v, hv, hz⟩ := hden Z h
    apply hnonzero hv
    rw [← neg_sub, neg_mulVec, dotProduct_neg, hz, neg_zero]
  have hDh : IsUnit ((mR y').toBlocks₂₁ * Zᴴ + (mR y').toBlocks₂₂).det := by
    by_contra h
    obtain ⟨v, hv, hz⟩ := hden Zᴴ h
    exact hnonzero hv (by simpa only [conjTranspose_conjTranspose] using hz)
  have hW : IsSiegel (actZ y' Z) := by
    have hid := identG hg Z Z
    unfold IsSiegel actZ
    unfold IsSiegel at hZ
    set N := (mR y').toBlocks₁₁ * Z + (mR y').toBlocks₁₂
    set M := (mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂
    have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hD
    have hMM' : ∀ X : Matrix (Fin n) (Fin n) ℂ, (M⁻¹)ᴴ * (Mᴴ * X) = X := by
      intro X
      rw [← Matrix.mul_assoc, ← conjTranspose_mul, hMM, conjTranspose_one, Matrix.one_mul]
    have hZZ : Mᴴ * N - Nᴴ * M = Z - Zᴴ := by
      rw [← neg_sub, hid, neg_sub]
    have key : -(Complex.I / 2) • (N * M⁻¹ - (N * M⁻¹)ᴴ) =
        (M⁻¹)ᴴ * (-(Complex.I / 2) • (Z - Zᴴ)) * M⁻¹ := by
      rw [← hZZ, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc, hMM, Matrix.mul_one, hMM']
    rw [key]
    exact hZ.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hD)))
  have e1 : actZ y' Z * (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Z + toBlocks₁₂ (mR y') := by
    unfold actZ
    exact Matrix.nonsing_inv_mul_cancel_right _ _ hD
  have e2 : (actZ y' Z)ᴴ * (toBlocks₂₁ (mR y') * Zᴴ + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Zᴴ + toBlocks₁₂ (mR y') := by
    have hid := identG hg Z Zᴴ
    rw [sub_self] at hid
    have hDstar : IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂)ᴴ.det := by
      rw [det_conjTranspose]
      exact hD.star
    unfold actZ
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, sub_eq_zero.mp hid,
      nonsing_inv_mul_cancel_left _ _ hDstar]
  obtain ⟨n1, n2⟩ := num_den_mul (mR y) (mR y') Z _ e1
  obtain ⟨-, n3⟩ := num_den_mul (mR y) (mR y') Zᴴ _ e2
  refine ⟨hD, hDh, hW, ?_, ?_⟩
  · show ((mR (y * y')).toBlocks₁₁ * Z + (mR (y * y')).toBlocks₁₂) *
        ((mR (y * y')).toBlocks₂₁ * Z + (mR (y * y')).toBlocks₂₂)⁻¹ = actZ y (actZ y' Z)
    rw [mR_mul, n1, n2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')),
      Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]
    rfl
  · simp only [jF]
    rw [mR_mul, n2, n3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow, mul_zpow]
    ring

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem actZ_K {k : GR n} (hk : InK (mR k)) : actZ k (Complex.I • 1) = Complex.I • 1 := by
  obtain ⟨hC, hD⟩ := inK_blocks hk
  have hI : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold IsSiegel
    have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
      rw [Complex.star_def, Complex.conj_I]
      linear_combination (-1 : ℂ) * Complex.I_sq
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
    exact Matrix.PosDef.one
  have hu := (cocycleZ n 0 0 0 k k _ hI).1
  have key : toBlocks₁₁ (mR k) * (Complex.I • 1) + toBlocks₁₂ (mR k) =
      (Complex.I • 1) * (toBlocks₂₁ (mR k) * (Complex.I • 1) + toBlocks₂₂ (mR k)) := by
    rw [hC, hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_neg,
      smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
    abel
  unfold actZ
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

def mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, hG⟩

theorem mR_mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : mR (mkGR M hM hG) = M := rfl

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb]

theorem inG_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mM a) := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold InG mM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  simp [nU]

theorem det_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : (mM a).det ≠ 0 := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold mM
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (ha.mul (Matrix.isUnit_nonsing_inv_det _ ha')).ne_zero

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end
