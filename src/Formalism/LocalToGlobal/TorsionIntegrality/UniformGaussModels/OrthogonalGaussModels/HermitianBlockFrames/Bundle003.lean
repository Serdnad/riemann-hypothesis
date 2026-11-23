module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.ExistsUnitVec
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

@[expose] public section

section

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Γp (Γ : Matrix ι ι K) (a : ι → K) : Matrix ι ι K := Γ - vecMulVec (Γ *ᵥ a) (S.cv a ᵥ* Γ)

def proj (Γ : Matrix ι ι K) (a y : ι → K) : ι → K := y - S.hf Γ a y • a

theorem hf_eq_vecMul (Γ : Matrix ι ι K) (x y : ι → K) : S.hf Γ x y = (S.cv x ᵥ* Γ) ⬝ᵥ y :=
  dotProduct_mulVec _ _ _

private theorem vecMulVec_mulVec_hermitian_block_frames (u v y : ι → K) : vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem Γp_mulVec (Γ : Matrix ι ι K) (a y : ι → K) :
    S.Γp Γ a *ᵥ y = Γ *ᵥ y - S.hf Γ a y • (Γ *ᵥ a) := by
  rw [Γp, sub_mulVec, vecMulVec_mulVec_hermitian_block_frames, hf_eq_vecMul]

private theorem vecMul_vecMulVec' (u v x : ι → K) : x ᵥ* vecMulVec u v = (x ⬝ᵥ u) • v := by
  ext j
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecMul_Γp (Γ : Matrix ι ι K) (a x : ι → K) :
    S.cv x ᵥ* S.Γp Γ a = S.cv x ᵥ* Γ - S.hf Γ x a • (S.cv a ᵥ* Γ) := by
  rw [Γp, vecMul_sub, vecMul_vecMulVec']
  rfl

theorem hf_Γp (Γ : Matrix ι ι K) (a x y : ι → K) :
    S.hf (S.Γp Γ a) x y = S.hf Γ x y - S.hf Γ a y * S.hf Γ x a := by
  show S.cv x ⬝ᵥ (S.Γp Γ a *ᵥ y) = _
  rw [Γp_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rfl

variable {Γ : Matrix ι ι K} {a : ι → K}

theorem Γp_mulVec_self (haa : S.hf Γ a a = 1) : S.Γp Γ a *ᵥ a = 0 := by
  rw [Γp_mulVec, haa, one_smul, sub_self]

theorem vecMul_Γp_self (haa : S.hf Γ a a = 1) : S.cv a ᵥ* S.Γp Γ a = 0 := by
  rw [vecMul_Γp, haa, one_smul, sub_self]

theorem IntM_Γp (hΓ : S.IntM Γ) (ha : S.IntV a) : S.IntM (S.Γp Γ a) := by
  intro i j
  have h1 : (Γ *ᵥ a) i ∈ S.O := S.IntV_mulVec hΓ ha i
  have h2 : (S.cv a ᵥ* Γ) j ∈ S.O := by
    simp only [vecMul, dotProduct]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.IntV_cv ha k) (hΓ k j)
  simp only [Γp, Matrix.sub_apply, vecMulVec_apply]
  exact S.O.sub_mem (hΓ i j) (S.O.mul_mem h1 h2)

theorem Herm_Γp (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) : S.Herm (S.Γp Γ a) := by
  intro i j
  simp only [Γp, Matrix.sub_apply, vecMulVec_apply, map_sub, map_mul, hH i j, S.σ_mulVec hH,
    S.σ_vecMul hH ha]
  ring

theorem mulVec_proj (Γ : Matrix ι ι K) (a y : ι → K) : Γ *ᵥ S.proj Γ a y = S.Γp Γ a *ᵥ y := by
  rw [proj, mulVec_sub, mulVec_smul, Γp_mulVec]

theorem IntV_proj (hΓ : S.IntM Γ) (ha : S.IntV a) {y : ι → K} (hy : S.IntV y) : S.IntV (S.proj Γ a y) :=
  S.IntV_sub hy (S.IntV_smul (S.hf_mem hΓ ha hy) ha)

private theorem sub_smul_vecMul (x b : ι → K) (c : K) (M : Matrix ι ι K) :
    (x - c • b) ᵥ* M = x ᵥ* M - c • (b ᵥ* M) := by
  ext j
  simp only [vecMul, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

private theorem hf_proj_right_eq_hf_Γp (Γ : Matrix ι ι K) (a x y : ι → K) :
    S.hf Γ x (S.proj Γ a y) = S.hf (S.Γp Γ a) x y := by
  show S.cv x ⬝ᵥ (Γ *ᵥ S.proj Γ a y) = S.cv x ⬝ᵥ (S.Γp Γ a *ᵥ y)
  rw [mulVec_proj]

theorem hf_proj_proj (haa : S.hf Γ a a = 1) (x y : ι → K) :
    S.hf Γ (S.proj Γ a x) (S.proj Γ a y) = S.hf (S.Γp Γ a) x y := by
  rw [hf_proj_right_eq_hf_Γp, hf_eq_vecMul, hf_eq_vecMul, proj, cv_sub, cv_smul,
    sub_smul_vecMul, S.vecMul_Γp_self haa, smul_zero, sub_zero]

theorem hf_self_proj (haa : S.hf Γ a a = 1) (y : ι → K) : S.hf Γ a (S.proj Γ a y) = 0 := by
  rw [hf_proj_right_eq_hf_Γp, hf_Γp, haa, mul_one, sub_self]

theorem hf_proj_self (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) (haa : S.hf Γ a a = 1) {y : ι → K}
    (hy : S.IntV y) : S.hf Γ (S.proj Γ a y) a = 0 := by
  rw [S.hf_swap hΓ hH ha (S.IntV_proj hΓ ha hy), S.hf_self_proj haa, map_zero]

theorem vecMul_proj (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) {y : ι → K} (hy : S.IntV y) :
    S.cv (S.proj Γ a y) ᵥ* Γ = S.cv y ᵥ* S.Γp Γ a := by
  rw [proj, cv_sub, cv_smul, sub_smul_vecMul, vecMul_Γp, S.hf_swap hΓ hH ha hy]

theorem UM_Γp (hΓ : S.IntM Γ) (hH : S.Herm Γ) (hU : S.UM Γ) (ha : S.IntV a) (haa : S.hf Γ a a = 1) :
    S.UM (S.Γp Γ a) := by
  intro x hx hPx
  have hz := S.IntV_proj hΓ ha hx
  have hΓz : ∀ i, S.NU ((Γ *ᵥ S.proj Γ a x) i) := by
    intro i
    rw [mulVec_proj]
    exact hPx i
  obtain ⟨z, hz', hzz⟩ := hU _ hz hΓz
  refine ⟨z, hz', ?_⟩
  have h0 : S.hf Γ a z = 0 := by
    have h1 : S.hf Γ a (S.proj Γ a x) = S.p * S.hf Γ a z := by
      show S.cv a ⬝ᵥ (Γ *ᵥ S.proj Γ a x) = S.p * (S.cv a ⬝ᵥ (Γ *ᵥ z))
      rw [hzz, dotProduct_smul, smul_eq_mul]
    rw [S.hf_self_proj haa] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left S.hp0
  rw [← S.mulVec_proj Γ a x, hzz, Γp_mulVec, h0, zero_smul, sub_zero]

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

variable {l : ℕ} [Fact l.Prime]

def OO (dK : ℕ) (δ : MaximalUnramifiedExtension l) (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : Subring (MaximalUnramifiedExtension l) where
  carrier := {x | ∃ a b : ℤ_[l], x = ψ l a + δ * ψ l b}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c - dK * (b * e), a * e + b * c, ?_⟩
    simp only [map_add (f := _), map_sub, map_mul, map_natCast]
    linear_combination (ψ l b * ψ l e) * hδ
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by simp only [map_add (f := _)]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by simp only [map_neg]; ring⟩

theorem norm_add_le_Kur (x y : MaximalUnramifiedExtension l) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  show ‖(x : ℂ_[l]) + y‖ ≤ max ‖(x : ℂ_[l])‖ ‖(y : ℂ_[l])‖
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_δ_le {dK : ℕ} {δ : MaximalUnramifiedExtension l} (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : ‖δ‖ ≤ 1 := by
  have h : ‖δ‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hδ, norm_neg, norm_natCast_Kur]
    have : ((dK : ℤ_[l]) : ℚ_[l]) = (dK : ℚ_[l]) := by push_cast; rfl
    rw [← this]; exact PadicInt.norm_le_one _
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

theorem norm_le_one_of_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} {x : MaximalUnramifiedExtension l}
    (hx : x ∈ OO dK δ hδ) : ‖x‖ ≤ 1 := by
  obtain ⟨a, b, rfl⟩ := hx
  refine (norm_add_le_Kur _ _).trans (max_le (norm_ψ_le l a) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (norm_δ_le hδ) (norm_nonneg _) (norm_ψ_le l b)

theorem ratCast_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} (q : ℚ) (hq : padicNorm l q ≤ 1) :
    (q : MaximalUnramifiedExtension l) ∈ OO dK δ hδ := by
  have hq' : ‖(q : ℚ_[l])‖ ≤ 1 := by rw [Padic.eq_padicNorm]; exact_mod_cast hq
  refine ⟨⟨(q : ℚ_[l]), hq'⟩, 0, ?_⟩
  simp only [map_zero, mul_zero, add_zero]
  show (q : MaximalUnramifiedExtension l) = φ l (q : ℚ_[l])
  rw [map_ratCast]

theorem δ_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} : δ ∈ OO dK δ hδ := ⟨0, 1, by simp⟩

theorem norm_sq_unit {dK : ℕ} (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (a b : ℤ_[l])
    (h : ‖a‖ = 1 ∨ ‖b‖ = 1) : ‖a * a + dK * (b * b)‖ = 1 := by
  rw [norm_eq_one_iff]
  intro h0
  rw [map_add (f := _), map_mul, map_mul, map_mul, toZMod_natCast] at h0
  by_cases hB : PadicInt.toZMod b = 0
  · have hA : PadicInt.toZMod a = 0 := by
      rw [hB, mul_zero, mul_zero, add_zero] at h0; exact mul_self_eq_zero.mp h0
    rcases h with h | h
    · exact (norm_eq_one_iff l a).mp h hA
    · exact (norm_eq_one_iff l b).mp h hB
  · exact hin ⟨PadicInt.toZMod a / PadicInt.toZMod b, by field_simp; linear_combination h0⟩

def setup (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l))
    (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (δ : MaximalUnramifiedExtension l) (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) (hσδ : σ δ = -δ) :
    JSetup (MaximalUnramifiedExtension l) where
  σ := σ
  O := OO dK δ hδ
  p := (l : MaximalUnramifiedExtension l)
  hp0 := by
    intro h
    have := norm_l_Kur l
    rw [h, norm_zero] at this
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    exact (inv_pos.mpr hl).ne this
  hpO := ⟨l, 0, by simp⟩
  hσp := map_natCast σ l
  hσO := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a, -b, by rw [map_add (f := _), map_mul, σ_ψ l σ hσ, σ_ψ l σ hσ, hσδ, map_neg]; ring⟩
  hσσ := by
    rintro _ ⟨a, b, rfl⟩
    simp only [map_add (f := _), map_mul, σ_ψ l σ hσ, hσδ, map_neg, neg_neg]
  hinv := by
    rintro _ ⟨a, b, rfl⟩ hnu
    have hab : ‖a‖ = 1 ∨ ‖b‖ = 1 := by
      by_contra hc
      push Not at hc
      apply hnu
      obtain ⟨a', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (lt_of_le_of_ne (PadicInt.norm_le_one a) hc.1)
      obtain ⟨b', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd b).mp (lt_of_le_of_ne (PadicInt.norm_le_one b) hc.2)
      exact ⟨ψ l a' + δ * ψ l b', ⟨a', b', rfl⟩, by simp only [map_mul, map_natCast]; ring⟩
    obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr (norm_sq_unit hin a b hab)
    refine ⟨a * ↑u⁻¹, -(b * ↑u⁻¹), ?_⟩
    have hNu : ψ l (a * a + dK * (b * b)) * ψ l ↑u⁻¹ = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hmul : (ψ l a + δ * ψ l b) * (ψ l (a * ↑u⁻¹) + δ * ψ l (-(b * ↑u⁻¹))) = 1 := by
      simp only [map_mul, map_neg, map_add (f := _), map_natCast] at hNu ⊢
      linear_combination hNu + (-(ψ l b * ψ l b * ψ l ↑u⁻¹)) * hδ
    exact inv_eq_of_mul_eq_one_right hmul
  hone := by
    rintro ⟨y, hy, h⟩
    have h1 := congrArg norm h
    rw [norm_one, norm_mul, norm_l_Kur] at h1
    have hy1 := norm_le_one_of_mem hy
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have : (l : ℝ)⁻¹ * ‖y‖ ≤ (l : ℝ)⁻¹ := mul_le_of_le_one_right (by positivity) hy1
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
    linarith
  htwo := by
    have h2 : ‖(2 : ℤ_[l])‖ = 1 := by
      rw [norm_eq_one_iff, map_ofNat]; exact odd_l l h5
    obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr h2
    refine ⟨↑u⁻¹, 0, ?_⟩
    have : (2 : MaximalUnramifiedExtension l) * ψ l ↑u⁻¹ = 1 := by
      rw [← map_ofNat (ψ l) 2, ← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_zero, mul_zero, add_zero]
    exact inv_eq_of_mul_eq_one_right this
  h2 := two_ne_zero
  hnorm := by
    rintro _ ⟨a, b, rfl⟩ hσu hnu
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at hδ
      exact hld (hδ ▸ dvd_zero l)
    have hb : ψ l b = 0 := by
      rw [map_add (f := _), map_mul, σ_ψ l σ hσ, σ_ψ l σ hσ, hσδ] at hσu
      have h2δ : (2 * δ) * ψ l b = 0 := by linear_combination -hσu
      rcases mul_eq_zero.mp h2δ with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hδ0)
      · exact h
    have ha : ‖a‖ = 1 := by
      by_contra hc
      apply hnu
      obtain ⟨a', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (lt_of_le_of_ne (PadicInt.norm_le_one a) hc)
      exact ⟨ψ l a', ⟨a', 0, by simp⟩, by rw [hb]; simp [map_mul]⟩
    obtain ⟨x, y, hxy⟩ := exists_norm l h5 dK hld a ha
    refine ⟨ψ l x + δ * ψ l y, ⟨x, y, rfl⟩, ?_⟩
    rw [hb, mul_zero, add_zero, ← hxy]
    simp only [map_add (f := _), map_mul, σ_ψ l σ hσ, hσδ, map_natCast]
    linear_combination (-(ψ l y * ψ l y)) * hδ
  hsep := by
    intro x hx hx0
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
    refine ⟨N, ?_⟩
    rintro ⟨y, hy, rfl⟩
    have hy1 := norm_le_one_of_mem hy
    rw [norm_mul, norm_pow, norm_l_Kur] at hpos
    rw [norm_mul, norm_pow, norm_l_Kur] at hN
    have : (l : ℝ)⁻¹ ^ N * ‖y‖ ≤ (l : ℝ)⁻¹ ^ N := mul_le_of_le_one_right (by positivity) hy1
    linarith

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem sq_conj (d : ℕ) : conj (sq d) = -sq d := by
  simp [sq, Complex.conj_ofReal]

theorem sq_mul_sq (d : ℕ) : sq d * sq d = -(d : ℂ) := by
  rw [← pow_two]
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [sq, mul_pow, h, Complex.I_sq]; ring

def Kc (d : ℕ) (hd : 0 < d) : Subfield ℂ where
  carrier := {z | ∃ q₁ q₂ : ℚ, z = q₁ + q₂ * sq d}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    have := sq_mul_sq d
    push_cast
    linear_combination (b * e : ℂ) * this
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases h0 : (a : ℂ) + b * sq d = 0
    · exact ⟨0, 0, by rw [h0]; simp⟩
    have hn : (a ^ 2 + d * b ^ 2 : ℚ) ≠ 0 := by
      intro hn
      have hb : b = 0 := by
        by_contra hb
        have : (0 : ℚ) < a ^ 2 + d * b ^ 2 := by
          have : (0 : ℚ) < d := by exact_mod_cast hd
          positivity
        linarith
      have ha : a = 0 := by subst hb; simpa using hn
      apply h0; subst ha; subst hb; simp
    refine ⟨a / (a ^ 2 + d * b ^ 2), -b / (a ^ 2 + d * b ^ 2), ?_⟩
    have hn' : ((a ^ 2 + d * b ^ 2 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hn
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    have := sq_mul_sq d
    push_cast at hn' ⊢
    field_simp
    linear_combination (-(b:ℂ) ^ 2) * this

theorem conj_mem_Kc {d : ℕ} {hd : 0 < d} {z : ℂ} (hz : z ∈ Kc d hd) : conj z ∈ Kc d hd := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨a, -b, by simp [sq_conj]⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem delta_mem (l : ℕ) [Fact l.Prime] (dK : ℕ) (hd : dK.Prime) (hd4 : dK % 4 = 3) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) : ι (sq dK) ∈ MaximalUnramifiedExtension l := by
  haveI : Fact dK.Prime := ⟨hd⟩
  have hd2 : ringChar (ZMod dK) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hζ : IsPrimitiveRoot (ι (Complex.exp (2 * ↑Real.pi * Complex.I / ↑dK))) dK :=
    (Complex.isPrimitiveRoot_exp dK hd.ne_zero).map_of_injective ι.injective
  set χ := (quadraticChar (ZMod dK)).ringHomComp (Int.castRingHom ℂ_[l]) with hχ
  set ψ := AddChar.zmodChar dK hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root dK hζ
  have hχ1 : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := MulChar.ne_one_iff.1 (quadraticChar_ne_one hd2)
    refine MulChar.ne_one_iff.2 ⟨a, fun h => ha ?_⟩
    rw [hχ, MulChar.ringHomComp_apply, eq_intCast] at h
    exact_mod_cast h
  have hG : gaussSum χ ψ ^ 2 = -(dK : ℂ_[l]) := by
    rw [gaussSum_sq hχ1 ((quadraticChar_isQuadratic (ZMod dK)).comp _) hψ, ZMod.card, hχ,
      MulChar.ringHomComp_apply, quadraticChar_neg_one hd2, ZMod.card, ZMod.χ₄_nat_three_mod_four hd4]
    simp
  have hx : ι (sq dK) ^ 2 = -(dK : ℂ_[l]) := by
    rw [← map_pow]
    have h2 : sq dK ^ 2 = -(dK : ℂ) := by
      unfold sq
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    rw [h2, map_neg, map_natCast]
  have hmem : gaussSum χ ψ ∈ MaximalUnramifiedExtension l := by
    unfold gaussSum
    refine Subfield.sum_mem _ (fun a _ => Subfield.mul_mem _ ?_ ?_)
    · rw [hχ, MulChar.ringHomComp_apply, eq_intCast]
      exact intCast_mem _ _
    · rw [hψdef, AddChar.zmodChar_apply]
      unfold MaximalUnramifiedExtension
      apply Subfield.le_topologicalClosure
      apply Subfield.subset_closure
      refine ⟨dK, hd.pos, hld, ?_⟩
      rw [← pow_mul, mul_comm a.val dK, pow_mul, hζ.pow_eq_one, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hG.symm) with h | h
  · rw [h]
    exact hmem
  · rw [h]
    exact Subfield.neg_mem _ hmem

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end
