module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle035
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroOfAe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x6

open C2x5

variable {k r : ℕ}

lemma herm_ff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by
  rw [ggBlockA k r z hz a b, hzz_real]
  simp only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha hb; simp
  · simp [ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]
  · simp [ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]
  · by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [ha, hab]

lemma E_cast {n : ℕ} (x : Fin n → ℂ) : star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma E_unit {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  rw [← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]

lemma euclid_cs {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (star b ⬝ᵥ a) ≤ (∑ i, Complex.normSq (a i)) * (∑ i, Complex.normSq (b i)) := by
  have h1 : ‖star b ⬝ᵥ a‖ ≤ ∑ i, ‖b i‖ * ‖a i‖ := by
    rw [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b i‖) (fun i => ‖a i‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖star b ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖b i‖ * ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖a i‖ ^ 2) := h2
    _ = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := mul_comm _ _

lemma Hpk_mul_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
  rw [Matrix.mul_apply]
  simp [GBasic.Hpk_eq]

lemma mul_Hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (M * Hpk k r) i j = M i (GBasic.sig k r j) * GBasic.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r j)]
  · rw [GBasic.Hpk_eq, if_pos (GBasic.sig_sig k r j).symm, GBasic.sgn_sig]
  · intro l _ hl
    rw [GBasic.Hpk_eq, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, GBasic.sig_sig])
  · simp

lemma normSq_sgn (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by
  unfold GBasic.sgn
  split_ifs <;> simp

end C2x6

open C2x5 C2x6

theorem gram_block_form : C2.GramBlocks := by
  intro k r z z' hz hz' g hg
  have hH := GBasic.Hpk_herm k r

  have hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    simp only [herm]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    exact herm_ff hz.1 a b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [ggHerm_swap _ hH]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [hpres]
    exact herm_ff hz'.1 a b

theorem majorant_estimate : C2.Majorant := by
  intro k r
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  refine ⟨?_, hsq, fun v => ⟨?_, ?_⟩⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hH, hsq, Matrix.one_mul]
  · simp only [herm]
    rw [E_cast, E_unit _ hH hsq]
  · have hcs := euclid_cs (Hpk k r *ᵥ v) v
    rw [E_unit _ hH hsq] at hcs
    set S := ∑ i, Complex.normSq (v i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h1 : ‖herm (Hpk k r) v v‖ ^ 2 ≤ S ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, sq]
      exact hcs
    have h2 : ‖herm (Hpk k r) v v‖ ≤ S := (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp h1
    exact (Complex.re_le_norm _).trans h2

theorem norm_of_inverse : C2.NormInv := by
  intro k r g hg
  have hsq := GBasic.Hpk_sq k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg

  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hleft
  have hright : g * g⁻¹ = 1 := by
    rw [hinv]
    first
    | exact Matrix.mul_eq_one_comm.mp hleft
    | exact mul_eq_one_comm.mp hleft
  have hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j) := by
    have he : ∀ i j, Complex.normSq (g⁻¹ i j) =
        Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i)) := by
      intro i j
      rw [hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul,
        Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]
      ring
    simp only [he]
    let σ : Equiv.Perm (Fin (2 * r + k + 1)) :=
      Function.Involutive.toPerm _ (GBasic.sig_sig k r)
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv σ _ _ fun j => ?_
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  refine ⟨by simp only [B.gN, hsum], ?_⟩

  set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hcs := euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))
  have h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1 := by
    have := congrFun (congrFun hright i0) i0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [dotProduct] using this
  rw [h1, Complex.normSq_one] at hcs
  have hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j) := fun h =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2 := by
    rw [hgN, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j))
      (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2 := by
    rw [hgN]
    simp only [Complex.star_def, Complex.normSq_conj]
    exact Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hN0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hEq : B.gN g⁻¹ = B.gN g := by simp only [B.gN, hsum]
  rw [hEq] at hA
  have h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2 :=
    hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
      (sq_nonneg _))
  by_contra hlt
  push_neg at hlt
  have : B.gN g ^ 2 * B.gN g ^ 2 < 1 := by
    have h5 : B.gN g ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (B.gN g)]
  linarith

end Formalism.FourierDecayAlt.P
end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section SpacedProductLowerBound

variable {k : ℕ}

def pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) : Fin m :=
  ⟨if c < i.val then c else c - 1, by split_ifs <;> omega⟩

theorem succAbove_pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) :
    (i.succAbove (pidx m i c h)).val = c := by
  rw [succAbove_val]; unfold pidx; simp only; split_ifs <;> omega

theorem pidx_succAbove (m : ℕ) (i : Fin (m + 1)) (b : Fin m) (h : (i.succAbove b).val < m + 1 ∧ (i.succAbove b).val ≠ i.val) :
    pidx m i (i.succAbove b).val h = b := by
  ext; unfold pidx; simp only; rw [succAbove_val]; split_ifs <;> omega

theorem herm_add_smul_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w1 w2 : Fin n → ℂ) (a b : ℂ) :
    herm H v (a • w1 + b • w2) = star a * herm H v w1 + star b * herm H v w2 := by
  unfold herm
  simp [star_add, star_smul, add_dotProduct, smul_dotProduct]

def ViF (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ) : Fin (2 * (m + 1) + k + 1) → ℂ :=
  fun p => if p = esI k (m + 1) i then 1
    else if h : p.val < m + 1 ∧ p.val ≠ i.val then -star (Vc (pidx m i p.val h) (eI k (m + 1) i)) else 0

variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem insertion_vector_zero_off_index (p : Fin (2 * (m + 1) + k + 1)) (hp : m + 1 ≤ p.val) (hne : p ≠ esI k (m + 1) i) : ViF m i Vc p = 0 := by
  unfold ViF; rw [if_neg hne, dite_eq_right (by omega)]

theorem ViF_eI : ViF m i Vc (eI k (m + 1) i) = 0 := by
  unfold ViF
  rw [if_neg, dite_eq_right]
  · simp [eI]
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega

theorem tau_eI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (eI k (m + 1) c) = esI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by left; simp only [eI]; omega)]; simp only [eI, esI]

theorem tau_esI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (esI k (m + 1) c) = eI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by right; simp only [esI]; omega)]; simp only [esI, eI]; omega

end SpacedProductLowerBound

section N2c

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem sg_val' (q : Fin (2 * (m + 1) + k + 1)) : (NFOne.sg k (m + 1) q).val = 2 * (m + 1) + k - q.val := rfl

theorem ViF_alt (l : Fin (2 * (m + 1) + k + 1)) : ViF m i Vc l = 0 ∨ ViF m i Vc (WeylGroupFacts.tau k (m + 1) l) = 0 := by
  by_cases h1 : l = esI k (m + 1) i
  · right; rw [h1, tau_esI]; exact ViF_eI m i Vc
  by_cases h2 : l = eI k (m + 1) i
  · left; rw [h2]; exact ViF_eI m i Vc
  by_cases h3 : m + 1 ≤ l.val
  · left; exact insertion_vector_zero_off_index m i Vc l h3 h1
  · right
    apply insertion_vector_zero_off_index
    · rw [tau_val]; split_ifs <;> omega
    · intro h; apply h2
      have := congrArg (WeylGroupFacts.tau k (m + 1)) h
      rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this

theorem ViF_iso : herm (Hpk k (m + 1)) (ViF m i Vc) (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  rcases ViF_alt m i Vc l with h | h <;> simp [h]

theorem hermitian_insertion_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') :
    herm (Hpk k (m + 1)) z' (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
  · rw [insertion_vector_zero_off_index m i Vc l hW.1 (by intro h; rw [h] at hW; simp [esI] at hW; omega)]; simp
  · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp

theorem ViF_star (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    ViF m i Vc q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]
    unfold ViF; rw [if_pos h]
  · rw [insertion_vector_zero_off_index m i Vc q (by omega) h, if_neg]
    intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

theorem ViF_Vc (hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0) (c' : Fin m) :
    herm (Hpk k (m + 1)) (ViF m i Vc) (Vc c') = 0 := by
  have hs := (i.succAbove c').isLt
  have hsi : (i.succAbove c').val ≠ i.val := fun h' => Fin.succAbove_ne i c' (Fin.ext h')
  rw [herm_expand, Finset.sum_eq_add (eI k (m + 1) i) (esI k (m + 1) (i.succAbove c'))]
  · rw [tau_eI, tau_esI]
    have e1 : ViF m i Vc (esI k (m + 1) i) = 1 := by unfold ViF; rw [if_pos rfl]
    have e2 : ViF m i Vc (eI k (m + 1) (i.succAbove c')) = -star (Vc c' (eI k (m + 1) i)) := by
      unfold ViF
      rw [if_neg (by intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega),
        dite_eq_left ⟨by simp only [eI]; omega, by simpa [eI] using hsi⟩]
      congr 3
      have := pidx_succAbove m i c' ⟨hs, hsi⟩
      simpa [eI] using this
    have e3 : Vc c' (esI k (m + 1) (i.succAbove c')) = 1 := by
      rw [hVs c' _ (by simp [esI]; omega), if_pos (by rw [sg_val']; simp [esI]; omega)]
    rw [e1, e2, e3, sgn_one _ (by simp [eI]; omega), sgn_one _ (by simp [esI]; omega)]
    simp
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega
  · intro l _ hl
    by_cases hS : m + 1 + k < l.val
    · rw [hVs c' l hS, if_neg]
      · simp
      · intro h'; apply hl.2; ext; rw [sg_val'] at h'; simp [esI]; omega
    · by_cases hX : l.val < m + 1
      · rw [insertion_vector_zero_off_index m i Vc (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]
        · simp
        · intro h; apply hl.1
          have := congrArg (WeylGroupFacts.tau k (m + 1)) h
          rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this
      · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
        rw [ht, insertion_vector_zero_off_index m i Vc l (by omega) (by intro h; rw [h] at hS; simp [esI] at hS; omega)]; simp
  · simp
  · simp

end N2c

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section



namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

open Formalism.FourierDecayAlt.ThreeDimData

theorem vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : BeConv) (hIn : Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, hBC2, hBC3, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hc : ContinuousOn (fun g => be z c π σ μW μN (σ g x) v ξ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hBC3 x hx v hv).clm_apply continuousOn_const
  have heq : ∀ hh ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      be z c π σ μW μN (σ (hh * n * g) x) v ξ = Formalism.QuantumDeterminants.psi k r z c n • π hh (be z c π σ μW μN (σ g x) v ξ) := by
    intro hh hhW n hn g hg
    have hhn : hh * n ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhW.1 hn.1
    have hm : σ (hh * n * g) = (σ (hh * n)).comp (σ g) := TranslationBesselVanishing.sigma_mul hσ hhn hg
    rw [hm, ContinuousLinearMap.comp_apply,
      hBC2 v hv hh hhW n hn (σ g x) (TranslationBesselVanishing.smooth_translate hσ hx hg)]
    rfl
  have h0 := aez hW hN hG hq (fun g => be z c π σ μW μN (σ g x) v ξ) hc heq (hl ξ) 1 Formalism.QuantumDeterminants.WeylGroupFacts.uh_one
  simpa [sigma_one hσ] using h0

theorem zeroCaseDD_of (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp

theorem zeroCase_of (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCase := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  have hA := zeroCaseDD_of hBC hNI hSch hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hDD
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv

  have hB : ∀ u ∈ DDsp σ w0, be z c π σ μW μN u v = 0 := by
    intro u hu
    have h1 : be z c π σ μW μN v u = 0 := hA u hu v hvs
    have h2 := (hBC4 u hu v (Or.inr hv)).2
    rw [h1] at h2
    have h3 := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_adjoint, map_zero] at h3

  have hw0n : ‖w0‖ = 1 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    exact hn1
  have hw0ne : w0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw0n; exact zero_ne_one hw0n
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hdeg : PI.BesselPeriodGGP.fdegH μG σ w0 = d := DDSmoothness.fdeg_eq hd hSd hw0ne
  have hw0DD : w0 ∈ DDsp σ w0 := by
    refine Submodule.subset_span ⟨1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, ?_⟩
    simp [sigma_one hσ]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 w0 hw0DD
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hC : ∀ ξ : Wp, ⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ = 0 := by
    intro ξ
    obtain ⟨hNv, him, hre⟩ := hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS w0 hw0s v (Or.inr hv) ξ
    have hL : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g w0) v ξ) = 0 := by
      unfold PI.BesselPeriodGGP.l2SG
      refine (lintegral_congr_ae (hae.mono fun g hg => ?_)).trans lintegral_zero
      have hgD : σ (Matrix.of g) w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨Matrix.of g, hg, rfl⟩
      simp [hB _ hgD]
    rw [hL, hdeg, hw0n] at hNv
    have h0 : 1 ^ 2 * (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re / d ≤ 0 := ENNReal.ofReal_eq_zero.mp hNv.symm
    have hre0 : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re = 0 := by
      have : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re ≤ 0 := by
        rw [one_pow, one_mul] at h0
        exact (div_nonpos_iff.mp h0).elim (fun h => absurd h.2 (not_le.mpr hd)) (fun h => h.1)
      linarith
    exact Complex.ext hre0 him
  have hvv : be z c π σ μW μN v v = 0 := by
    have hlin : (be z c π σ μW μN v v : Wp →ₗ[ℂ] Wp) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro ξ
      rw [← inner_conj_symm]
      simp [hC ξ]
    ext ξ
    have := LinearMap.congr_fun hlin ξ
    simpa using this

  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inr hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) ξ).1, hvv]
  simp

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P
end
end
