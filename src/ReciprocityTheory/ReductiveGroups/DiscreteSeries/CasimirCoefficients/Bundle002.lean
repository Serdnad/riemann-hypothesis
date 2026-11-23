module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LogL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcA_exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ))

lemma exists_local_matrix_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  have hf := lcA_exp_strict (n := n)
  refine ⟨hf.localInverse _ _ _, ?_, ?_, hf.eventually_left_inverse⟩
  · have h1 := hf.localInverse_continuousAt.tendsto
    have h2 := hf.localInverse_apply_image
    rw [NormedSpace.exp_zero] at h1 h2
    rwa [h2] at h1
  · have h := hf.eventually_right_inverse
    rwa [NormedSpace.exp_zero] at h

lemma continuous_matrix_exp_alt :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | exact exp_continuous

end LogL

lemma lcA_exists_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  first
  | exact exists_local_matrix_log
  | exact exists_local_matrix_log (n := n)

lemma lcA_exists_klog (ε : Fin n → Bool) : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ ∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      k ∈ Kset ε → inK ε (ℓ k) ∧ NormedSpace.exp (ℓ k) = k := by
  obtain ⟨L, hL1, hL2, hL3⟩ := lcA_exists_log (n := n)
  refine ⟨L, hL1, ?_⟩
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hA : Tendsto (fun k => (L k)ᴴ) (𝓝 1) (𝓝 0) := by
    have h := hL1.star
    rw [star_zero] at h
    exact h
  have hB : Tendsto (fun k => -(L k)) (𝓝 1) (𝓝 0) := by
    have h := hL1.neg
    rw [neg_zero] at h
    exact h
  have hC : Tendsto (fun k => Jm ε * L k * Jm ε) (𝓝 1) (𝓝 0) := by
    have h := (hL1.const_mul (Jm ε)).mul_const (Jm ε)
    rw [mul_zero, zero_mul] at h
    exact h
  filter_upwards [hL2, hA.eventually hL3, hB.eventually hL3, hC.eventually hL3] with k h2 hA' hB' hC' hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkk : kᴴ * k = 1 := by
    have h := hk'.1
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact h
  have e1 : NormedSpace.exp ((L k)ᴴ) = kᴴ := by rw [Matrix.exp_conjTranspose, h2]
  have e2 : NormedSpace.exp (-(L k)) = kᴴ := by
    rw [Matrix.exp_neg, h2]
    exact Matrix.inv_eq_left_inv hkk
  have hstar : (L k)ᴴ = -(L k) := by
    rw [← hA', e1, ← e2, hB']
  have e3 : NormedSpace.exp (Jm ε * L k * Jm ε) = NormedSpace.exp (L k) := by
    have h := Matrix.exp_conj (Jm ε) (L k) hJu
    rw [hJinv] at h
    rw [h, h2, mul_assoc, hk'.2, ← mul_assoc, hJJ, one_mul]
  have e4 : Jm ε * L k * Jm ε = L k := by
    rw [← hC', e3, h2]
  have hcomm : L k * Jm ε = Jm ε * L k := by
    calc L k * Jm ε = Jm ε * L k * Jm ε * Jm ε := by rw [e4]
      _ = Jm ε * L k := by rw [mul_assoc, hJJ, mul_one]
  refine ⟨⟨?_, hcomm⟩, h2⟩
  show (L k)ᴴ * Jm ε + Jm ε * L k = 0
  rw [hstar, neg_mul, ← hcomm]
  first
  | exact neg_add_cancel _
  | simp

open scoped Matrix.Norms.L2Operator in
lemma lcA_polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def nuNext (ν : Fin n → ℝ) (i : Fin n) : ℝ := if h : (i : ℕ) + 1 < n then ν ⟨(i : ℕ) + 1, h⟩ else 0

lemma inP_entry_zero {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, hab] at h
  cases hb : ε b <;> simp [hb] at h <;>
    first | exact h | linear_combination h / 2 | linear_combination -h / 2

lemma conjTranspose_eq_self_of_mem_noncompactPart {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) : Yᴴ = Y := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    split_ifs <;> norm_num
  have h1 : Yᴴ * Jm ε = Y * Jm ε := by
    rw [hY.2]
    exact eq_neg_of_add_eq_zero_left hY.1
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Y * Jm ε * Jm ε := by rw [h1]
    _ = Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

lemma inP_norm_symm {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) (a b : Fin n) :
    ‖Y b a‖ = ‖Y a b‖ := by
  have h := congrFun (congrFun (conjTranspose_eq_self_of_mem_noncompactPart hY) b) a
  rw [← h, Matrix.conjTranspose_apply, norm_star]

lemma hs_eq_two_lower {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    hs Y = 2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
  have hsplit : ∀ a b : Fin n, ‖Y a b‖ ^ 2 =
      (if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [inP_entry_zero hY rfl]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [inP_norm_symm hY]
  unfold hs
  calc (∑ a : Fin n, ∑ b : Fin n, ‖Y a b‖ ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, ((if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = (∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) +
        ∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0 := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

lemma sum_Ico_tele (f : ℕ → ℝ) {b : ℕ} : ∀ m, b ≤ m → ∑ i ∈ Finset.Ico b m, (f i - f (i + 1)) = f b - f m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

lemma nuNext_tele (ν : Fin n → ℝ) {a b : Fin n} (hba : b < a) :
    ∑ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) = ν b - ν a := by
  let f : ℕ → ℝ := fun k => if h : k < n then ν ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) =
      (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then f i - f (i + 1) else 0) := by
    intro i
    simp [f, nuNext, i.isLt]
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    Fin.sum_univ_eq_sum_range (fun k => if (b : ℕ) ≤ k ∧ k < (a : ℕ) then f k - f (k + 1) else 0) n,
    ← Finset.sum_filter]
  have hfil : (Finset.range n).filter (fun k => (b : ℕ) ≤ k ∧ k < (a : ℕ)) = Finset.Ico (b : ℕ) a := by
    ext k
    have := a.isLt
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfil, sum_Ico_tele f (b := (b : ℕ)) (a : ℕ) (Fin.lt_iff_val_lt_val.mp hba).le]
  simp [f, b.isLt, a.isLt]

theorem dec_weighted {ε : Fin n → Bool} (ν : Fin n → ℝ) (hν : Antitone ν) {g : ℝ}
    (hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → g ≤ ν b - ν a) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    g * hs Y / 2 ≤
      ∑ i : Fin n, (ν i - nuNext ν i) *
        (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) := by
  rw [hs_eq_two_lower hY]
  have hR : ∑ i : Fin n, (ν i - nuNext ν i) *
      (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then (ν b - ν a) * ‖Y a b‖ ^ 2 else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hba
    · rw [← nuNext_tele ν hba, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg, mul_zero]
      intro h
      exact hba (Fin.lt_iff_val_lt_val.mpr (lt_of_le_of_lt h.1 h.2))
  rw [hR]
  have hL : g * (2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) / 2 =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then g * ‖Y a b‖ ^ 2 else 0 := by
    have hg' : ∀ a b : Fin n, (if b < a then g * ‖Y a b‖ ^ 2 else 0) =
        g * (if b < a then ‖Y a b‖ ^ 2 else 0) := by
      intro a b; split_ifs <;> simp
    simp_rw [hg', ← Finset.mul_sum]
    ring
  rw [hL]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  split_ifs with hba
  · by_cases hε : ε a = ε b
    · rw [inP_entry_zero hY hε]; simp
    · exact mul_le_mul_of_nonneg_right (hg a b hε hba) (by positivity)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma toMK_one' (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

lemma toMK_mul' {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ Kset ε := k.2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
