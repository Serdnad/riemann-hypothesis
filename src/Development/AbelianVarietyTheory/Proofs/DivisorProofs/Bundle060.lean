module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

section

open scoped Matrix Matrix.Norms.Frobenius

namespace GlobalTheory

theorem frobCmp_normSq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

theorem frobCmp_le {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : ‖A‖ ≤ ‖B‖ := by
  have hsq : ‖A‖ ^ 2 ≤ ‖B‖ ^ 2 := by
    rw [frobCmp_normSq, frobCmp_normSq]
    gcongr with i _ j _
    exact h i j
  nlinarith [norm_nonneg A, norm_nonneg B]

theorem frobCmp_le_const {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i j, ‖A i j‖ ≤ ε) : ‖A‖ ≤ r * ε := by
  have hsq : ‖A‖ ^ 2 ≤ ((r : ℝ) * ε) ^ 2 := by
    rw [frobCmp_normSq]
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin r, ∑ _j : Fin r, ε ^ 2 := by
          gcongr with i _ j _
          exact h i j
      _ = ((r : ℝ) * ε) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have : 0 ≤ (r : ℝ) * ε := by positivity
  nlinarith [norm_nonneg A]

theorem frobenius_lower_comparison : ∀ (r : ℕ) (g n b B W H : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, a < c → n a c = 0) → (∀ a : Fin r, n a a = 1) → (∀ a c : Fin r, c < a → ‖n a c‖ ≤ δ) → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) → (∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ) → (∀ a c : Fin r, c < a → B a c = 0) → (∀ a c : Fin r, a ≤ c → W a c = 0) → (∀ a c : Fin r, a ≤ c → H a c = 0) → g * n = b → g * W = H * b + B → ∑ a, ∑ c, ‖W a c‖ ^ 2 ≤ 2 * ∑ a, ∑ c, ‖H a c‖ ^ 2 := by
  intro r g n b B W H δ hδ hrδ hn_up hn_diag hn_low hb_low hb_diag hb_up hB hW hH hgn hgW
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hδ1 : δ ≤ 1 / 100 := by nlinarith

  have hnT : n.BlockTriangular OrderDual.toDual := fun i j hij => hn_up i j (by simpa using hij)
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_lowerTriangular n hnT]; simp [hn_diag]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  letI := n.invertibleOfIsUnitDet hu
  have hinvT : n⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hnT
  obtain ⟨Y, hY⟩ : ∃ Y, Y = n⁻¹ * W := ⟨_, rfl⟩
  have hYlow : ∀ a c, a ≤ c → Y a c = 0 := by
    intro a c hac
    rw [hY, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : a < k
    · rw [hinvT (by simpa using hk), zero_mul]
    · rw [hW k c (le_trans (not_lt.mp hk) hac), mul_zero]
  have hWnY : W = n * Y := by
    rw [hY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hg : g = b * n⁻¹ := by
    rw [← hgn, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hbY : b * Y = H * b + B := by rw [← hgW, hg, hY, Matrix.mul_assoc]

  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = Matrix.diagonal (fun a => b a a) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu'⟩ : ∃ u, u = b - D := ⟨_, rfl⟩
  have hbDu : b = D + u := by rw [hu']; abel
  have hdlow : ∀ a, (0.969 : ℝ) ≤ ‖b a a‖ := by
    intro a
    have h1 := (abs_le.mp (hb_diag a)).1
    nlinarith [norm_nonneg (b a a)]
  have hdup : ∀ a, ‖b a a‖ ≤ (1.03 : ℝ) := by
    intro a
    have h1 := (abs_le.mp (hb_diag a)).2
    nlinarith [norm_nonneg (b a a)]
  have hunorm : ‖u‖ ≤ 6 / 100 := by
    have h := frobCmp_le_const u (6 * δ) (by positivity) (by
      intro a c
      rw [hu', Matrix.sub_apply, hD]
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), sub_zero]; exact hb_up a c hac
      · simp; positivity
      · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), sub_zero, hb_low a c hac, norm_zero]
        positivity)
    nlinarith
  have hn1 : ‖n - 1‖ ≤ 1 / 100 := by
    have h := frobCmp_le_const (n - 1) δ hδ (by
      intro a c
      rw [Matrix.sub_apply]
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [hn_up a c hac, Matrix.one_apply_ne (ne_of_lt hac), sub_zero, norm_zero]; exact hδ
      · rw [hn_diag, Matrix.one_apply_eq, sub_self, norm_zero]; exact hδ
      · rw [Matrix.one_apply_ne (ne_of_gt hac), sub_zero]; exact hn_low a c hac)
    linarith

  have hM : D * Y = H * D + H * u - u * Y + B := by
    have e1 : D * Y = b * Y - u * Y := by rw [hbDu, Matrix.add_mul]; abel
    rw [e1, hbY, hbDu, Matrix.mul_add]; abel
  have hkey : ‖D * Y‖ ≤ ‖H * D + H * u - u * Y‖ := by
    apply frobCmp_le
    intro a c
    by_cases hca : c < a
    · rw [hM, Matrix.add_apply, hB a c hca, add_zero]
    · rw [hD, Matrix.diagonal_mul, hYlow a c (not_lt.mp hca), mul_zero, norm_zero]
      exact norm_nonneg _
  have hDY : (0.969 : ℝ) * ‖Y‖ ≤ ‖D * Y‖ := by
    have h : ‖(0.969 : ℝ) • Y‖ ≤ ‖D * Y‖ := by
      apply frobCmp_le
      intro a c
      rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
        hD, Matrix.diagonal_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hdlow a) (norm_nonneg _)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
  have hHD : ‖H * D‖ ≤ (1.03 : ℝ) * ‖H‖ := by
    have h : ‖H * D‖ ≤ ‖(1.03 : ℝ) • H‖ := by
      apply frobCmp_le
      intro a c
      rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
        hD, Matrix.mul_diagonal, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hdup c) (norm_nonneg _)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
  have hHu : ‖H * u‖ ≤ ‖H‖ * ‖u‖ := Matrix.frobenius_norm_mul H u
  have huY : ‖u * Y‖ ≤ ‖u‖ * ‖Y‖ := Matrix.frobenius_norm_mul u Y
  have htri : ‖H * D + H * u - u * Y‖ ≤ ‖H * D‖ + ‖H * u‖ + ‖u * Y‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have hHn := norm_nonneg H
  have hYn := norm_nonneg Y
  have hun := norm_nonneg u
  have hY12 : ‖Y‖ ≤ 1.2 * ‖H‖ := by nlinarith
  have hWY : ‖W‖ ≤ (1.01 : ℝ) * ‖Y‖ := by
    have e : W = Y + (n - 1) * Y := by rw [hWnY, Matrix.sub_mul, Matrix.one_mul]; abel
    have h1 : ‖W‖ ≤ ‖Y‖ + ‖n - 1‖ * ‖Y‖ := by
      rw [e]; exact (norm_add_le _ _).trans (by gcongr; exact Matrix.frobenius_norm_mul _ _)
    nlinarith [norm_nonneg (n - 1)]
  have hWn := norm_nonneg W
  rw [← frobCmp_normSq, ← frobCmp_normSq]
  nlinarith

end GlobalTheory
end

section

open Matrix Filter Topology

namespace GlobalTheory.MatSqrtNearOne

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem norm_mul_le_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_apply_le_norm A) (norm_apply_le_norm B)
    (norm_nonneg _) (norm_nonneg _)

theorem norm_add_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [Matrix.norm_le_iff (le_max_of_le_left (norm_nonneg _))]
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_apply_le_norm A) (norm_apply_le_norm B))

theorem norm_sub_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [sub_eq_add_neg, ← norm_neg B]
  exact norm_add_le_max_ultra A (-B)

noncomputable def iter (u : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => 0
  | k + 1 => u - iter u k * iter u k

theorem commute_iter {u a : Matrix (Fin n) (Fin n) K} (h : Commute a u) :
    ∀ k, Commute a (iter u k)
  | 0 => Commute.zero_right a
  | k + 1 => h.sub_right ((commute_iter h k).mul_right (commute_iter h k))

theorem norm_iter_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) : ∀ k, ‖iter u k‖ ≤ ‖u‖ := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter]
    refine (norm_sub_le_max_ultra _ _).trans (max_le le_rfl ?_)
    calc ‖iter u k * iter u k‖ ≤ ‖iter u k‖ * ‖iter u k‖ := norm_mul_le_ultra _ _
      _ ≤ ‖u‖ * 1 := mul_le_mul ih (ih.trans hc.le) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u‖ := mul_one _

theorem matrix_sub_mul_self_sub_eq_neg_mul_of_commute (u a b : Matrix (Fin n) (Fin n) K) (h : Commute a b) :
    (u - b * b) - (u - a * a) = -((b - a) * (a + b)) := by
  rw [sub_mul, mul_add, mul_add, ← h.eq]
  abel

theorem norm_iter_diff_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) :
    ∀ k, ‖iter u (k + 1) - iter u k‖ ≤ ‖u‖ * ‖u‖ ^ k := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hcomm : Commute (iter u k) (iter u (k + 1)) :=
      commute_iter (commute_iter (Commute.refl u) k).symm (k + 1)
    have hstep : iter u (k + 1 + 1) - iter u (k + 1) =
        (u - iter u (k + 1) * iter u (k + 1)) - (u - iter u k * iter u k) :=
      congrArg₂ (· - ·) (iter.eq_2 u (k + 1)) (iter.eq_2 u k)
    rw [hstep, matrix_sub_mul_self_sub_eq_neg_mul_of_commute u _ _ hcomm, norm_neg]
    have hab : ‖iter u k + iter u (k + 1)‖ ≤ ‖u‖ :=
      (norm_add_le_max_ultra _ _).trans (max_le (norm_iter_le hc k) (norm_iter_le hc (k + 1)))
    calc ‖(iter u (k + 1) - iter u k) * (iter u k + iter u (k + 1))‖
        ≤ ‖iter u (k + 1) - iter u k‖ * ‖iter u k + iter u (k + 1)‖ := norm_mul_le_ultra _ _
      _ ≤ (‖u‖ * ‖u‖ ^ k) * ‖u‖ :=
          mul_le_mul ih hab (norm_nonneg _) (by positivity)
      _ = ‖u‖ * ‖u‖ ^ (k + 1) := by ring

theorem tau_add (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A + B).map σ)ᵀ = (A.map σ)ᵀ + (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_sub (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A - B).map σ)ᵀ = (A.map σ)ᵀ - (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_mul (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem tau_one (σ : K →+* K) : ((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

theorem tau_smul (σ : K →+* K) (c : K) (A : Matrix (Fin n) (Fin n) K) :
    ((c • A).map σ)ᵀ = σ c • (A.map σ)ᵀ := by
  ext i j; simp

theorem exists_sqrt [CompleteSpace K] [CharZero K] (σ : K →+* K) (hσ : Continuous σ)
    (s : Matrix (Fin n) (Fin n) K)
    (hs : ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖) :
    ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K,
      a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have h4p : 0 < ‖(4 : K)‖ := norm_pos_iff.2 h4
  set u : Matrix (Fin n) (Fin n) K := (4 : K)⁻¹ • (s - 1) with hu
  have hs1 : ‖s - 1‖ < ‖(4 : K)‖ := (Matrix.norm_lt_iff h4p).2 fun i j => by simpa using hs i j
  have hc : ‖u‖ < 1 := by
    rw [hu, norm_smul, norm_inv, inv_mul_lt_iff₀ h4p, mul_one]
    exact hs1
  have hcs : CauchySeq (iter u) := cauchySeq_of_le_geometric ‖u‖ ‖u‖ hc fun k => by
    rw [dist_eq_norm, norm_sub_rev]; exact norm_iter_diff_le hc k
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  have hfix : y + y * y = u := by
    have h1 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 y) := hy.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 (u - y * y)) :=
      tendsto_const_nhds.sub (hy.mul hy)
    exact eq_sub_iff_add_eq.1 (tendsto_nhds_unique h1 h2)
  refine ⟨1 + (2 : K) • y, ?_, ?_, ?_⟩
  · calc (1 + (2 : K) • y) * (1 + (2 : K) • y) = 1 + (4 : K) • (y + y * y) := by
          rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
          module
      _ = s := by rw [hfix, hu, smul_inv_smul₀ h4]; abel
  · intro a ha
    have hau : Commute a u := ((Commute.sub_right ha (Commute.one_right a))).smul_right _
    have hay : a * y = y * a :=
      tendsto_nhds_unique (hy.const_mul a)
        ((hy.mul_const a).congr fun k => (commute_iter hau k).eq.symm)
    exact ((Commute.one_right a).add_right ((show Commute a y from hay).smul_right (2 : K))).eq
  · intro hsσ
    have hτu : (u.map σ)ᵀ = u := by
      rw [hu, tau_smul, tau_sub, tau_one, hsσ, map_inv₀, map_ofNat]
    have hτiter : ∀ k, ((iter u k).map σ)ᵀ = iter u k := by
      intro k
      induction k with
      | zero => ext i j; simp [iter]
      | succ k ih =>
        show ((u - iter u k * iter u k).map σ)ᵀ = u - iter u k * iter u k
        rw [tau_sub, tau_mul, ih, hτu]
    have hτc : Continuous fun M : Matrix (Fin n) (Fin n) K => (M.map σ)ᵀ :=
      (continuous_id.matrix_map hσ).matrix_transpose
    have hτy : (y.map σ)ᵀ = y :=
      tendsto_nhds_unique ((hτc.tendsto y).comp hy) (hy.congr fun k => (hτiter k).symm)
    rw [tau_add, tau_one, tau_smul, hτy, map_ofNat]

end GlobalTheory.MatSqrtNearOne

namespace GlobalTheory

theorem matrix_sqrt_near_one_ultrametric :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ →
      ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K,
        r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧
        ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  intro K _ _ _ _ n σ hσ
  have h4 : (4 : K) ≠ 0 := by norm_num
  refine ⟨{s | ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp [h4])
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_id.matrix_elem i j).sub continuous_const).norm continuous_const
  · intro s hs
    exact MatSqrtNearOne.exists_sqrt σ hσ s hs

end GlobalTheory
end

section

namespace GlobalTheory

theorem norm_eigenvalue_le_one_of_integral_matrix (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] (emb : O →+* K) (hemb : ∀ c, ‖emb c‖ ≤ 1) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K) (hc : c ≠ 0)
    (hM : (M.map emb).mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖) ⟨j₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖c k‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hj₀) (hk j₀ (Finset.mem_univ _))
  have hrow : (M.map emb).mulVec c k = μ * c k := by
    rw [hM]; simp
  have hsum : ‖(M.map emb).mulVec c k‖ ≤ ‖c k‖ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖emb (M k j)‖ * ‖c j‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul (hemb _) (hk j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖c k‖ := one_mul _
  rw [hrow, norm_mul] at hsum
  have : ‖μ‖ * ‖c k‖ ≤ 1 * ‖c k‖ := by rwa [one_mul]
  exact le_of_mul_le_mul_right this hpos

theorem eigenvalue_integral_matrix_norm_le_one :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K),
      (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K),
      c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 :=
  fun O K _ _ _ emb hemb n M μ c hc hM =>
    norm_eigenvalue_le_one_of_integral_matrix O K emb hemb n M μ c hc hM

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial

theorem norm_multiset_sum_le_of_forall_le_ultrametric {K : Type} [NormedField K]
    [IsUltrametricDist K] (m : Multiset K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ m, ‖x‖ ≤ C) :
    ‖m.sum‖ ≤ C := by
  induction m using Multiset.induction_on with
  | empty => simpa using hC
  | cons a s ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self _ _)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

theorem norm_multiset_prod_le_pow_card_of_forall_le {K : Type} [NormedField K]
    (m : Multiset K) {B : ℝ} (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    have ha := h a (Multiset.mem_cons_self _ _)
    exact mul_le_mul ha (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      ((norm_nonneg _).trans ha)

theorem norm_coeff_natDegree_sub_le_pow_of_roots_le (K : Type) [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] (Q : Polynomial K) (hQ : Q.Monic) (B : ℝ)
    (hB : ∀ r : K, Q.IsRoot r → ‖r‖ ≤ B) (i : ℕ) (hi : i ≤ Q.natDegree) :
    ‖Q.coeff (Q.natDegree - i)‖ ≤ B ^ i := by
  have hcard : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ r ∈ Q.roots, ‖r‖ ≤ B := fun r hr => hB r (isRoot_of_mem_roots hr)
  have hBi : 0 ≤ B ^ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp
    · have : 0 < Multiset.card Q.roots := by omega
      obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.1 this
      exact pow_nonneg ((norm_nonneg _).trans (hroot r hr)) _
  rw [Polynomial.coeff_eq_esymm_roots_of_card hcard (Nat.sub_le _ _), hQ.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Multiset.esymm]
  refine norm_multiset_sum_le_of_forall_le_ultrametric _ hBi ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hle, hc⟩ := Multiset.mem_powersetCard.1 ht
  rw [← hc]
  exact norm_multiset_prod_le_pow_card_of_forall_le t fun y hy =>
    hroot y (Multiset.mem_of_le hle hy)

end GlobalTheory
end

section

namespace GlobalTheory.BoundedUnitsCompact

theorem boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))

theorem isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]

end GlobalTheory.BoundedUnitsCompact
end
