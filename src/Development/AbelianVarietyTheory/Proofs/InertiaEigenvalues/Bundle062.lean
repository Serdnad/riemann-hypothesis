module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle020
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Fintype.Pigeonhole

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem pow_iter_frobeniusEquiv_symm {F : Type} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (x : F) (m : ℕ) : (((frobeniusEquiv F p).symm)^[m] x) ^ p ^ m = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have h := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[m] x)
    rw [frobenius_def] at h
    rw [h, ih]

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem norm_pw (k : ℤ) (x : F) : ‖pw p k x‖ = ‖x‖ ^ ((p : ℝ) ^ k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold pw
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [norm_pow, Int.toNat_natCast, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hm
    rw [neg_neg, Int.toNat_natCast]
    have hy := pow_iter_frobeniusEquiv_symm p x m
    conv_rhs => rw [← hy]
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (by positivity), Real.rpow_one]

theorem norm_term (k : ℕ) (ϖ : F) (hϖ : ‖ϖ‖ = (p : ℝ)⁻¹) (lam π : Fin (k + 1) → F) (r j : Fin (k + 1)) (n : ℤ) :
    ‖term p ϖ lam π r j n‖ = ‖lam j‖ * (p : ℝ) ^ n * ‖π j‖ ^ ((p : ℝ) ^ (((r : ℕ) : ℤ) + n * ((k : ℤ) + 1))) := by
  unfold term
  rw [norm_mul, norm_mul, norm_zpow, hϖ, norm_pw, inv_zpow', neg_neg]
  push_cast
  rfl

def idx (k : ℕ) (J : ℤ) : Fin (k + 1) :=
  ⟨(J % ((k : ℤ) + 1)).toNat, by
    have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos J (show (0 : ℤ) < (k : ℤ) + 1 by omega)
    omega⟩

theorem idx_spec (k : ℕ) (j : Fin (k + 1)) (m : ℤ) :
    idx k (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = j ∧ (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) / ((k : ℤ) + 1) = m := by
  have hj := j.isLt
  have h0 : ((j : ℕ) : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h1 : ((j : ℕ) : ℤ) % ((k : ℤ) + 1) = j := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · ext
    simp [idx, Int.add_mul_emod_self_left, h1]
  · rw [Int.add_mul_ediv_left _ _ (by omega), h0, zero_add]

theorem decomp (k : ℕ) (J : ℤ) : ∃ j : Fin (k + 1), ∃ m : ℤ, J = ((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
  refine ⟨idx k J, J / ((k : ℤ) + 1), ?_⟩
  have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
  have h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1)) := Int.emod_def _ _
  show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _
  rw [Int.toNat_of_nonneg h1]
  linarith

def aW (k : ℕ) (lam : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖lam (idx k J)‖ * (p : ℝ) ^ (-(J / ((k : ℤ) + 1)))

def rW (k : ℕ) (π : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖π (idx k J)‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * (J / ((k : ℤ) + 1)))))

theorem aW_at (k : ℕ) (lam : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    aW p k lam (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖lam j‖ * (p : ℝ) ^ (-m) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [aW, h1, h2]

theorem rW_at (k : ℕ) (π : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    rW p k π (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * m))) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [rW, h1, h2]

end GlobalTheory.PMonE.WinBounds

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem term_le_bound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  intro F _ p _ _ _ k ϖ hϖ lam π hlam hanti hratio hπ hrel1 hrel2 r j n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have ha : ∀ J, 0 < aW p k lam J := by
    intro J; unfold aW; exact mul_pos (norm_pos_iff.2 (hlam _)) (zpow_pos hp0 _)
  have hρ : ∀ J, 0 < rW p k π J := by
    intro J; unfold rW; exact Real.rpow_pos_of_pos (norm_pos_iff.2 (hπ _).1) _
  have hrp : ∀ (x : ℝ), 0 ≤ x → ∀ c d : ℤ, (x ^ ((p : ℝ) ^ c)) ^ ((p : ℝ) ^ d) = x ^ ((p : ℝ) ^ (c + d)) := by
    intro x hx c d; rw [← Real.rpow_mul hx, zpow_add₀ hpne]
  have hnat : ∀ (x : ℝ) (e : ℕ), x ^ ((p : ℝ) ^ (e : ℤ)) = x ^ (p ^ e) := by
    intro x e; rw [zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  have hstep : ∀ J, aW p k lam (J + 1) ≤ aW p k lam J := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
      have h1 := hratio 0 (Fin.last k)
      have hz := zpow_pos hp0 (-m)
      calc ‖lam 0‖ * ((p : ℝ) ^ (-m) * (p : ℝ)⁻¹) = (‖lam 0‖ / p) * (p : ℝ) ^ (-m) := by ring
        _ ≤ ‖lam (Fin.last k)‖ * (p : ℝ) ^ (-m) := by
          gcongr
          rw [div_le_iff₀ hp0]; linarith
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at]
      have h1 : ‖lam i.succ‖ ≤ ‖lam (Fin.castSucc i)‖ := hanti (Fin.castSucc_lt_succ (i := i)).le
      have hz := zpow_pos hp0 (-m)
      gcongr
  have hA : Antitone (aW p k lam) := antitone_int_of_succ_le hstep
  have hA0 : aW p k lam 0 < (p : ℝ) * aW p k lam (((k + 1 : ℕ) : ℤ) - 1) := by
    have h1 : aW p k lam 0 = ‖lam 0‖ := by simpa using aW_at p k lam 0 0
    have h2 : aW p k lam (k : ℤ) = ‖lam (Fin.last k)‖ := by simpa using aW_at p k lam (Fin.last k) 0
    rw [h1, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, h2]
    exact hratio 0 (Fin.last k)
  have hperA : ∀ J, aW p k lam (J + ((k + 1 : ℕ) : ℤ)) = aW p k lam J / p := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
    ring
  have hperR : ∀ J, rW p k π (J + ((k + 1 : ℕ) : ℤ)) = rW p k π J ^ (((p : ℝ) ^ (k + 1))⁻¹) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, rW_at, rW_at]
    have e3 : ((p : ℝ) ^ (k + 1))⁻¹ = (p : ℝ) ^ (-((k : ℤ) + 1)) := by
      rw [zpow_neg]; norm_cast
    rw [e3, hrp _ (norm_nonneg _), show -(((k : ℤ) + 1) * (m + 1)) = -(((k : ℤ) + 1) * m) + -((k : ℤ) + 1) by ring]
  have hrelW : ∀ J, aW p k lam (J + 1) * rW p k π (J + 1) ^ ((p : ℝ) ^ J)
      = aW p k lam J * rW p k π J ^ ((p : ℝ) ^ J) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * (m + 1)) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = -1 := by
        push_cast [Fin.val_last]; ring
      have e3 : -(((k : ℤ) + 1) * m) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((k : ℕ) : ℤ) := by
        push_cast [Fin.val_last]; ring
      rw [e2, e3, hnat, zpow_neg_one]
      have hXY : ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) = ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by
        have hx : 0 ≤ ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) := by positivity
        have hy : 0 ≤ ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by positivity
        refine (pow_left_inj₀ hx hy (Fact.out : p.Prime).ne_zero).1 ?_
        rw [mul_pow, ← hrel2, ← Real.rpow_natCast (‖π 0‖ ^ ((p : ℝ)⁻¹)) p, ← Real.rpow_mul (norm_nonneg _),
          inv_mul_cancel₀ hpne, Real.rpow_one]
      rw [neg_add, zpow_add₀ hpne, zpow_neg_one]
      linear_combination (p : ℝ) ^ (-m) * hXY
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * m) + ((((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((i : ℕ) : ℤ) := by
        push_cast [Fin.coe_castSucc]; ring
      rw [e2, hnat, hnat]
      have h := hrel1 i
      linear_combination (p : ℝ) ^ (-m) * h
  have hJ := window_ineq p (k + 1) (by exact_mod_cast (Fact.out : p.Prime).one_lt) (Nat.succ_pos k) (aW p k lam)
    (rW p k π) ha hρ hA hA0 hperA hperR hrelW (r : ℕ) r.isLt (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * (-n))
  rw [aW_at p k lam j (-n), rW_at p k π j (-n)] at hJ
  have hR1 : aW p k lam ((r : ℕ) : ℤ) = ‖lam r‖ := by simpa using aW_at p k lam r 0
  have hR2 : rW p k π ((r : ℕ) : ℤ) = ‖π r‖ := by simpa using rW_at p k π r 0
  rw [hR1, hR2] at hJ
  have hT : ‖term p ϖ lam π r j n‖
      = ‖lam j‖ * (p : ℝ) ^ (-(-n)) * (‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * -n)))) ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_term p k ϖ hϖ, ← zpow_natCast (p : ℝ) (r : ℕ), hrp _ (norm_nonneg _), neg_neg,
      show -(((k : ℤ) + 1) * -n) + ((r : ℕ) : ℤ) = ((r : ℕ) : ℤ) + n * ((k : ℤ) + 1) by ring]
  have hRt : ‖lam r * π r ^ p ^ (r : ℕ)‖ = ‖lam r‖ * ‖π r‖ ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖π r‖ (p ^ (r : ℕ)), Nat.cast_pow]
  rw [hT, hRt]
  obtain ⟨W1, W2, W3, W4⟩ := hJ
  have hj1 : ((j : ℕ) : ℤ) < (k : ℤ) + 1 := by exact_mod_cast j.isLt
  have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
  refine ⟨W1, fun hn => W2 (by nlinarith), fun hn => ?_⟩
  rcases lt_abs.1 hn with hn | hn
  · exact W3 (by push_cast; nlinarith)
  · exact W4 (by push_cast; nlinarith)

end GlobalTheory.PMonE.WinBounds
end
end

section

noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

section Lower

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lowerOrder (N : ℕ) (M : ℕ → Matrix m m F) (n : ℕ) : Matrix (m ⊕ m) (m ⊕ m) F :=
  fromBlocks (if n = N then 1 else 0) (if n + 1 = N then -1 else 0) (if n = 0 then M 0 else 0) (M (n + 1))

omit [Fintype m] in
theorem norm_one_apply_le (i j : m) : ‖(1 : Matrix m m F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype m] in
theorem lowerOrder_normal {N : ℕ} (hN : 1 ≤ N) {M : ℕ → Matrix m m F} (hM : Normal (N + 1) M) :
    Normal N (lowerOrder N M) := by
  constructor
  · intro n i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · split_ifs
      · exact norm_one_apply_le i j
      · simp
    · split_ifs
      · rw [Matrix.neg_apply, norm_neg]
        exact norm_one_apply_le i j
      · simp
    · split_ifs
      · exact hM.int 0 i j
      · simp
    · exact hM.int (n + 1) i j
  · have hN₀ : N ≠ 0 := by omega
    simp [lowerOrder, hN₀, hM.top]
  · intro n hn i j
    have h1 : n ≠ N := by omega
    have h2 : n + 1 ≠ N := by omega
    have h3 : n ≠ 0 := by omega
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, ite_eq_right h1, ite_eq_right h2,
        ite_eq_right h3,
        Matrix.zero_apply, norm_zero, zero_lt_one]
    exact hM.small (n + 1) (by omega) i j

theorem gsum_lowerOrder_inl (q : ℕ) {K D : ℕ} (hD : K + 1 ≤ D) (M : ℕ → Matrix m m F) (z : m ⊕ m → F) (i : m) :
    gsum q D (lowerOrder (K + 1) M) z (Sum.inl i) = z (Sum.inl i) ^ q ^ (K + 1) - z (Sum.inr i) ^ q ^ K := by

  have h : ∀ n, (lowerOrder (K + 1) M n).mulVec (fun k => z k ^ q ^ n) (Sum.inl i) =
      (if n = K + 1 then z (Sum.inl i) ^ q ^ (K + 1) else 0) +
        (if n = K then -z (Sum.inr i) ^ q ^ K else 0) := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Function.comp_def]
    by_cases h1 : n = K + 1
    · subst h1
      simp
    · by_cases h2 : n = K
      · subst h2
        simp [Matrix.neg_mulVec]
      · have h3 : n ≠ K := h2
        simp [h1, h3]
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), sub_eq_add_neg]

theorem gsum_lowerOrder_inr (q : ℕ) (N D : ℕ) (M : ℕ → Matrix m m F) (z : m ⊕ m → F)
    (hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ q) (i : m) :
    gsum q D (lowerOrder N M) z (Sum.inr i) = gsum q (D + 1) M (fun j => z (Sum.inl j)) i := by

  have h : ∀ n, (lowerOrder N M n).mulVec (fun k => z k ^ q ^ n) (Sum.inr i) =
      (if n = 0 then (M 0).mulVec (fun j => z (Sum.inl j) ^ q ^ 0) i else 0) +
        (M (n + 1)).mulVec (fun j => z (Sum.inl j) ^ q ^ (n + 1)) i := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Function.comp_def, hz]
    congr 1
    · split_ifs with h0
      · subst h0
        rfl
      · simp
    · congr 2
      funext j
      rw [← pow_mul, ← pow_succ']
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_range_succ' _ (D + 1), ite_eq_left (by omega), add_comm]

end Lower

theorem glOnto_succ (K : ℕ) (H : GLOnto (K + 1)) : GLOnto (K + 2) := by
  intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩

  obtain ⟨z, hzI, hzs⟩ := H F p (m ⊕ m) e D he (by omega) (lowerOrder (K + 1) M)
    (lowerOrder_normal (by omega) hM) (Sum.elim 0 b) (by
      intro k
      rcases k with k | k
      · simp
      · exact hb k)

  have hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ p ^ e := by
    intro i
    have h0 := congrFun hzs (Sum.inl i)
    rw [gsum_lowerOrder_inl (p ^ e) (by omega)] at h0
    simp only [Sum.elim_inl, Pi.zero_apply] at h0
    have hqK : (p ^ e) ^ K = p ^ (e * K) := (pow_mul p e K).symm
    have h1 : (z (Sum.inl i) ^ p ^ e - z (Sum.inr i)) ^ p ^ (e * K) = 0 := by
      rw [sub_pow_char_pow, ← hqK, ← pow_mul, ← pow_succ']
      exact h0
    exact (sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h1)).symm
  refine ⟨fun j => z (Sum.inl j), fun j => hzI (Sum.inl j), ?_⟩
  funext i
  rw [← gsum_lowerOrder_inr (p ^ e) (K + 1) D M z hz i, hzs]
  rfl

theorem glOnto_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  intro N hN H
  induction N, hN using Nat.le_induction with
  | base => exact H
  | succ n hn ih =>
    obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
    exact glOnto_succ K ih

end GlobalTheory.PMonE

end
end

section

namespace GlobalTheory.PsChar

open Matrix

theorem det_succ_eq_sub_sum_updateRow {A : Type*} [CommRing A] {m : ℕ} (N : Matrix (Fin (m + 1)) (Fin (m + 1)) A) :
    N.det = N 0 0 * (N.submatrix Fin.succ Fin.succ).det -
      ∑ c : Fin m, N c.succ 0 * ((N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ)).det := by
  rw [Matrix.det_apply', Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type, Fin.sum_univ_succ,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign]
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.det_apply', Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h : ∀ i : Fin m, N (Equiv.swap 0 c.succ (e i).succ) i.succ =
        (N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ) (e i) i := by
      intro i
      by_cases hc : e i = c
      · simp [hc]
      · rw [Matrix.updateRow_ne hc, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => hc (Fin.succ_injective _ h))]
        rfl
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign, h]
    ring

theorem alt_trace_eq_sum_det {M A : Type*} [Monoid M] [CommRing A] {n : ℕ} (r : M →* Matrix (Fin n) (Fin n) A) :
    ∀ (m : ℕ) (x : Fin m → M), alt (fun g => (r g).trace) m x =
      ∑ i : Fin m → Fin n, (Matrix.of fun a b => r (x a) (i b) (i a)).det
  | 0, x => by simp [alt]
  | m + 1, x => by
    rw [alt, ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    simp only [alt_trace_eq_sum_det r m, det_succ_eq_sub_sum_updateRow, Finset.sum_sub_distrib]
    congr 1
    · rw [Matrix.trace, Finset.sum_mul_sum]
      rfl
    · rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 : (Matrix.of fun a b => r (Function.update (Fin.tail x) c (x 0 * Fin.tail x c) a) (i b) (i a)) =
          (Matrix.of fun a b => r (x a.succ) (i b) (i a)).updateRow c
            (∑ j : Fin n, r (x c.succ) j (i c) • fun b => r (x 0) (i b) j) := by
        ext a b
        by_cases h : a = c
        · subst h
          simp [Fin.tail, Matrix.mul_apply, mul_comm]
        · simp [Fin.tail, h]
      rw [h1]
      have h2 : ∀ (P : Matrix (Fin m) (Fin m) A) (s : Finset (Fin n)) (w : Fin n → A) (v : Fin n → Fin m → A),
          (P.updateRow c (∑ j ∈ s, w j • v j)).det = ∑ j ∈ s, w j * (P.updateRow c (v j)).det := by
        intro P s w v
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact Matrix.det_eq_zero_of_row_eq_zero c (by simp)
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.det_updateRow_add, ih, Matrix.det_updateRow_smul]
      rw [h2]
      rfl

theorem isPsChar_trace (M A : Type) [Monoid M] [CommRing A] (n : ℕ) (r : M →* Matrix (Fin n) (Fin n) A) :
    IsPsChar n (fun g => (r g).trace) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro x y
    simp only [map_mul]
    exact Matrix.trace_mul_comm _ _
  · intro x
    rw [alt_trace_eq_sum_det]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨b, b', hne, hb⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hb])

end GlobalTheory.PsChar
end

section

namespace GlobalTheory.BaseChangeInduction

theorem baseChange_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : GlobalTheory.Prism.SemiBC u)
    (p : N → Prop) (hzero : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (r : B) (y : N), p y → p (r • y)) (himg : ∀ x : M, p (u x)) (y : N) : p y := by
  let S : Submodule B N :=
    { carrier := {n | p n}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun r n hn => hsmul r n hn }
  have hq : S.mkQ = 0 := by
    refine (h (N ⧸ S) 0).unique (fun x => ?_) (fun x => rfl)
    exact (Submodule.Quotient.mk_eq_zero S).2 (himg x)
  have hy : S.mkQ y = 0 := by rw [hq]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 hy

end GlobalTheory.BaseChangeInduction
end
