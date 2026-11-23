module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.HookSteps.Cap

open Finset

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

theorem Lw_succ (x d : I → S → 𝒰) {k : ℕ} (w g : Fin (k + 1) → I) :
    Lw x d w g = (Eop x d (w 0) (g 0) + if w 0 = g 0 then (k : 𝒰) else 0) *
      Lw x d (fun i => w i.succ) (fun i => g i.succ) := by
  unfold Lw
  rw [List.ofFn_succ, List.prod_cons]
  congr 1
  · simp
  · congr 2
    funext j
    split_ifs
    · push_cast [Fin.val_succ]
      abel
    · rfl

theorem Pn_succ (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (w g : Fin (k + 1) → I) :
    Pn x d w g = Eop x d (w 0) (g 0) * Pn x d (fun i => w i.succ) (fun i => g i.succ) -
      ∑ j : Fin k, if w j.succ = g 0 then
        Pn x d (Function.update (fun i => w i.succ) j (w 0)) (fun i => g i.succ) else 0 := by
  have h := E_Pn x d hxx hdx (fun i => w i.succ) (fun i => g i.succ) (w 0) (g 0)
  have hw : (Fin.cons (w 0) (fun i => w i.succ) : Fin (k + 1) → I) = w := Fin.cons_self_tail w
  have hg : (Fin.cons (g 0) (fun i => g i.succ) : Fin (k + 1) → I) = g := Fin.cons_self_tail g
  rw [hw, hg] at h
  rw [h]
  abel

theorem D_succ (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (w g : Fin (k + 1) → I) :
    Lw x d w g - Pn x d w g =
      (Eop x d (w 0) (g 0) + if w 0 = g 0 then (k : 𝒰) else 0) *
        (Lw x d (fun i => w i.succ) (fun i => g i.succ) -
          Pn x d (fun i => w i.succ) (fun i => g i.succ)) +
      (k : ℕ) • (if w 0 = g 0 then Pn x d (fun i => w i.succ) (fun i => g i.succ) else 0) +
      ∑ j : Fin k, if w j.succ = g 0 then
        Pn x d (Function.update (fun i => w i.succ) j (w 0)) (fun i => g i.succ) else 0 := by
  rw [Lw_succ, Pn_succ x d hxx hdx]
  have hc : (if w 0 = g 0 then (k : 𝒰) else 0) * Pn x d (fun i => w i.succ) (fun i => g i.succ) =
      (k : ℕ) • (if w 0 = g 0 then Pn x d (fun i => w i.succ) (fun i => g i.succ) else 0) := by
    split_ifs <;> simp [nsmul_eq_mul]
  rw [mul_sub, add_mul (Eop x d (w 0) (g 0)),
    add_mul (Eop x d (w 0) (g 0)) _ (Pn x d (fun i => w i.succ) (fun i => g i.succ)), hc]
  abel

theorem alt_first {k : ℕ} (F : I → 𝒰) (Δ : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I)
    (hIH : ∀ r' : Fin k → I,
      ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun j => r' (τ j)) = 0) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      (F (r (σ 0)) * Δ (fun i => r (σ i.succ))) = 0 := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp only [Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  have h0 : ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      Δ (fun i => r (Equiv.swap 0 p (τ i).succ)) = 0 := hIH (fun j => r (Equiv.swap 0 p j.succ))
  calc _ = F (r p) * (((if p = 0 then 1 else -1 : ℤˣ) : ℤ) • ∑ τ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun i => r (Equiv.swap 0 p (τ i).succ))) := by
        rw [Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Units.val_mul, mul_smul, mul_smul_comm, mul_smul_comm]
    _ = 0 := by rw [h0, smul_zero, mul_zero]

theorem alt_contract {k : ℕ} (Q : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I) (b : I) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) = 0 := by
  obtain ⟨A, hA⟩ : ∃ A : Equiv.Perm (Fin (k + 1)) → 𝒰,
      ∀ σ, A σ = if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0 := ⟨_, fun _ => rfl⟩
  have hB : ∀ (σ : Equiv.Perm (Fin (k + 1))) (j : Fin k),
      (if r (σ j.succ) = b then Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) =
        A (σ * Equiv.swap 0 j.succ) := by
    intro σ j
    have hf : Function.update (fun i => r (σ i.succ)) j (r (σ 0)) =
        fun i => r (σ (Equiv.swap 0 j.succ i.succ)) := by
      funext i
      by_cases h : i = j
      · subst h
        rw [Function.update_apply, if_pos rfl, Equiv.swap_apply_right]
      · rw [Function.update_apply, if_neg h, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
          (fun e => h (Fin.succ_injective _ e))]
    rw [hA]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [hf]
  have hS : ∀ j : Fin k, ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      A (σ * Equiv.swap 0 j.succ) =
      -∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A σ := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (k + 1)) j.succ)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Fin.succ_ne_zero j).symm, Units.val_mul, Units.val_neg, Units.val_one,
      mul_neg_one, neg_smul]
  have e : ∀ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) =
      (k : ℕ) • (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A σ) +
        ∑ j : Fin k, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A (σ * Equiv.swap 0 j.succ) := by
    intro σ
    rw [smul_add, Finset.smul_sum, smul_comm ((Equiv.Perm.sign σ : ℤˣ) : ℤ) (k : ℕ), ← hA σ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB σ j]
  rw [Finset.sum_congr rfl fun σ _ => e σ, Finset.sum_add_distrib, Finset.sum_comm,
    ← Finset.smul_sum]
  simp_rw [hS]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_neg, add_neg_cancel]

theorem capelli_absolute_value : CapAbsMain := by
  unfold CapAbsMain
  intro 𝒰 _ I S _ _ _ x d hxx hdx k
  induction k with
  | zero =>
    intro r g
    simp only [Lw, Pn, xw, dw]
    simp
  | succ k ih =>
    intro r g
    have h1 := alt_first (fun a => Eop x d a (g 0) + if a = g 0 then (k : 𝒰) else 0)
      (fun w' => Lw x d w' (fun i => g i.succ) - Pn x d w' (fun i => g i.succ)) r
      (fun r' => ih r' (fun i => g i.succ))
    have h2 := alt_contract (fun w' => Pn x d w' (fun i => g i.succ)) r (g 0)
    calc _ = ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            ((Eop x d (r (σ 0)) (g 0) + if r (σ 0) = g 0 then (k : 𝒰) else 0) *
              (Lw x d (fun i => r (σ i.succ)) (fun i => g i.succ) -
                Pn x d (fun i => r (σ i.succ)) (fun i => g i.succ))) +
          ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            ((k : ℕ) • (if r (σ 0) = g 0 then Pn x d (fun i => r (σ i.succ)) (fun i => g i.succ)
                else 0) +
              ∑ j : Fin k, if r (σ j.succ) = g 0 then
                Pn x d (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) (fun i => g i.succ)
                else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← smul_add, D_succ x d hxx hdx, add_assoc]
      _ = 0 + 0 := congrArg₂ (· + ·) h1 h2
      _ = 0 := add_zero 0

end PI.HookSteps.Cap
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

theorem sum_rev_eq (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := Finset.sum_range_reflect (fun i => i) N
  rw [h, Finset.sum_range_id]

theorem factorial_add_le (a k B : ℕ) (h : a + k ≤ B) : (a + k).factorial ≤ a.factorial * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    rw [← add_assoc, Nat.factorial_succ, pow_succ]
    calc (a + k + 1) * (a + k).factorial ≤ B * (a.factorial * B ^ k) :=
          Nat.mul_le_mul (by omega) ih'
      _ = a.factorial * (B ^ k * B) := by ring

theorem prod_factorial_le (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∏ i : Fin N, (ν i + (N - 1 - i)).factorial ≤
      (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
  have hB : ∀ i : Fin N, ν i + (N - 1 - i) ≤ ν ⟨0, hN⟩ + N := fun i => by
    have := hν (show (⟨0, hN⟩ : Fin N) ≤ i from Nat.zero_le _)
    omega
  calc ∏ i : Fin N, (ν i + (N - 1 - i)).factorial
      ≤ ∏ i : Fin N, ((ν i).factorial * (ν ⟨0, hN⟩ + N) ^ (N - 1 - (i : ℕ))) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun i _ => factorial_add_le _ _ _ (hB i)
    _ = (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rev_eq]

theorem hook_bound : HookBoundOf := by
  unfold HookBoundOf PI.HookBound
  intro hH N hN ν hν
  have h1 := PI.HookLower.one_le_cNu ν hν
  refine ⟨h1, ?_⟩
  have hD : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast (ν l).factorial_pos
  unfold PI.cNu at h1 ⊢
  have hF0r : (0 : ℝ) ≤ (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) := by
    have := (one_le_div hD).1 h1
    linarith
  have hF0 : (0 : ℚ) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by exact_mod_cast hF0r
  have hP : (1 : ℚ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ) := by
    calc (1 : ℚ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (1 : ℚ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun j hj => by
            have hij' : i < j := Finset.mem_Ioi.1 hj
            have hij : (i : ℕ) < j := hij'
            exact_mod_cast (show 1 ≤ ν i - ν j + (j - i) by omega)
  have hQ := hH N ν hν
  have hFQ : fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ) := by
    rw [← hQ]
    exact le_mul_of_one_le_right hF0 hP
  have hFQr : (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ) := by exact_mod_cast hFQ
  have hle : (∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ)) ≤
      (∏ i, ((ν i).factorial : ℝ)) * ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2) := by
    exact_mod_cast prod_factorial_le N hN ν hν
  rw [div_le_iff₀ hD]
  linarith

end PI.HookSteps
end
end
