module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

theorem rop_apply_eq (K : Type) [Field K] (k : ℕ) (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

theorem pderiv_inl_tt (K : Type) [Field K] (k : ℕ) (b : Fin k) :
    pderiv (Sum.inl b) (tt K k) = X (Sum.inr b) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem pderiv_inr_tt (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    pderiv (Sum.inr a) (tt K k) = X (Sum.inl a) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem rttRelation : RTT := by
  intro K _ _ k a b g
  rw [rop_apply_eq, rop_apply_eq]
  simp only [Derivation.leibniz, pderiv_inl_tt, pderiv_inr_tt, smul_eq_mul]
  ring

theorem iwh_X_pderiv {σ : Type} {K : Type} [Field K] (w : σ → ℕ) (i j : σ) (hij : w i = w j)
    {f : MvPolynomial σ K} {n : ℕ} (hf : IsWeightedHomogeneous w f n) :
    IsWeightedHomogeneous w (X i * pderiv j f) n := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum, Finset.mul_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have hwm : weight w m = n := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [pderiv_monomial]
  by_cases hmj : m j = 0
  · simp [hmj, isWeightedHomogeneous_zero]
  · have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have hs : ∀ v, weight w (Finsupp.single v 1) = w v := by
      intro v
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    have h1 : weight w (m - Finsupp.single j 1) + w j = n := by
      rw [← hs j, ← map_add (f := _), tsub_add_cancel_of_le hle, hwm]
    rw [X, monomial_mul, one_mul]
    apply isWeightedHomogeneous_monomial
    rw [map_add (f := _), hs i, hij, add_comm, h1]

theorem polarizationBihomogeneous : RBihom := by
  intro K _ _ k d a b f hf
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  show Rop K k a b f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  rw [rop_apply_eq]
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ ?_ ?_, Submodule.sub_mem _ ?_ ?_⟩ <;>
    rw [mem_weightedHomogeneousSubmodule]
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2

theorem coeff_X_pderiv_self {σ : Type} {K : Type} [Field K] (i : σ) (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (X i * pderiv i f) m = AddMonoidAlgebra.coeff f m * (m i : K) := by
  classical
  induction f using MvPolynomial.induction_on'
  next u a =>
    rw [pderiv_monomial]
    by_cases hu : u i = 0
    · by_cases h : u = m
      · subst h
        simp [hu]
      · simp [hu, coeff_monomial, h]
    · have hle : Finsupp.single i 1 ≤ u := by
        rw [Finsupp.single_le_iff]
        omega
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, coeff_monomial, coeff_monomial]
      split_ifs with h
      · subst h
        rfl
      · simp
  next p q hp hq =>
    simp only [map_add (f := _), mul_add, MvPolynomial.coeff_add, hp, hq, add_mul]

theorem weightOfEigenvector : WtOfEig := by
  intro K _ _ k a w f h m hm
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [rop_apply_eq, MvPolynomial.coeff_sub, coeff_X_pderiv_self, coeff_X_pderiv_self, MvPolynomial.coeff_smul] at h1
  have hc : AddMonoidAlgebra.coeff f m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h2 : (((m (Sum.inl a) : ℤ) - m (Sum.inr a) : ℤ) : K) = (w : K) := by
    apply mul_left_cancel₀ hc
    push_cast
    linear_combination h1
  exact_mod_cast h2

def va (k : ℕ) (a : Fin k) : Fin k ⊕ Fin k → ℤ :=
  Sum.elim (fun i => if i = a then 1 else 0) (fun i => if i = a then -1 else 0)

theorem weight_va (k : ℕ) (a : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) :
    weight (va k a) m = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, va, Fintype.sum_sum_type, sub_eq_add_neg]

theorem tt_va (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    IsWeightedHomogeneous (va k a) (tt K k) 0 := by
  show IsWeightedHomogeneous (va k a) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 0
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (va k a) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (va k a) (Sum.inr i))
  by_cases hi : i = a <;> simpa [va, hi] using h

theorem comp_mul_zero {σ : Type} {K : Type} [Field K] (w : σ → ℤ) {φ : MvPolynomial σ K}
    (hφ : IsWeightedHomogeneous w φ 0) (n : ℤ) (ψ : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (φ * ψ) = φ * weightedHomogeneousComponent w n ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : AddMonoidAlgebra.coeff φ x.1 = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 = n := by
        rw [← hd, ← hsum, map_add (f := _), hx0, zero_add]
      rw [if_pos hw]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : AddMonoidAlgebra.coeff φ x.1 = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 ≠ n := by
        rw [← hsum, map_add (f := _), hx0, zero_add] at hd
        exact hd
      rw [if_neg hw, mul_zero]

theorem tt_ne_zero (K : Type) [Field K] [CharZero K] (k : ℕ) (hk : 0 < k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  simp [tt] at h1
  omega

theorem pairingWeightCancel : TTWt := by
  intro K _ _ k c g h m hm a
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := ⟨_, rfl⟩
  have hwm : weight (va k a) m = n := by rw [weight_va, hn]
  have hk : 0 < k := Fin.pos a
  have hcomp : weightedHomogeneousComponent (va k a) n g ≠ 0 := by
    intro h0
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hwm] at h3
    exact (MvPolynomial.mem_support_iff.1 hm) (by simpa using h3)
  have hprod : weightedHomogeneousComponent (va k a) n (tt K k * g) ≠ 0 := by
    rw [comp_mul_zero (va k a) (tt_va K k a) n g]
    exact mul_ne_zero (tt_ne_zero K k hk) hcomp
  apply hprod
  ext m'
  rw [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero]
  split_ifs with hw
  · by_contra hne
    have h4 := h m' (MvPolynomial.mem_support_iff.2 hne) a
    rw [weight_va] at hw
    omega
  · rfl

end PI.OpWords
end
end

section

open MvPolynomial

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

def shiftPt (a b : Fin k) (s : K) (p : Fin k ⊕ Fin k → K) : Fin k ⊕ Fin k → K :=
  fun i => p i + s * eval p (Rop K k a b (X i))

lemma rop_apply (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

lemma rop_C (a b : Fin k) (r : K) : Rop K k a b (C r) = 0 := by
  simp [rop_apply]

lemma rop_mul (a b : Fin k) (f g : Pol K k) :
    Rop K k a b (f * g) = Rop K k a b f * g + f * Rop K k a b g := by
  rw [rop_apply, rop_apply, rop_apply]
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

lemma rop_rop_X (a b : Fin k) (hab : a ≠ b) (i : Fin k ⊕ Fin k) :
    Rop K k a b (Rop K k a b (X i)) = 0 := by
  rcases i with j | j
  · by_cases h : j = b
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]
  · by_cases h : j = a
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]

lemma rop_iter_mul_X (a b : Fin k) (hab : a ≠ b) (g : Pol K k) (i : Fin k ⊕ Fin k) (n : ℕ) :
    (Rop K k a b)^[n + 1] (g * X i) = (Rop K k a b)^[n + 1] g * X i
      + (n + 1) • ((Rop K k a b)^[n] g * Rop K k a b (X i)) := by
  induction n with
  | zero => simp [rop_mul]
  | succ n ih =>
    have e1 : (Rop K k a b)^[n + 1 + 1] (g * X i) = Rop K k a b ((Rop K k a b)^[n + 1] (g * X i)) :=
      Function.iterate_succ_apply' _ _ _
    have e2 : (Rop K k a b)^[n + 1 + 1] g = Rop K k a b ((Rop K k a b)^[n + 1] g) :=
      Function.iterate_succ_apply' _ _ _
    have e3 : (Rop K k a b)^[n + 1] g = Rop K k a b ((Rop K k a b)^[n] g) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, ih, map_add (f := _), map_nsmul, rop_mul, rop_mul, rop_rop_X a b hab i, e2, ← e3]
    rw [mul_zero, add_zero, succ_nsmul _ (n + 1)]
    abel

def ExpFormula (a b : Fin k) (s : K) (g : Pol K k) : Prop :=
  ∃ N : ℕ, (∀ n, N < n → (Rop K k a b)^[n] g = 0) ∧
    ∀ M, N ≤ M → ∀ p : Fin k ⊕ Fin k → K,
      eval (shiftPt a b s p) g =
        ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval p ((Rop K k a b)^[n] g)

theorem expFormula (a b : Fin k) (hab : a ≠ b) (s : K) (g : Pol K k) : ExpFormula a b s g := by
  unfold ExpFormula
  induction g using MvPolynomial.induction_on
  next r =>
    have hz : ∀ n, (Rop K k a b)^[n + 1] (C r) = 0 := by
      intro n
      rw [Function.iterate_succ_apply, rop_C]
      exact Function.iterate_fixed (map_zero _) n
    refine ⟨0, fun n hn => ?_, fun M _ x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact hz m
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro n _ hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hz m]
        simp
      · intro h
        simp at h
  next p q hp hq =>
    obtain ⟨N1, hz1, hs1⟩ := hp
    obtain ⟨N2, hz2, hs2⟩ := hq
    refine ⟨max N1 N2, fun n hn => ?_, fun M hM x => ?_⟩
    · rw [← Module.End.coe_pow, map_add (f := _), Module.End.coe_pow, hz1 n (by omega), hz2 n (by omega), add_zero]
    · rw [map_add (f := _), hs1 M (by omega) x, hs2 M (by omega) x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Module.End.coe_pow, map_add (f := _), map_add (f := _)]
      ring
  next p i hp =>
    obtain ⟨N, hz, hsum⟩ := hp
    refine ⟨N + 1, fun n hn => ?_, fun M hM x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rop_iter_mul_X a b hab p i m, hz (m + 1) (by omega), hz m (by omega)]
      simp
    · have hterm : ∀ m : ℕ, eval x ((Rop K k a b)^[m + 1] (p * X i)) =
          eval x ((Rop K k a b)^[m + 1] p) * x i +
            ((m : K) + 1) * (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) := by
        intro m
        rw [rop_iter_mul_X a b hab p i m, map_add (f := _), eval_mul, eval_X, map_nsmul, eval_mul, nsmul_eq_mul]
        push_cast
        ring
      have hTM : s ^ M / (M.factorial : K) * eval x ((Rop K k a b)^[M] p) = 0 := by
        rw [hz M (by omega), map_zero, mul_zero]
      have hfac : ∀ m : ℕ, s ^ (m + 1) / ((m + 1).factorial : K) * ((m : K) + 1) =
          s * (s ^ m / (m.factorial : K)) := by
        intro m
        have h1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have h2 : (m.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        rw [Nat.factorial_succ, Nat.cast_mul]
        push_cast
        (try field_simp)
        (try ring)
      have hR : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] (p * X i)) =
          ∑ m ∈ Finset.range M, (s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) * x i +
            s * eval x (Rop K k a b (X i)) * (s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p))) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) * x i := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hterm]
          linear_combination (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) * hfac m
        · simp
      have hS1 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) := Finset.sum_range_succ' _ _
      have hS2 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p) := by
        rw [Finset.sum_range_succ, hTM, add_zero]
      have hxi : shiftPt a b s x i = x i + s * eval x (Rop K k a b (X i)) := rfl
      rw [hR, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hS2, eval_mul, eval_X,
        hsum M (by omega) x, hxi, hS1]
      ring

end PI.OpWords
end
end
