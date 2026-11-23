module

public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle006
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Mathlib.Algebra.AffineMonoid.UniqueSums
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

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookLower

def diagHom (N : ℕ) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N × Fin N) ℚ :=
  aeval fun v => if v.1 = v.2 then X v else 0

def IsDiag {N : ℕ} (m : Fin N × Fin N →₀ ℕ) : Prop := ∀ v : Fin N × Fin N, v.1 ≠ v.2 → m v = 0

open scoped Classical in
theorem diagHom_monomial {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (c : ℚ) :
    diagHom N (monomial m c) = if IsDiag m then monomial m c else 0 := by
  classical
  rw [diagHom, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v.1 = v.2 := by
      by_contra hne
      exact (Finsupp.mem_support_iff.1 hv) (h v hne)
    rw [if_pos this]
  · have : ∃ v, v.1 ≠ v.2 ∧ m v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h fun v hv => by_contra fun h0 => h0 (hc v hv)
    obtain ⟨v, hv, hmv⟩ := this
    rw [Finsupp.prod, Finset.prod_eq_zero (i := v) (Finsupp.mem_support_iff.2 hmv), mul_zero]
    rw [if_neg hv, zero_pow hmv]

theorem coeff_diagHom {N : ℕ} (f : MvPolynomial (Fin N × Fin N) ℚ) (m : Fin N × Fin N →₀ ℕ)
    (hm : IsDiag m) : AddMonoidAlgebra.coeff (diagHom N f) m = AddMonoidAlgebra.coeff f m := by
  classical
  refine MvPolynomial.induction_on' f (fun μ c => ?_) (fun p q hp hq => ?_)
  · rw [diagHom_monomial]
    split_ifs with h
    · rfl
    · rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, coeff_monomial, if_neg]
      rintro rfl
      exact h hm
  · rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

def diagMono {N : ℕ} (s : ℕ) (h : s ≤ N) : Fin N × Fin N →₀ ℕ :=
  ∑ p : Fin s, Finsupp.single (Fin.castLE h p, Fin.castLE h p) 1

theorem diagHom_lpMinor {N : ℕ} (s : ℕ) (hr hn : s ≤ N) :
    diagHom N (lpMinor ℚ s hr hn) = monomial (diagMono s hr) 1 := by
  classical
  rw [lpMinor, AlgHom.map_det]
  have hM : (diagHom N).mapMatrix
      (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin N × Fin N) ℚ)) =
      Matrix.diagonal fun p : Fin s => (X (Fin.castLE hr p, Fin.castLE hr p) : MvPolynomial (Fin N × Fin N) ℚ) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      simp [diagHom]
    · have : ¬ (Fin.castLE hr p = Fin.castLE hn q) := by
        intro h
        apply hpq
        exact Fin.ext (by simpa [Fin.ext_iff] using h)
      simp [diagHom, hpq, this]
  rw [hM, Matrix.det_diagonal, diagMono, monomial_sum_one]
  rfl

def M0 {N : ℕ} (ν : Fin N → ℕ) : Fin N × Fin N →₀ ℕ :=
  ∑ s : Fin N, (ν s - nuNext ν s) • diagMono (s.val + 1) s.isLt

theorem diagHom_hw {N : ℕ} (ν : Fin N → ℕ) :
    diagHom N (hw ℚ le_rfl ν) = monomial (M0 ν) 1 := by
  classical
  rw [hw, map_prod, M0, monomial_sum_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, diagHom_lpMinor, monomial_pow, one_pow]

theorem isDiag_diagonal_monomial {N : ℕ} (ν : Fin N → ℕ) : IsDiag (M0 ν) := by
  classical
  intro v hv
  simp only [M0, diagMono, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro p _
  rw [Finsupp.single_apply, if_neg]
  intro h
  subst h
  exact hv rfl

theorem coeff_diagonal_monomial_hw {N : ℕ} (ν : Fin N → ℕ) : AddMonoidAlgebra.coeff (hw ℚ le_rfl ν) (M0 ν) = 1 := by
  rw [← coeff_diagHom _ _ (isDiag_diagonal_monomial ν), diagHom_hw, coeff_monomial, if_pos rfl]

theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) m) a = ∑ b : Fin N, m (a, b) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [Pi.smul_apply, rowW, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem diagonal_monomial_apply {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) (a : Fin N) : M0 ν (a, a) = ν a := by
  classical
  have hmem : AddMonoidAlgebra.coeff (hw ℚ le_rfl ν) (M0 ν) ≠ 0 := by rw [coeff_diagonal_monomial_hw]; exact one_ne_zero
  have hw8 := hwRowWeight ℚ N N le_rfl ν hν hmem
  have h1 := congrFun hw8 a
  rw [weight_rowW_apply, Finset.sum_eq_single a] at h1
  · rw [h1]
    simp [rowNu]
  · intro b _ hb
    exact isDiag_diagonal_monomial ν (a, b) (Ne.symm hb)
  · simp

theorem diagonal_monomial_factorial {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    (∏ k ∈ (M0 ν).support, ((M0 ν) k).factorial) = ∏ l, (ν l).factorial := by
  classical
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.1 hk]; rfl)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single a]
  · rw [diagonal_monomial_apply ν hν a]
  · intro b _ hb
    rw [isDiag_diagonal_monomial ν (a, b) (Ne.symm hb)]
    rfl
  · simp

theorem fockQ_hw_ge {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    (∏ l, ((ν l).factorial : ℚ)) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  classical
  have hmem : M0 ν ∈ (hw ℚ le_rfl ν).support := by
    rw [mem_support_iff, coeff_diagonal_monomial_hw]; exact one_ne_zero
  unfold fockQ
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun m =>
      AddMonoidAlgebra.coeff (hw ℚ le_rfl ν) m * AddMonoidAlgebra.coeff (hw ℚ le_rfl ν) m *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ))
    (fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)) hmem)
  simp only [coeff_diagonal_monomial_hw, one_mul]
  rw [diagonal_monomial_factorial ν hν]
  push_cast
  rfl

theorem one_le_cNu {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) : 1 ≤ PI.cNu ν := by
  have h := fockQ_hw_ge ν hν
  have hpos : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
  have h' : (∏ l, ((ν l).factorial : ℝ)) ≤ ((fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℚ) : ℝ) := by
    exact_mod_cast h
  unfold PI.cNu
  rw [one_le_div hpos]
  exact h'

end PI.HookLower
end
end

section

noncomputable section

namespace PI.HookSteps.Cap

open Finset

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

theorem xw_succ (x : I → S → 𝒰) {k : ℕ} (r : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    xw x r s = x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
  unfold xw
  rw [List.ofFn_succ, List.prod_cons]

theorem dw_succ (d : I → S → 𝒰) {k : ℕ} (g : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    dw d g s = d (g 0) (s 0) * dw d (fun i => g i.succ) (fun i => s i.succ) := by
  unfold dw
  rw [List.ofFn_succ, List.prod_cons]

theorem xw_zero (x : I → S → 𝒰) (r : Fin 0 → I) (s : Fin 0 → S) : xw x r s = 1 := by
  unfold xw
  simp

theorem sum_fun_succ {M : Type} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → S) → M) :
    ∑ s, f s = ∑ t : S, ∑ s : Fin k → S, f (Fin.cons t s) := by
  rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
  rfl

theorem dx_key (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) :
    ∀ (k : ℕ) (r : Fin k → I) (s : Fin k → S) (a b : I) (t : S),
      x a t * (d b t * xw x r s) = x a t * xw x r s * d b t +
        ∑ j, if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0 := by
  intro k
  induction k with
  | zero =>
    intro r s a b t
    simp [xw_zero]
  | succ k ih =>
    intro r s a b t
    have h1 : xw x (Function.update r 0 a) s =
        x a (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
      have hf : (fun i : Fin k => Function.update r 0 a i.succ) = fun i => r i.succ :=
        funext fun i => by rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]
      rw [xw_succ, hf, Function.update_apply, if_pos rfl]
    have h2 : ∀ j : Fin k, xw x (Function.update r j.succ a) s =
        x (r 0) (s 0) * xw x (Function.update (fun i => r i.succ) j a) (fun i => s i.succ) := by
      intro j
      have hf : (fun i : Fin k => Function.update r j.succ a i.succ) =
          Function.update (fun i => r i.succ) j a :=
        Function.update_comp_eq_of_injective r (Fin.succ_injective k) j a
      rw [xw_succ, hf, Function.update_apply, if_neg (Fin.succ_ne_zero j).symm]
    have key : x a t * (x (r 0) (s 0) * (d b t * xw x (fun i => r i.succ) (fun i => s i.succ))) =
        x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) +
        ∑ j : Fin k, if r j.succ = b ∧ s j.succ = t then
          xw x (Function.update r j.succ a) s else 0 := by
      rw [← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih, mul_add,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2 j, mul_ite, mul_zero]
    have c0 : x a t * ((if r 0 = b ∧ s 0 = t then (1 : 𝒰) else 0) *
        xw x (fun i => r i.succ) (fun i => s i.succ)) =
        if r 0 = b ∧ s 0 = t then xw x (Function.update r 0 a) s else 0 := by
      split_ifs with h
      · rw [h1, h.2, one_mul]
      · rw [zero_mul, mul_zero]
    have m : x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) =
        x a t * (x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ)) * d b t := by
      simp only [mul_assoc]
      rw [← mul_assoc, hxx (r 0) (s 0) a t, mul_assoc]
    rw [xw_succ x r s, Fin.sum_univ_succ, ← c0, ← mul_assoc (d b t), hdx (r 0) (s 0) b t,
      add_mul, mul_add, mul_assoc (x (r 0) (s 0)) (d b t), key, m]
    abel

theorem E_Pn (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (r g : Fin k → I) (a b : I) :
    Eop x d a b * Pn x d r g = Pn x d (Fin.cons a r) (Fin.cons b g) +
      ∑ j, if r j = b then Pn x d (Function.update r j a) g else 0 := by
  have first : Pn x d (Fin.cons a r) (Fin.cons b g) =
      ∑ t, ∑ s : Fin k → S, x a t * xw x r s * (d b t * dw d g s) := by
    unfold Pn
    rw [sum_fun_succ]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    rw [xw_succ, dw_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_assoc]
  have second : ∀ j : Fin k, (if r j = b then Pn x d (Function.update r j a) g else 0) =
      ∑ t, ∑ s : Fin k → S,
        (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s := by
    intro j
    rw [Finset.sum_comm]
    unfold Pn
    split_ifs with h
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp [h]
    · simp [h]
  have term : ∀ (t : S) (s : Fin k → S), x a t * d b t * (xw x r s * dw d g s) =
      x a t * xw x r s * (d b t * dw d g s) +
      ∑ j, (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s := by
    intro t s
    rw [mul_assoc (x a t), ← mul_assoc (d b t), ← mul_assoc (x a t), dx_key x d hxx hdx k r s a b t,
      add_mul, Finset.sum_mul, mul_assoc (x a t * xw x r s)]
  rw [first]
  simp_rw [second]
  unfold Eop Pn
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, term, Finset.sum_add_distrib]
  congr 1
  exact (Finset.sum_congr rfl fun t _ => Finset.sum_comm).trans Finset.sum_comm

end PI.HookSteps.Cap
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

variable {N : ℕ}

theorem rowGen_coeff_zero (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    (rowGen ℚ a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on
  · next c =>
    simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add (f := _), Polynomial.coeff_add, hp, hq]
  · next p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    simp only [rowGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

theorem rowDiv_one_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    rowDiv ℚ a b 1 (p * X v) = rowDiv ℚ a b 1 p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have hX : rowGen ℚ a b (X v : MvPolynomial (Fin N × Fin N) ℚ) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
    simp only [rowGen, MvPolynomial.aeval_X]
  have h0 := rowGen_coeff_zero a b p
  simp only [rowDiv, map_mul, hX, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  split_ifs with h <;> simp [Polynomial.coeff_C, Polynomial.coeff_X_mul, add_comm]

theorem polE_apply (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    polE N a b f = ∑ s : Fin N, X (a, s) * pderiv (b, s) f := by
  simp [polE, LinearMap.sum_apply]

theorem polE_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    polE N a b (p * X v) = polE N a b p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have key : ∀ s : Fin N, X (a, s) * pderiv (b, s) (p * X v) =
      X (a, s) * pderiv (b, s) p * X v + p * (if v = (b, s) then X (a, s) else 0) := by
    intro s
    rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp only [smul_eq_mul] <;> ring
  have hs : (∑ s : Fin N, (if v = (b, s) then (X (a, s) : MvPolynomial (Fin N × Fin N) ℚ) else 0)) =
      if v.1 = b then X (a, v.2) else 0 := by
    obtain ⟨v1, v2⟩ := v
    by_cases h : v1 = b
    · subst h
      simp [Prod.ext_iff, eq_comm]
    · simp [h]
  rw [polE_apply, polE_apply, Finset.sum_mul]
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, hs]

theorem polynomial_eq_divisibility : PolEqRowDiv := by
  intro N a b f
  induction f using MvPolynomial.induction_on
  · next c =>
    rw [polE_apply]
    simp [rowDiv, rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add (f := _), hp, hq]
    simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]
  · next p v hp =>
    rw [polE_mul_X, rowDiv_one_mul_X, hp]

theorem fockQ_smul_right {σ : Type*} (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ f (c • g) = c * fockQ f g := by
  simp only [fockQ, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem determinant_shift_norm : DetShiftNormOf := by
  intro hAdj hDD hPol hHw N ν hν
  have hν' : Antitone (fun i : Fin N => ν i + 1) := fun a b hab => Nat.add_le_add_right (hν hab) 1
  have hG' := hHw N ν hν

  have heul : ∀ a : Fin N, rowDiv ℚ a a 1 (hw ℚ le_rfl (fun i => ν i + 1)) =
      (((ν a + 1 : ℕ) : ℚ)) • hw ℚ le_rfl (fun i => ν i + 1) := by
    intro a
    ext m
    rw [lgraded_coeff_euler, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : AddMonoidAlgebra.coeff (hw ℚ le_rfl (fun i : Fin N => ν i + 1)) m = 0
    · simp [hm]
    · have hW := hwRowWeight ℚ N N le_rfl _ hν' hm
      have hWa := congrFun hW a
      have hr : rowNu (r := N) (fun i : Fin N => ν i + 1) a = ν a + 1 := by
        simp [rowNu]
      rw [hr] at hWa
      congr 1
      rw [← hWa]
      norm_cast
      simp [Finsupp.weight_apply, Finsupp.sum, lgraded_wa, rowW, Pi.single_apply, eq_comm]
  have hcap := Formalism.CohomologicalDescent.HeightDescentMinors.c2_holds_alt ℚ (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
    (MvPolynomial (Fin N × Fin N) ℚ) N (polE N) ((N : ℚ) - 1) (fun i => ((ν i + 1 : ℕ) : ℚ))
    (hw ℚ le_rfl (fun i => ν i + 1))
    (fun i j hij => by
      rw [Module.End.smul_def, hPol]
      exact hwRaise ℚ N N le_rfl _ i j 1 hij le_rfl)
    (fun i => by rw [Module.End.smul_def, hPol, heul])
  rw [← hDD N, Module.End.smul_def, Module.End.mul_apply, LinearMap.mulLeft_apply] at hcap
  have hdet0 : detX N ≠ 0 := by
    intro h0
    have h1 := hHw N (fun _ => 0) (fun _ _ _ => le_rfl)
    rw [h0, zero_mul] at h1
    exact hwNe ℚ N N le_rfl _ h1
  have hD : detD N (detX N * hw ℚ le_rfl ν) =
      (∏ i : Fin N, ((N : ℚ) - 1 + ((ν i + 1 : ℕ) : ℚ) - ((i : ℕ) : ℚ))) • hw ℚ le_rfl ν := by
    apply mul_left_cancel₀ hdet0
    rw [← hG', hcap, hG', mul_smul_comm]
  rw [hAdj N (hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν), hD, fockQ_smul_right]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ ν i + N := by omega
  rw [Nat.cast_sub hi]
  push_cast
  ring

end PI.HookSteps
end
end
