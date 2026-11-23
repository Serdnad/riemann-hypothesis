module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  unfold mom
  rw [← integral_add (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp [evX, add_mul]

theorem mom_C_mul (c : ℝ) (a : ℂ) (P : PX m n) : mom c (C a * P) = a * mom c P := by
  unfold mom
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [evX, mul_assoc]

theorem mom_sub (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P - Q) = mom c P - mom c Q := by
  unfold mom
  rw [← integral_sub (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp [evX, sub_mul]

theorem mom_sum (c : ℝ) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    mom c (∑ i ∈ s, f i) = ∑ i ∈ s, mom c (f i) := by
  unfold mom
  rw [← MeasureTheory.integral_finsetSum s (fun i _ => integrable_pg c hc (f i))]
  congr 1
  funext x
  simp [evX, Finset.sum_mul]

theorem pderiv_Sg (c : ℝ) (k : Fin m × Fin n × Bool) :
    pderiv k (Sg c : PX m n) = C (-(c : ℂ)) * X (k.1, k.2.1, !k.2.2) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [Sg, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_comm, ite_and,
    Finset.sum_ite_eq', Finset.sum_ite_eq]

def Qv (c : ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) : PX m n :=
  ∑ k, C (crd k v) * (pderiv k P + P * pderiv k (Sg c))

theorem hasFDerivAt_pg (c : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => evX P y * gs c y) (evX P x • (gs c x • dP (Sg c) x) + gs c x • dP P x) x := by
  have hg : HasFDerivAt (fun y : Fin m → Fin n → ℂ => gs c y) (gs c x • dP (Sg c) x) x := by
    have h := (hasFDerivAt_evX (Sg c) x).cexp
    have he : (fun y : Fin m → Fin n → ℂ => gs c y) = fun y => Complex.exp (evX (Sg c) y) :=
      funext (gs_eq c)
    rw [he, gs_eq]
    exact h
  exact (hasFDerivAt_evX P x).mul hg

theorem fderiv_pg (c : ℝ) (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    fderiv ℝ (fun y => evX P y * gs c y) x v = evX (Qv c P v) x * gs c x := by
  rw [(hasFDerivAt_pg c P x).fderiv]

  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dP,
  ContinuousLinearMap.sum_apply, smul_eq_mul, Qv, evX, map_sum, map_add, map_mul, eval_C]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem integral_fderiv_pg (c : ℝ) (hc : 0 < c) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    mom c (Qv c P v) = 0 := by
  unfold mom
  have e : (fun x => evX (Qv c P v) x * gs c x) =
      fun x => (1 : ℂ) * fderiv ℝ (fun y => evX P y * gs c y) x v := by
    funext x
    rw [fderiv_pg, one_mul]
  rw [e, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  · simp
  · simp
  · simpa [fderiv_pg] using integrable_pg c hc (Qv c P v)
  · simpa using integrable_pg c hc P
  · intro x _
    exact differentiableAt_const _
  · intro x _
    exact (hasFDerivAt_pg c P x).differentiableAt

def ev1 (k : Fin m × Fin n × Bool) (z : ℂ) : Fin m → Fin n → ℂ := fun a i => if a = k.1 ∧ i = k.2.1 then z else 0

theorem null_operator_evaluation (c : ℝ) (P : PX m n) (k : Fin m × Fin n × Bool) (z : ℂ) :
    Qv c P (ev1 k z) = C z * (pderiv (k.1, k.2.1, false) P + P * pderiv (k.1, k.2.1, false) (Sg c)) +
      C (star z) * (pderiv (k.1, k.2.1, true) P + P * pderiv (k.1, k.2.1, true) (Sg c)) := by
  obtain ⟨a, i, b⟩ := k
  unfold Qv
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Fintype.sum_prod_type, Finset.sum_eq_single i,
    Fintype.sum_bool]
  · simp [crd_apply, ev1, add_comm]
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp

theorem mom_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (P : PX m n) :
    mom c (pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P) = 0 := by
  obtain ⟨a, i, b⟩ := k
  have h1 := integral_fderiv_pg c hc P (ev1 (a, i, b) 1)
  have h2 := integral_fderiv_pg c hc P (ev1 (a, i, b) Complex.I)
  rw [null_operator_evaluation, mom_add c hc, mom_C_mul, mom_C_mul] at h1 h2
  simp only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 h2
  have hu : mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
    have h3 : 2 * Complex.I * mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
      linear_combination h2 + Complex.I * h1
    simpa [Complex.I_ne_zero] using h3
  have hw : mom c (pderiv (a, i, true) P + P * pderiv (a, i, true) (Sg c)) = 0 := by
    linear_combination h1 - hu
  have key : pderiv (a, i, b) P - C (c : ℂ) * X (a, i, !b) * P =
      pderiv (a, i, b) P + P * pderiv (a, i, b) (Sg c) := by
    rw [pderiv_Sg, map_neg]
    ring
  rw [key]
  cases b
  · exact hu
  · exact hw

end PositivityTheory.Rg.Sw.LC.NullS
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool

abbrev Dk (k : Ix m n) : Module.End ℂ (PX m n) := (pderiv (R := ℂ) k).toLinearMap

theorem pderiv_comm (i j : Ix m n) (p : PX m n) : pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have hc : ∀ a b : Ix m n, pderiv a (pderiv b (X k : PX m n)) = 0 := by
      intro a b; rw [pderiv_X]; by_cases h : b = k
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [pderiv_mul, map_add (f := _), hp, hc, mul_zero, add_zero]
    ring

theorem dk_comm (i j : Ix m n) : Commute (Dk i) (Dk j) :=
  LinearMap.ext fun p => pderiv_comm i j p

def dvE (e : Ix m n → ℕ) : Module.End ℂ (PX m n) :=
  ((Finset.univ : Finset (Ix m n)).toList.map fun k => Dk k ^ e k).prod

theorem list_dv_mul (l : List (Ix m n)) (a b : Ix m n → ℕ) :
    (l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod = (l.map fun k => Dk k ^ (a k + b k)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hc : Commute (l.map fun k => Dk k ^ a k).prod (Dk x ^ b x) := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨z, -, rfl⟩ := hy
      exact ((dk_comm x z).pow_pow _ _)
    calc Dk x ^ a x * (l.map fun k => Dk k ^ a k).prod * (Dk x ^ b x * (l.map fun k => Dk k ^ b k).prod)
        = Dk x ^ a x * ((l.map fun k => Dk k ^ a k).prod * Dk x ^ b x) * (l.map fun k => Dk k ^ b k).prod := by
          simp only [mul_assoc]
      _ = Dk x ^ a x * (Dk x ^ b x * (l.map fun k => Dk k ^ a k).prod) * (l.map fun k => Dk k ^ b k).prod := by
          rw [hc.eq]
      _ = Dk x ^ (a x + b x) * ((l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod) := by
          simp only [pow_add, mul_assoc]
      _ = _ := by rw [ih]

theorem dvE_mul (a b : Ix m n → ℕ) : dvE a * dvE b = dvE (a + b) := by
  unfold dvE; rw [list_dv_mul]; rfl

theorem dvE_single (k : Ix m n) : dvE (Pi.single k 1) = Dk k := by
  unfold dvE
  rw [List.prod_map_eq_pow_single k]
  · simp only [Pi.single_eq_same, pow_one]
    convert pow_one (Dk k)
    exact @List.count_eq_one_of_mem _ instBEqOfDecidableEq inferInstance _ _ (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ k))
  · intro a' ha' _
    simp [Pi.single_apply, ha']

theorem opMono_eq (t : Ix m n ⊕ Ix m n →₀ ℕ) (f : PX m n) :
    opMono t f = monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 * dvE (fun k => t (Sum.inr k)) f := rfl

theorem opMono_add (t : Ix m n ⊕ Ix m n →₀ ℕ) (f g : PX m n) : opMono t (f + g) = opMono t f + opMono t g := by
  simp only [opMono_eq, map_add (f := _), mul_add]

theorem opMono_smul (t : Ix m n ⊕ Ix m n →₀ ℕ) (a : ℂ) (f : PX m n) : opMono t (a • f) = a • opMono t f := by
  simp only [opMono_eq, map_smul, mul_smul_comm]

theorem op_eq_of_subset (s : Sym m n) (S : Finset (Ix m n ⊕ Ix m n →₀ ℕ)) (h : s.support ⊆ S) (f : PX m n) :
    op s f = ∑ t ∈ S, s.coeff t • opMono t f := by
  unfold op
  apply Finset.sum_subset h
  intro t _ ht
  rw [MvPolynomial.notMem_support_iff.1 ht, zero_smul]

theorem op_add (u v : Sym m n) (f : PX m n) : op (u + v) f = op u f + op v f := by
  classical
  rw [op_eq_of_subset (u + v) (u.support ∪ v.support) MvPolynomial.support_add,
    op_eq_of_subset u (u.support ∪ v.support) Finset.subset_union_left,
    op_eq_of_subset v (u.support ∪ v.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [MvPolynomial.coeff_add, add_smul]

theorem op_smul (a : ℂ) (u : Sym m n) (f : PX m n) : op (a • u) f = a • op u f := by
  classical
  rw [op_eq_of_subset (a • u) u.support MvPolynomial.support_smul, op, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

theorem op_zero (f : PX m n) : op (0 : Sym m n) f = 0 := by simp [op]

theorem op_sum {ι : Type*} (S : Finset ι) (u : ι → Sym m n) (f : PX m n) : op (∑ i ∈ S, u i) f = ∑ i ∈ S, op (u i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]

theorem op_monomial (t : Ix m n ⊕ Ix m n →₀ ℕ) (a : ℂ) (f : PX m n) : op (monomial t a) f = a • opMono t f := by
  classical
  rw [op_eq_of_subset _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem op_add_f (u : Sym m n) (f g : PX m n) : op u (f + g) = op u f + op u g := by
  simp only [op, opMono_add, smul_add, Finset.sum_add_distrib]

theorem op_smul_f (u : Sym m n) (a : ℂ) (f : PX m n) : op u (a • f) = a • op u f := by
  simp only [op, opMono_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_comm]

theorem op_zero_f (u : Sym m n) : op u 0 = 0 := by simp [op, opMono_eq]

theorem dvE_zero : dvE (0 : Ix m n → ℕ) = 1 := by
  unfold dvE; simp

theorem op_C (a : ℂ) (f : PX m n) : op (C a : Sym m n) f = a • f := by
  rw [← monomial_zero', op_monomial, opMono_eq]
  have h0 : (fun k : Ix m n => (0 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) = 0 := by ext; simp
  rw [h0, dvE_zero, Finsupp.comapDomain_zero]
  simp

theorem comapDomain_inl_add (t s : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t + s).comapDomain Sum.inl Sum.inl_injective.injOn =
      t.comapDomain Sum.inl Sum.inl_injective.injOn + s.comapDomain Sum.inl Sum.inl_injective.injOn := by
  ext k; simp [Finsupp.comapDomain_apply]

theorem opMono_add_inl (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inl k) 1) f = X k * opMono t f := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inl k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn =
      Finsupp.single k 1 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inl k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) = fun j => t (Sum.inr j) := by
    ext j; simp [Finsupp.single_apply]
  rw [h1, h2, monomial_add_single, pow_one]
  ring

theorem opMono_add_inr (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inr k) 1) f = opMono t (pderiv k f) := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) =
      (fun j => t (Sum.inr j)) + Pi.single k 1 := by
    ext j; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [h1, add_zero, h2, ← dvE_mul, dvE_single]
  rfl

theorem op_mul_inl (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inl k)) f = X k * op u f := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inl, mul_smul_comm]

theorem op_mul_inr (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inr k)) f = op u (pderiv k f) := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inr]

theorem op_X_mul (u : Sym m n) : ∀ (k : Ix m n) (g : PX m n),
    op u (X k * g) = X k * op u g + op (pderiv (Sum.inr k) u) g := by
  induction u using MvPolynomial.induction_on with
  | C a => intro k g; simp [op_C, op_zero, mul_smul_comm]
  | add p q hp hq => intro k g; rw [op_add, op_add, hp, hq, map_add (f := _), op_add]; ring
  | mul_X p j hp =>
    intro k g
    rcases j with j | j
    · rw [op_mul_inl, op_mul_inl, hp, pderiv_mul, pderiv_X, op_add, op_mul_inl]
      simp only [Pi.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, mul_zero, op_zero, add_zero]
      ring
    · rw [op_mul_inr, op_mul_inr, pderiv_mul, pderiv_mul, pderiv_X, pderiv_X, op_add_f, op_add, hp, op_mul_inr]
      by_cases h : j = k
      · subst h
        simp only [Pi.single_apply, if_true, mul_one, one_mul]
        ring
      · have h' : (Sum.inr k : Ix m n ⊕ Ix m n) ≠ Sum.inr j := fun e => h (Sum.inr_injective e).symm
        have e1 : ¬ (k = j) := fun e => h e.symm
        have e2 : ¬ ((Sum.inr j : Ix m n ⊕ Ix m n) = Sum.inr k) := fun e => h (Sum.inr_injective e)
        simp only [Pi.single_apply, e1, e2, if_false, zero_mul, mul_zero, op_zero, add_zero, op_zero_f, zero_add]

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def cw (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  if ∀ a i, s (a, i, false) = s (a, i, true) then
    ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

theorem contr_eq_sum (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * cw c s := by
  unfold contr cw
  rw [← Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · intro s _ hs
    rw [MvPolynomial.notMem_support_iff.mp hs]
    simp

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_sum c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_sum c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_sum c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eq_sum c (r • p) p.support (support_smul), contr_eq_sum c p p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

def contrL (c : ℝ) : PX m n →ₗ[ℂ] ℂ where
  toFun := contr c
  map_add' := contr_add c
  map_smul' := contr_smul c

theorem fform_eq_sum (c : ℝ) (p q : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ∪ q.support ⊆ S) :
    fform c p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * (wt c s : ℂ) := by
  unfold fform
  rw [← Finset.sum_subset hS]
  intro s _ hs
  have h1 : p.coeff s = 0 := MvPolynomial.notMem_support_iff.mp fun h => hs (Finset.mem_union_left _ h)
  simp [h1]

theorem fform_add_right (c : ℝ) (p q₁ q₂ : PX m n) : fform c p (q₁ + q₂) = fform c p q₁ + fform c p q₂ := by
  classical
  set S := p.support ∪ q₁.support ∪ q₂.support
  rw [fform_eq_sum c p (q₁ + q₂) S (Finset.union_subset (by intro x hx; simp [S, hx]) (fun x hx => by
      have := support_add hx; simp only [S, Finset.mem_union] at this ⊢; tauto)),
    fform_eq_sum c p q₁ S (Finset.union_subset (by intro x hx; simp [S, hx]) (by intro x hx; simp [S, hx])),
    fform_eq_sum c p q₂ S (Finset.union_subset (by intro x hx; simp [S, hx]) (by intro x hx; simp [S, hx])),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fform_smul_right (c : ℝ) (p q : PX m n) (r : ℂ) : fform c p (r • q) = r * fform c p q := by
  classical
  rw [fform_eq_sum c p (r • q) (p.support ∪ q.support) (Finset.union_subset Finset.subset_union_left
      (support_smul.trans Finset.subset_union_right)),
    fform_eq_sum c p q (p.support ∪ q.support) le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

end PositivityTheory.Rg.Sw.LC.Core
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def EtaLt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) < N

def EtaLe (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) ≤ N

def vecVar (ε : Fin m → Bool) (a : Fin m) (i : Fin n) : Sym m n :=
  if ε a then X (Sum.inl (a, i, false)) else X (Sum.inr (a, i, true))

def covVar (ε : Fin m → Bool) (b : Fin m) (i : Fin n) : Sym m n :=
  if ε b then X (Sum.inr (b, i, false)) else X (Sum.inl (b, i, true))

def pairSym (ε : Fin m → Bool) (a b : Fin m) : Sym m n := ∑ i, vecVar ε a i * covVar ε b i

def CompSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (u v : Sym m n) (d₁ d₂ : ℕ), SymbolInFirstFamily ε u → SymbolInFirstFamily ε v → EtaLe u d₁ → EtaLe v d₂ →
    ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r (d₁ + d₂) ∧ ∀ f, op u (op v f) = op (u * v) f + op r f

def FFTSym : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    s ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => (pairSym (n := n) ε ab.1 ab.2))

end PositivityTheory.Rg.Sw.LC
end
end
