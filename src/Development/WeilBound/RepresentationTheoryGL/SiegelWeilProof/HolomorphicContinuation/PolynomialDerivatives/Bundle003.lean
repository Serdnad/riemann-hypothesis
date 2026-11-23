module

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Derivation.Lie
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def Sg (c : ℝ) : PX m n := C (-(c : ℂ)) * ∑ a, ∑ i, X (a, i, true) * X (a, i, false)

theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = Complex.exp (evX (Sg c) x) := by
  unfold gs
  congr 1

  simp only [Sg, evX_eq, map_mul, map_sum, eval_C, eval_X, crd_apply, if_true, Bool.false_eq_true, if_false,
  Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

theorem evX_bound (P : PX m n) : ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ x, ‖evX P x‖ ≤ K * (1 + ‖x‖) ^ d := by
  apply PositivityTheory.Rg.Sw.AbsSt.DF.poly_bound <;> assumption

theorem sq_norm_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le x

theorem norm_gs_le (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [show (-(↑(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℂ)) = ↑(-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp_ofReal]
  apply Real.exp_le_exp.2
  have := sq_norm_le x
  nlinarith

theorem poly_exp_bound (c : ℝ) (hc : 0 < c) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * ((N.factorial : ℝ) / (2 * c) ^ N) := by
  set y := 2 * c * (1 + t) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * Real.exp (-y) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (t - 1)]
  have h2 : (1 + t) ^ N * Real.exp (-y) ≤ (N.factorial : ℝ) / (2 * c) ^ N := by
    have := Real.pow_div_factorial_le_exp y hy0 N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have hyN : y ^ N = (2 * c) ^ N * (1 + t) ^ N := by rw [hy, mul_pow]
    calc (1 + t) ^ N * Real.exp (-y) * (2 * c) ^ N = y ^ N * Real.exp (-y) := by rw [hyN]; ring
      _ ≤ (Real.exp y * N.factorial) * Real.exp (-y) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = N.factorial := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add]; simp
  calc (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ (1 + t) ^ N * (Real.exp (3 * c) * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (3 * c) * ((1 + t) ^ N * Real.exp (-y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

instance instHaarX : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]; exact Complex.continuous_exp.comp (continuous_evX _)

theorem integrable_pg (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  obtain ⟨K, d, hK, hb⟩ := evX_bound P
  set R : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hR
  set M := Real.exp (3 * c) * (((d + R).factorial : ℝ) / (2 * c) ^ (d + R)) with hM
  have hcont : Continuous (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := (continuous_evX P).mul (continuous_gs c)
  refine ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume) (r := (R : ℝ)) (by simp [hR])).const_mul
    (K * M)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hpos : 0 < (1 + ‖x‖) ^ R := by positivity
  have key := poly_exp_bound c hc (d + R) ‖x‖ ht
  rw [norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (K * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hb x) (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖x‖) ^ (d + R) * Real.exp (-(c * ‖x‖ ^ 2))) / (1 + ‖x‖) ^ R := by
        rw [pow_add]; field_simp
    _ ≤ K * M / (1 + ‖x‖) ^ R := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left key hK
    _ = K * M * ((1 + ‖x‖) ^ R)⁻¹ := by rw [div_eq_mul_inv]

end PositivityTheory.Rg.Sw.LC.NullS
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hC (c : ℝ) (p q : ℕ) : ℂ := if p = q then (p.factorial : ℂ) * (2 * c : ℂ) ^ p else 0

def wC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))

theorem hC_comm (c : ℝ) (p q : ℕ) : hC c p q = hC c q p := by
  unfold hC; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem hC_rel (c : ℝ) (p q : ℕ) : hC c (p + 1) q = (2 * c : ℂ) * (q : ℂ) * hC c p (q - 1) := by
  rcases q with _ | q
  · simp [hC]
  · simp only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rw [Nat.factorial_succ]; push_cast; ring
    · simp

theorem contr_eq (c : ℝ) (p : PX m n) : contr c p = ∑ s ∈ p.support, p.coeff s * wC c s := by
  unfold contr wC
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) =
      if ∀ a i, s (a, i, false) = s (a, i, true) then
        ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0 := by
    simp only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [this]
  split_ifs <;> simp

theorem contr_eq_of_subset (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * wC c s := by
  rw [contr_eq]
  refine Finset.sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, zero_mul]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem contr_monomial (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) : contr c (monomial s r) = r * wC c s := by
  classical
  rw [contr_eq_of_subset c _ {s} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem contr_C (c : ℝ) (r : ℂ) : contr c (C r : PX m n) = r := by
  rw [← monomial_zero', contr_monomial]
  simp [wC, hC]

theorem wC_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    wC c s = hC c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold wC
  rw [← Fintype.prod_prod_type' (f := fun a i => hC c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem wC_rel (c : ℝ) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    wC c (Finsupp.single k 1 + u) = (2 * c : ℂ) * (u (flip k) : ℂ) * wC c (u - Finsupp.single (flip k) 1) := by
  obtain ⟨a, i, b⟩ := k
  rw [wC_split c _ a i, wC_split c _ a i]
  have hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_erase.1 hx).1
    have key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') := by
      intro b'
      have h1 : (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp at this; exact this.symm)
      have h2 : flip (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp [flip] at this; exact this.symm)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg h1, if_neg h2, tsub_zero, zero_add]
    rw [key false, key true]
  rw [hrest, ← mul_assoc]
  congr 1
  have e1 : (a, i, true) ≠ (a, i, false) := by simp
  cases b
  · simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact hC_rel c _ _
  · simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]
    exact hC_rel c _ _

theorem contr_X_mul (c : ℝ) (k : Fin m × Fin n × Bool) (p : PX m n) :
    contr c (X k * p) = (2 * c : ℂ) * contr c (pderiv (flip k) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X k : PX m n) * monomial u r = monomial (Finsupp.single k 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [hX, pderiv_monomial, contr_monomial, contr_monomial, wC_rel]
    ring
  | add P Q hP hQ => rw [mul_add, contr_add, hP, hQ, map_add (f := _), contr_add, mul_add]

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def FockBasic : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → IsLinearMap ℂ (fock (m := m) (n := n) c) ∧ Function.Bijective (fock (m := m) (n := n) c) ∧
    ∀ k (p : PX m n), fock c (X k * p) = cr c k (fock c p)

def FockHOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (a b : Fin m) (p : PX m n),
    hOp ε c a b (fock c p) = fock c (Dop ε c a b p)

def FockMom : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → mom (m := m) (n := n) c 1 ≠ 0 ∧ ∀ p : PX m n, mom c (fock c p) = mom c (1 : PX m n) * contr c p

def NullStable : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (i j : Fin n) (P : PX m n), NullSec ε c P →
    NullSec ε c (lapS ε c i j P) ∧ NullSec ε c (eulH c i j P) ∧ NullSec ε c (eulA c i j P) ∧ NullSec ε c (mulQ ε i j P)

def FockK : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∃ a₁ a₂ a₃ a₄ a₅ : ℂ, ∀ (i j : Fin n) (p : PX m n),
    fock c (KopL ε i j p) = a₁ • mulQ ε i j (fock c p) + a₂ • lapS ε c i j (fock c p) + a₃ • eulH c i j (fock c p) +
      a₄ • eulA c i j (fock c p) + (if i = j then a₅ else 0) • fock c p

def CoreLC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ Λ : PX m n →ₗ[ℂ] ℂ, (∀ a b p, Λ (Dop ε c a b p) = 0) →
    ∀ p, ∃ w ∈ kAlg ε, Λ p = contr c (w p)

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gaussian_moment_symm (c : ℝ) (p q : ℕ) : g1 c p q = g1 c q p := by
  unfold g1; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem gaussian_moment_recurrence (c : ℝ) (hc : 0 < c) (p q : ℕ) : (p : ℂ) * g1 c (p - 1) q = (c : ℂ) * g1 c p (q + 1) := by
  rcases p with _ | p
  · simp [g1]
  · simp only [Nat.add_sub_cancel, g1, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp

theorem phi_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    phi c s = g1 c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold phi
  rw [← Fintype.prod_prod_type' (f := fun a i => g1 c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem rest_congr (c : ℝ) (s s' : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n)
    (h : ∀ x : Fin m × Fin n, x ≠ (a, i) → ∀ b, s (x.1, x.2, b) = s' (x.1, x.2, b)) :
    ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s' (x.1, x.2, false)) (s' (x.1, x.2, true)) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' := (Finset.mem_erase.1 hx).1
  rw [h x hx' false, h x hx' true]

theorem phi_rel (c : ℝ) (hc : 0 < c) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (u k : ℂ) * phi c (u - Finsupp.single k 1) = (c : ℂ) * phi c (Finsupp.single (flip k) 1 + u) := by
  obtain ⟨a, i, b⟩ := k
  rw [phi_split c _ a i, phi_split c _ a i,
    rest_congr c (u - Finsupp.single (a, i, b) 1) (Finsupp.single (flip (a, i, b)) 1 + u) a i (fun x hx b' => by
      have h1 : (x.1, x.2, b') ≠ (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa using this)
      have h2 : (x.1, x.2, b') ≠ flip (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa [flip] using this)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm h1), if_neg (Ne.symm h2), tsub_zero, zero_add])]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  cases b
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact gaussian_moment_recurrence c hc _ _
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [gaussian_moment_symm c _ (u (a, i, true) - 1), gaussian_moment_symm c (1 + u (a, i, false)), add_comm]
    exact gaussian_moment_recurrence c hc _ _

variable (hM : OneMom)


include hM in
theorem mom_pderiv (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X (flip k) : PX m n) * monomial u r = monomial (Finsupp.single (flip k) 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [pderiv_monomial, hX, mom_monomial hM c hc, mom_monomial hM c hc, mul_assoc, phi_rel c hc u k]
    ring
  | add P Q hP hQ => rw [map_add (f := _), mom_add hM c hc, hP, hQ, mul_add, mom_add hM c hc, mul_add]

theorem pderiv_comm (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (pderiv j Q) = pderiv j (pderiv k Q) := by
  have : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv j : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    classical
    rw [pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D Q) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.1 h

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -pderiv k Q + (2 * c : ℂ) • (X (flip k) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, flip]

theorem pderiv_cr (c : ℝ) (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + (if k = flip j then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm k j]
  by_cases h : k = flip j
  · subst h; simp [Pi.single_apply]; ring
  · simp [Pi.single_apply, h, Ne.symm h]

end PositivityTheory.Rg.Sw.LC
end
end
