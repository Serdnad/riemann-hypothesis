module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev QA (ε : Fin m → Bool) : Subalgebra ℂ (PX m n) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))

theorem sgn_mul_self (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem Qp_eq (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * (X (a, i, true) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgn; cases ε a <;> simp

theorem Qp_mem (ε : Fin m → Bool) (i j : Fin n) : (Qp ε i j : PX m n) ∈ QA ε :=
  Algebra.subset_adjoin ⟨(i, j), rfl⟩

theorem pd_Qp_f (ε : Fin m → Bool) (a : Fin m) (i k l : Fin n) :
    pderiv (a, i, false) (Qp ε k l : PX m n) = if l = i then C (sgn ε a) * X (a, k, true) else 0 := by
  rw [Qp_eq]

  simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : l = i <;> simp [h]

theorem partial_deriv_quadratic_pairing (ε : Fin m → Bool) (a : Fin m) (j k l : Fin n) :
    pderiv (a, j, true) (Qp ε k l : PX m n) = if k = j then C (sgn ε a) * X (a, l, false) else 0 := by
  rw [Qp_eq]

  simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : k = j <;> simp [h]

end PositivityTheory.Rg.Sw.LC.NullS
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def cr (c : ℝ) (k : Fin m × Fin n × Bool) : Module.End ℂ (PX m n) :=
  if k.2.2 then -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, false) : PX m n)
  else -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, true) : PX m n)

def fockMono (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (cr c k) ^ (s k)).prod) 1

def fock (c : ℝ) (p : PX m n) : PX m n := ∑ s ∈ p.support, p.coeff s • fockMono c s

def Dop (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    ∑ i, (X (b, i, true) * pderiv (a, i, true) p - X (a, i, false) * pderiv (b, i, false) p)
  else
    ∑ i, ((2 * c : ℂ) • pderiv (b, i, false) (pderiv (a, i, true) p) - (1 / (2 * c) : ℂ) • (X (a, i, false) * X (b, i, true) * p))

def contr (c : ℝ) (p : PX m n) : ℂ :=
  ∑ s ∈ p.support, if ∀ a i, s (a, i, false) = s (a, i, true) then
    p.coeff s * ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

def KopL (ε : Fin m → Bool) (i j : Fin n) : Module.End ℂ (PX m n) :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = true), LinearMap.mulLeft ℂ (X (a, i, false) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, j, false)).toLinearMap -
    ∑ a ∈ Finset.univ.filter (fun a => ε a = false), LinearMap.mulLeft ℂ (X (a, j, true) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, i, true)).toLinearMap

def mulQ (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) : PX m n := Qp ε i j * P

def lapS (ε : Fin m → Bool) (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, i, false) (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P) -
    C (c : ℂ) * X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P))

def eulH (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, j, false) * (pderiv (a, i, false) P - C (c : ℂ) * X (a, i, true) * P)

def eulA (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P)

def kAlg (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2)

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def MomLin : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (P Q : PX m n) (r : ℂ), mom c (P + Q) = mom c P + mom c Q ∧ mom c (r • P) = r * mom c P

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1))
  else (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1)

theorem crd_apply (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    crd k x = if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [Complex.conjCLE_apply, Complex.star_def]

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

theorem norm_crd_le (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ‖crd k x‖ ≤ ‖x‖ := by
  rw [crd_apply]
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  split_ifs <;> simpa using h

def dP (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ := ∑ k, evX (pderiv k P) x • crd k

theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (fun y => evX P y) (dP P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : dP (C a : PX m n) x = 0 := by simp [dP, evX_eq]
    have e : (fun y => evX (C a : PX m n) y) = fun _ => a := by funext y; simp [evX_eq]
    rw [this, e]; exact hasFDerivAt_const a x
  | add p q hp hq =>
    have : dP (p + q) x = dP p x + dP q x := by simp [dP, evX_eq, Finset.sum_add_distrib, add_smul]
    have e : (fun y => evX (p + q) y) = fun y => evX p y + evX q y := by funext y; simp [evX_eq]
    rw [this, e]; exact hp.add hq
  | mul_X p k hp =>
    have h1 : HasFDerivAt (fun y => evX p y * crd k y) (evX p x • crd k + crd k x • dP p x) x :=
      hp.mul (crd k).hasFDerivAt
    have e1 : (fun y => evX (p * X k) y) = fun y => evX p y * crd k y := by
      funext y; simp [evX_eq]
    have e2 : dP (p * X k) x = evX p x • crd k + crd k x • dP p x := by
      ext v
      have hb : ∀ b, evX (pderiv b (p * X k)) x * crd b v =
          crd k x * (evX (pderiv b p) x * crd b v) + (if k = b then evX p x * crd k v else 0) := by
        intro b
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : k = b
        · subst h; simp [evX_eq]; ring
        · simp [evX_eq, Pi.single_apply, Ne.symm h, h]; ring
      simp only [dP, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        ← Finset.mul_sum]
      ring
    rw [e1, e2]; exact h1

end PositivityTheory.Rg.Sw.LC.NullS
end
end

section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def flip (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

@[simp] theorem flip_flip (k : Fin m × Fin n × Bool) : flip (flip k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flip]

def g1 (c : ℝ) (p q : ℕ) : ℂ := if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

def phi (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, g1 c (s (a, i, false)) (s (a, i, true))

def fac (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) (z : ℂ) : ℂ :=
  z ^ s (a, i, false) * star z ^ s (a, i, true) * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))

theorem evX_monomial_mul_gs (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) (x : Fin m → Fin n → ℂ) :
    evX (monomial s r) x * gs c x = r * ∏ a, ∏ i, fac c s a i (x a i) := by
  have h1 : evX (monomial s r) x = r * ∏ a, ∏ i, (x a i ^ s (a, i, false) * star (x a i) ^ s (a, i, true)) := by
    rw [evX, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.prod_bool]
    simp [mul_comm]
  have h2 : gs c x = ∏ a, ∏ i, Complex.exp ((-(c * ‖x a i‖ ^ 2) : ℝ)) := by
    rw [gs, ← Complex.ofReal_neg]
    have : (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℝ) = ∑ a, ∑ i, (-(c * ‖x a i‖ ^ 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [this, Complex.ofReal_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Complex.ofReal_sum, Complex.exp_sum]
  rw [h1, h2, mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext a
  rw [← Finset.prod_mul_distrib]
  rfl

variable (hM : OneMom)

include hM in
theorem integrable_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX (monomial s r) x * gs c x) := by
  simp_rw [evX_monomial_mul_gs]
  refine Integrable.const_mul ?_ r
  exact Integrable.fintype_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))
    (fun a => Integrable.fintype_prod (f := fun i (z : ℂ) => fac c s a i z) (fun i => (hM c hc _ _).1))

include hM in
theorem mom_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    mom c (monomial s r) = r * phi c s := by
  rw [mom]
  simp_rw [evX_monomial_mul_gs]
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_volume_eq_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (z : ℂ) => fac c s a i z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (hM c hc _ _).2

include hM in
theorem integrable_evX (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s r => exact integrable_monomial hM c hc s r
  | add P Q hP hQ =>
    have : (fun x => evX (P + Q) x * gs c x) = fun x => evX P x * gs c x + evX Q x * gs c x := by
      funext x; simp [evX, add_mul]
    rw [this]; exact hP.add hQ

include hM in
theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  rw [mom, mom, mom, ← integral_add (integrable_evX hM c hc P) (integrable_evX hM c hc Q)]
  congr 1; funext x; simp [evX, add_mul]

omit hM in
theorem mom_smul (c : ℝ) (r : ℂ) (P : PX m n) : mom c (r • P) = r * mom c P := by
  rw [mom, mom, ← integral_const_mul]
  congr 1; funext x; simp [evX, mul_assoc]

end PositivityTheory.Rg.Sw.LC
end
end
