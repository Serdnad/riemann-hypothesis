module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Star.BigOperators

@[expose] public section

section

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev gl (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev U (n : ℕ) := UniversalEnvelopingAlgebra ℂ (gl n)

variable {n : ℕ}

def E (a : Fin n × Fin n) : gl n := Matrix.single a.1 a.2 1

noncomputable def e (a : Fin n × Fin n) : U n := UniversalEnvelopingAlgebra.ι ℂ (E a)

noncomputable def word (w : List (Fin n × Fin n)) : U n := (w.map e).prod

@[simp] theorem word_nil : word ([] : List (Fin n × Fin n)) = 1 := rfl

@[simp] theorem word_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    word (a :: w) = e a * word w := by
  simp [word]

@[simp] theorem word_append (v w : List (Fin n × Fin n)) : word (v ++ w) = word v * word w := by
  simp [word]

theorem word_singleton (a : Fin n × Fin n) : word [a] = e a := by simp

theorem E_mul_sub_mul (a b : Fin n × Fin n) :
    E a * E b - E b * E a =
      (if a.2 = b.1 then E (a.1, b.2) else 0) - (if b.2 = a.1 then E (b.1, a.2) else 0) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨k, l⟩ := b
  simp only [E]
  congr 1
  · by_cases h : j = k
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]
  · by_cases h : l = i
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]

theorem e_mul_sub_mul (a b : Fin n × Fin n) :
    e a * e b - e b * e a =
      (if a.2 = b.1 then e (a.1, b.2) else 0) - (if b.2 = a.1 then e (b.1, a.2) else 0) := by
  have h := congrArg (UniversalEnvelopingAlgebra.ι ℂ (L := gl n)) (E_mul_sub_mul a b)
  rw [← LieRing.of_associative_ring_bracket, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    at h
  simp only [e] at h ⊢
  rw [h, map_sub]
  congr 1 <;> split_ifs <;> simp

theorem eq_sum_E (X : gl n) : X = ∑ a : Fin n × Fin n, X a.1 a.2 • E a := by
  ext i j
  simp only [E, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem ι_eq_sum_e (X : gl n) :
    UniversalEnvelopingAlgebra.ι ℂ X = ∑ a : Fin n × Fin n, X a.1 a.2 • e (n := n) a := by
  conv_lhs => rw [eq_sum_E X]

  simp [e, map_sum, map_smul]

theorem U.induction {C : U n → Prop}
    (halg : ∀ r : ℂ, C (algebraMap ℂ _ r)) (hι : ∀ x, C (UniversalEnvelopingAlgebra.ι ℂ x))
    (hmul : ∀ a b, C a → C b → C (a * b)) (hadd : ∀ a b, C a → C b → C (a + b))
    (u : U n) : C u := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep u
  show C (UniversalEnvelopingAlgebra.mkAlgHom ℂ (gl n) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb

theorem mem_center_of_commute_e {z : U n} (hz : ∀ a, e a * z = z * e a) :
    z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  induction u using U.induction with
  | halg r => exact Algebra.commutes r z
  | hι X =>
    rw [ι_eq_sum_e, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, mul_smul_comm, hz]
  | hmul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | hadd a b ha hb => rw [add_mul, mul_add, ha, hb]

end GroundTheory.Automorphic.HarishChandra
end

section

namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial

variable {σ : Type*}

def mfact (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

theorem mfact_pos (m : σ →₀ ℕ) : 0 < mfact m :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem mfact_add_single [DecidableEq σ] (s : σ →₀ ℕ) (a : σ) :
    mfact (s + Finsupp.single a 1) = mfact s * (s a + 1) := by
  unfold mfact
  have h1 := Finsupp.mul_prod_erase' (s + Finsupp.single a 1) a (fun _ k => k.factorial)
    (fun _ => Nat.factorial_zero)
  have h2 := Finsupp.mul_prod_erase' s a (fun _ k => k.factorial) (fun _ => Nat.factorial_zero)
  have he : Finsupp.erase a (s + Finsupp.single a 1) = Finsupp.erase a s := by
    ext v
    by_cases hv : v = a
    · subst hv; simp
    · simp [Finsupp.erase_ne hv]
  rw [← h1, ← h2, he]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

noncomputable def fischer (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ g.support, (mfact m : ℂ) * star (AddMonoidAlgebra.coeff f m) * AddMonoidAlgebra.coeff g m

theorem fischer_eq_sum (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hg : g.support ⊆ s) :
    fischer f g = ∑ m ∈ s, (mfact m : ℂ) * star (AddMonoidAlgebra.coeff f m) * AddMonoidAlgebra.coeff g m :=
  Finset.sum_subset hg fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]

theorem fischer_add_left (f f' g : MvPolynomial σ ℂ) :
    fischer (f + f') g = fischer f g + fischer f' g := by
  simp only [fischer, MvPolynomial.coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem fischer_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer (c • f) g = star c * fischer f g := by
  simp only [fischer, MvPolynomial.coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem fischer_add_right (f g g' : MvPolynomial σ ℂ) :
    fischer f (g + g') = fischer f g + fischer f g' := by
  classical
  set s := g.support ∪ g'.support
  rw [fischer_eq_sum f (g + g') s (MvPolynomial.support_add),
    fischer_eq_sum f g s Finset.subset_union_left, fischer_eq_sum f g' s Finset.subset_union_right]
  simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem fischer_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer f (c • g) = c * fischer f g := by
  rw [fischer_eq_sum f (c • g) g.support (MvPolynomial.support_smul), fischer, Finset.mul_sum]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem fischer_zero_left (g : MvPolynomial σ ℂ) : fischer 0 g = 0 := by simp [fischer]

@[simp] theorem fischer_zero_right (f : MvPolynomial σ ℂ) : fischer f 0 = 0 := by simp [fischer]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (g : MvPolynomial σ ℂ) : fischer (∑ i ∈ s, f i) g = ∑ i ∈ s, fischer (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ)
    (g : ι → MvPolynomial σ ℂ) : fischer f (∑ i ∈ s, g i) = ∑ i ∈ s, fischer f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

theorem fischer_conj_symm (f g : MvPolynomial σ ℂ) : star (fischer f g) = fischer g f := by
  classical
  rw [fischer_eq_sum g f (f.support ∪ g.support) Finset.subset_union_left,
    fischer_eq_sum f g (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_natCast, Complex.conj_conj]
  ring

theorem fischer_monomial [DecidableEq σ] (s t : σ →₀ ℕ) (c d : ℂ) :
    fischer (monomial s c) (monomial t d) = if s = t then (mfact s : ℂ) * star c * d else 0 := by
  rw [fischer_eq_sum _ _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton]
  simp only [coeff_monomial]
  by_cases h : s = t
  · subst h; simp
  · simp [h]

theorem fischer_X_mul (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (X a * f) g = fischer f (pderiv a g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, fischer_add_left, fischer_add_left, hp, hq]
  | monomial s c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => rw [fischer_add_right, map_add (f := _), fischer_add_right, hp, hq]
    | monomial t d =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, fischer_monomial, fischer_monomial]
      by_cases ht : t a = 0
      · have hne : Finsupp.single a 1 + s ≠ t := by
          intro h
          have := congrArg (fun m => m a) h
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          omega
        rw [if_neg hne]
        split_ifs <;> simp [ht]
      · have hle : Finsupp.single a 1 ≤ t := by
          intro v
          by_cases hv : v = a
          · subst hv; simp only [Finsupp.single_eq_same]; omega
          · rw [Finsupp.single_apply, if_neg (Ne.symm hv)]; exact Nat.zero_le _
        have hiff : Finsupp.single a 1 + s = t ↔ s = t - Finsupp.single a 1 := by
          constructor
          · rintro rfl; simp
          · rintro rfl; rw [add_comm]; exact tsub_add_cancel_of_le hle
        by_cases h : s = t - Finsupp.single a 1
        · have h' := hiff.2 h
          rw [if_pos h', if_pos h]
          have hsa : (s a + 1 : ℕ) = t a := by
            rw [← h']; simp [add_comm]
          rw [add_comm (Finsupp.single a 1) s, mfact_add_single, ← hsa]
          push_cast
          ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem fischer_pderiv (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (pderiv a f) g = fischer f (X a * g) := by
  rw [← fischer_conj_symm, ← fischer_X_mul, fischer_conj_symm]

theorem fischer_self (f : MvPolynomial σ ℂ) :
    fischer f f = ((∑ m ∈ f.support, (mfact m : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff f m) : ℝ) : ℂ) := by
  rw [fischer]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

theorem fischer_self_eq_zero_iff (f : MvPolynomial σ ℂ) : fischer f f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [fischer_self, Complex.ofReal_eq_zero] at h
  have hnn : ∀ m ∈ f.support, 0 ≤ (mfact m : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff f m) :=
    fun m _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext m
  by_contra hm
  have hm' : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have := hz m hm'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (Nat.cast_ne_zero.2 (mfact_pos m).ne') h1
  · exact hm (Complex.normSq_eq_zero.1 h1)

end GroundTheory.Automorphic.HarishChandra
end

section

namespace GroundTheory.Automorphic.HarishChandra

abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

variable {n : ℕ}

noncomputable def rowOp (i j : Fin n) : Module.End ℂ (Poly n) :=
  ∑ k : Fin n, (LinearMap.mulLeft ℂ (MvPolynomial.X (i, k) : Poly n)) ∘ₗ
    (MvPolynomial.pderiv (j, k) : Derivation ℂ (Poly n) (Poly n)).toLinearMap

theorem rowOp_apply (i j : Fin n) (f : Poly n) :
    rowOp i j f = ∑ k : Fin n, MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) f := by
  simp [rowOp, LinearMap.sum_apply]

end GroundTheory.Automorphic.HarishChandra
end
