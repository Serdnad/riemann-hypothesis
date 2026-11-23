module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.FockInnerEqSumRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.Bundle001
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
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

section

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

def KHc : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ (e : ℕ) (P : Pol p q r s),
  homogeneousComponent e (fockAct1 p q r s (Eab a b) P) =
    fockAct1 p q r s (Eab a b) (homogeneousComponent e P)

def KHarm : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P : Pol p q r s,
  Harm2 P → Harm2 (fockAct1 p q r s (Eab a b) P)

def HcHarm : Prop := ∀ p q r s : ℕ, ∀ (e : ℕ) (P : Pol p q r s),
  Harm2 P → Harm2 (homogeneousComponent e P)

def HarmSub : Prop := ∀ p q r s : ℕ,
  Harm2 (0 : Pol p q r s) ∧ (∀ P Q : Pol p q r s, Harm2 P → Harm2 Q → Harm2 (P + Q)) ∧
    (∀ (c : ℂ) (P : Pol p q r s), Harm2 P → Harm2 (c • P))

def KAdj : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P Q : Pol p q r s,
  fockInner P (fockAct1 p q r s (Eab a b) Q) = fockInner (fockAct1 p q r s (Eab b a) P) Q

def HwExist : Prop := ∀ p q r s : ℕ, ∀ U : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ U → U ≠ ⊥ →
  (∀ a b : Ix p q, sameBlock a b → ∀ u ∈ U, fockAct1 p q r s (Eab a b) u ∈ U) →
    ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ IsHW (fockAct1 p q r s) ν v

end PI.FockOneDegW
end
end

section

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

section Ops

theorem omE_same {p q r s : ℕ} (a b : Ix p q) (c : Ix r s) (hab : sameBlock a b)
    (P : Pol p q r s) :
    omE ((a, c) : Ln p q r s) (b, c) P =
      ((if linePos ((a, c) : Ln p q r s) = true then
          X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0)
        - (if linePos ((b, c) : Ln p q r s) = true then 0 else
          X ((b, c) : Ln p q r s) * pderiv ((a, c) : Ln p q r s) P))
      + (if a = b then
          (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) • P else 0) := by
  classical

  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) := by
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [sameBlock, linePos]
  have hab' : (((a, c) : Ln p q r s) = (b, c)) ↔ a = b := by simp
  rw [FockRL.omE_apply]
  unfold raiB lowB
  rw [hl]
  cases h : linePos ((a, c) : Ln p q r s)
  · by_cases hab2 : a = b
    · subst hab2
      simp [Derivation.leibniz, pderiv_X]
      module
    · have hne : ((a, c) : Ln p q r s) ≠ (b, c) := fun h' => hab2 (hab'.1 h')
      simp [hab2, hne, Derivation.leibniz, pderiv_X, Pi.single_apply, Ne.symm hne]
  · simp [hab']

theorem fockAct1_Eab_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    fockAct1 p q r s (Eab a b) P = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) P := by
  classical
  rw [FockRL.fockAct1_eq, FockRL.omAct_eq_sum]
  simp [Eab, Matrix.single_apply, Matrix.one_apply, ite_and, Fintype.sum_prod_type,
    LinearMap.sum_apply]

theorem posOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    posOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0) := by
  unfold posOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem negOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    negOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then 0 else
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P) := by
  unfold negOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem sum_half {p q r s : ℕ} (a : Ix p q) :
    ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) =
      (((kShift r s a : ℚ)) : ℂ) := by
  rcases a with a | a <;> simp [kShift, cPair, linePos, Fintype.sum_sum_type] <;> push_cast <;> ring

theorem fock_operators_kernel : OpsK := by
  intro p q r s a b hab
  apply LinearMap.ext
  intro P
  rw [fockAct1_Eab_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, posOp_apply, negOp_apply]
  rw [Finset.sum_congr rfl fun c _ => omE_same a b c hab P, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1
  split_ifs with h
  · subst h
    simp only [↓reduceIte, LinearMap.smul_apply, Module.End.one_apply]
    rw [← Finset.sum_smul, sum_half]
  · simp

end Ops

section Harm

theorem minus2_eq {p q r s : ℕ} (Z : Mat r s) (hZ : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Z) P = -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P := by
  classical

  have hside : ∀ (a : Ix p q) (c d : Ix r s), ¬ sameBlock c d →
      linePos ((a, d) : Ln p q r s) = true → linePos ((a, c) : Ln p q r s) = false := by
    intro a c d hcd hd
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [sameBlock, linePos]
  have hOpp : FockRL.OppSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z) := by
    rintro ⟨a, c⟩ ⟨b, d⟩ hne
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at hne
    split_ifs at hne with hab
    · subst hab
      have hcd : ¬ sameBlock c d := fun h => hne (by rw [hZ c d h, mul_zero])
      intro hEq
      rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
        simp_all [sameBlock, linePos]
    · simp at hne
  rw [FockRL.fockAct2_eq, FockRL.omAct_eq_Rop_add_Lop _ hOpp,
    (FockRaiseLowGrade.raisingLoweringSplit _ _ _ (fun d P hP => FockRL.Rop_raise _ d P hP)
      (fun e P => FockRL.Lop_shift _ e P) P).2, FockRL.Lop_apply]

  have hL : ∀ (a : Ix p q) (c : Ix r s),
      (∑ l' : Ln p q r s, if linePos ((a, c) : Ln p q r s) = false ∧ linePos l' = true then
        Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z (a, c) l' •
          (-(pderiv ((a, c) : Ln p q r s) (pderiv l' P))) else 0) =
      ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    intro a c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun d _ => ?_
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
      by_cases hZcd : Z c d = 0
      · simp [hZcd]
      · have hcd : ¬ sameBlock c d := fun h => hZcd (hZ c d h)
        by_cases hd : linePos ((a, d) : Ln p q r s) = true
        · simp [hd, hside a c d hcd hd]
        · simp [hd]
    · intro b _ hba
      refine Finset.sum_eq_zero fun d _ => ?_
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hba)]
    · simp
  have hR : -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P =
      ∑ c : Ix r s, ∑ a : Ix p q, ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [lowOp, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [Fintype.sum_prod_type]
  simp only [hL]
  rw [Finset.sum_comm, hR]

theorem harmIff : HarmIff := by
  intro p q r s P
  unfold Harm2
  constructor
  · intro h c d hcd
    have hZ : IsPC (Matrix.single c d (1 : ℂ) : Mat r s) := by
      intro a b hab
      rw [Matrix.single_apply]
      split_ifs with h'
      · obtain ⟨rfl, rfl⟩ := h'
        exact absurd hab hcd
      · rfl
    have h1 := h _ hZ
    rw [minus2_eq _ hZ] at h1
    simpa [Matrix.single_apply, ite_and] using h1
  · intro h Z hZ
    rw [minus2_eq _ hZ, neg_eq_zero]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases hcd : sameBlock c d
    · rw [hZ c d hcd, zero_smul]
    · rw [h c d hcd, smul_zero]

end Harm

end PI.FockOneDegW
end
end

section

noncomputable section

open MvPolynomial FockH1Action FockRaiseLowInner

namespace PI.FockOneDegW.Inner

export FockRaiseLowInner (fockInner_X_mul fockInner_mul_X fockInner_sum_left fockInner_sum_right
  fockInner_swap fockInner_zero_left fockInner_zero_right fockInner_add_left fockInner_add_right
  fockInner_smul_left fockInner_smul_right fockInner_neg_left fockInner_neg_right fockInner_sub_right
  fockInner_eq_support wt)

section Pos

variable {σ : Type*}

def wtN (α : σ →₀ ℕ) : ℕ := α.prod (fun _ k => k.factorial)

theorem wtN_pos (α : σ →₀ ℕ) : 0 < wtN α := by
  unfold wtN Finsupp.prod
  exact Finset.prod_pos fun i _ ↦ Nat.factorial_pos _

theorem wt_eq_wtN (α : σ →₀ ℕ) : wt α = (wtN α : ℂ) := by
  simp only [wt, wtN, Finsupp.prod, Nat.cast_prod]

theorem fockInner_self_eq (F : MvPolynomial σ ℂ) :
    fockInner F F = ((∑ α ∈ F.support, Complex.normSq (AddMonoidAlgebra.coeff F α) * (wtN α : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_support, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast, wt_eq_wtN]

theorem fockInner_self_re_nonneg (F : MvPolynomial σ ℂ) : 0 ≤ (fockInner F F).re := by
  rw [fockInner_self_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun α _ ↦ mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fockInner_self_im (F : MvPolynomial σ ℂ) : (fockInner F F).im = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_im]

theorem eq_zero_of_fockInner_self_re (F : MvPolynomial σ ℂ) (h : (fockInner F F).re = 0) :
    F = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_re] at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ ↦ mul_nonneg (Complex.normSq_nonneg (AddMonoidAlgebra.coeff F α)) (Nat.cast_nonneg (wtN α)))).1 h
  by_contra hF
  obtain ⟨α, hα⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF)
  have hc : AddMonoidAlgebra.coeff F α ≠ 0 := MvPolynomial.mem_support_iff.1 hα
  have hne : Complex.normSq (AddMonoidAlgebra.coeff F α) * (wtN α : ℝ) ≠ 0 :=
    mul_ne_zero (Complex.normSq_pos.2 hc).ne' (by exact_mod_cast (wtN_pos α).ne')
  exact hne (hall α hα)

end Pos

end PI.FockOneDegW.Inner

namespace PI.FockOneDegW

open PI.FockOneDegW.Inner in
theorem fock_inner_facts : InnerFacts := by
  intro σ P Q Q' c
  refine ⟨fockInner_add_right _ _ _, fockInner_smul_right _ _ _, fockInner_swap _ _,
    ⟨fockInner_self_im _, fockInner_self_re_nonneg _⟩, fun h ↦ ?_, fun l ↦ fockInner_X_mul l P Q⟩
  exact eq_zero_of_fockInner_self_re P (by rw [h]; simp)

end PI.FockOneDegW
end
end
