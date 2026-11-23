module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle778
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle770
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockAnalytic

theorem totalDegree_pderiv_le_self {σ : Type} (i : σ) (Q : MvPolynomial σ ℂ) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  refine Finset.sup_le fun m hm => ?_
  have hc : AddMonoidAlgebra.coeff Q (m + Finsupp.single i 1) ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := le_totalDegree (mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ Q.totalDegree
  omega

def OneStep {σ : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (A : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d →
    (A P).totalDegree ≤ d + 1 ∧ ‖ι (A P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2

section
variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem oneStep_mul (h : IsFockIP ι) (i : σ) : OneStep ι (LinearMap.mulLeft ℂ (X i)) := by
  intro d P hP
  refine ⟨?_, (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).1⟩
  rw [LinearMap.mulLeft_apply]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]; omega

theorem oneStep_pderiv (h : IsFockIP ι) (i : σ) : OneStep ι (pderiv i).toLinearMap := by
  intro d P hP
  refine ⟨((totalDegree_pderiv_le_self i P).trans hP).trans (Nat.le_succ _), ?_⟩
  have := (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).2
  have h2 := sq_nonneg ‖ι P‖
  change ‖ι (pderiv i P)‖ ^ 2 ≤ _
  nlinarith

omit [DecidableEq σ] in
theorem OneStep.neg {A : Module.End ℂ (MvPolynomial σ ℂ)} (h : OneStep ι A) : OneStep ι (-A) := by
  intro d P hP
  simpa using h d P hP

omit [DecidableEq σ] in
theorem OneStep.comp {A B : Module.End ℂ (MvPolynomial σ ℂ)} (hA : OneStep ι A) (hB : OneStep ι B)
    (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ((A * B) P).totalDegree ≤ d + 2 ∧ ‖ι ((A * B) P)‖ ≤ ((d : ℝ) + 3 / 2) * ‖ι P‖ := by
  obtain ⟨h1, h2⟩ := hB d P hP
  obtain ⟨h3, h4⟩ := hA (d + 1) _ h1
  refine ⟨h3, ?_⟩
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  push_cast at h4
  have h5 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (d : ℝ) + 1 + 1 by positivity)
  have h6 := sq_nonneg ‖ι P‖
  change ‖ι (A (B P))‖ ^ 2 ≤ _
  nlinarith
end

section
variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Pol p q r s →ₗ[ℂ] H}

theorem omE_bound (h : IsFockIP ι) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s)
    (hP : P.totalDegree ≤ d) :
    (omE l l' P).totalDegree ≤ d + 2 ∧ ‖ι (omE l l' P)‖ ≤ ((d : ℝ) + 2) * ‖ι P‖ := by
  have hA : OneStep ι (raiB l) := by
    unfold raiB; split_ifs
    exacts [oneStep_mul h l, (oneStep_pderiv h l).neg]
  have hB : OneStep ι (lowB l') := by
    unfold lowB; split_ifs
    exacts [oneStep_pderiv h l', oneStep_mul h l']
  obtain ⟨h1, h2⟩ := hA.comp hB d P hP
  have hn := norm_nonneg (ι P)
  unfold omE
  split_ifs
  · rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    refine ⟨(totalDegree_add _ _).trans (max_le h1 ((totalDegree_smul_le _ _).trans (by omega))), ?_⟩
    rw [map_add (f := _), map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  · rw [add_zero]
    exact ⟨h1, by linarith⟩

theorem omAct_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ)
    (P : Pol p q r s) (hP : P.totalDegree ≤ d) :
    (omAct p q r s Y P).totalDegree ≤ d + 2 ∧
      ‖ι (omAct p q r s Y P)‖ ≤ (∑ l, ∑ l', ‖Y l l'‖) * (((d : ℝ) + 2) * ‖ι P‖) := by
  have e : omAct p q r s Y P = ∑ l, ∑ l', Y l l' • omE l l' P := by
    simp [omAct, LinearMap.sum_apply]
  rw [e]
  constructor
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l' _ => ?_)
    exact (totalDegree_smul_le _ _).trans (omE_bound h l l' d P hP).1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_

    rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l' _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (omE_bound h l l' d P hP).2 (norm_nonneg _)

theorem omAct_pow_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d m : ℕ)
    (hm : d ≤ 2 * m) (P : Pol p q r s) (hP : P.totalDegree ≤ d) (k : ℕ) :
    ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧
      ‖ι ((omAct p q r s Y ^ k) P)‖ ≤
        (2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖ := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := omAct_bound h Y _ _ ih.1
    refine ⟨by omega, h2.trans ?_⟩
    have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
    have hm' : (d : ℝ) ≤ 2 * m := by exact_mod_cast hm
    rw [Nat.ascFactorial_succ]
    push_cast
    calc _ ≤ (∑ l, ∑ l', ‖Y l l'‖) * ((2 * ((m : ℝ) + 1 + k)) *
            ((2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS
          exact mul_le_mul (by linarith) ih.2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
end

theorem omAct_pow_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  intro p q r s H _ _ ι h Y d k P hP
  obtain ⟨h1, h2⟩ := omAct_pow_bound h Y d ((d + 1) / 2) (by omega) P hP k
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  set m := (d + 1) / 2 with hm
  have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
  generalize (∑ l, ∑ l', ‖Y l l'‖) = S at hS
  have hm1 : (m : ℝ) ≤ (d : ℝ) / 2 + 1 := by
    have : 2 * m ≤ d + 2 := by omega
    have : (2 * m : ℝ) ≤ d + 2 := by exact_mod_cast this
    linarith
  have h3 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ ((d : ℝ) / 2 + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hm1
  have h4 : (((m + k).choose k : ℕ) : ℝ) ≤ 2 ^ (m + k) := by
    exact_mod_cast Nat.choose_le_two_pow (m + k) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  calc (2 * S) ^ k * ((k.factorial : ℝ) * ((m + k).choose k : ℝ))
      ≤ (2 * S) ^ k * ((k.factorial : ℝ) * 2 ^ (m + k)) := by gcongr
    _ = (4 * S) ^ k * (k.factorial : ℝ) * 2 ^ m := by
        rw [show (4 : ℝ) * S = 2 * (2 * S) by ring, mul_pow 2 (2 * S), pow_add]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.FockAnalytic
end
end

section

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, if_pos rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (if_neg h)

theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
end
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any | exact GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any | (intros; apply GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.CuspCutCoef

theorem isCuspFn_cutCoef : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π →
  ∀ (v : V), ∀ l ∈ smoothPart π.dual,
  ∀ f : GL (Fin N) k → ℂ, (∀ g, f g = if ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1 then l (π g v) else 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  ∃ K0 : Subgroup (GL (Fin N) k), IsOpen (K0 : Set (GL (Fin N) k)) ∧ IsCompact (K0 : Set (GL (Fin N) k)) ∧
    (∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin N) k,
      (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin N) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro k _ _ _ _ _ _ N V _ _ π hπ v l hl f hf
  have hsm : IsSmooth π := hπ.1
  have hU : {g : GL (Fin N) k | π g v = v} ∩ {g | ∀ y, l (π g y) = l y} ∈ nhds (1 : GL (Fin N) k) :=
    Filter.inter_mem ((hsm v).mem_nhds (by simp)) (GlobalTheory.CuspCoef.fix_mem_nhds π l hl)
  obtain ⟨γ, hγ, hsub⟩ := GlobalTheory.CentralExponent.exists_cong_subset hU
  set K0 := GlobalTheory.CentralExponent.cong (Fin N) γ hγ with hK0
  have hK0val : ∀ x ∈ K0, ValuativeRel.valuation k (x : Matrix (Fin N) (Fin N) k).det = 1 := by
    intro x hx
    have h1 : x ∈ GlobalTheory.SplitWeil.KO k (Fin N) :=
      KOne_le_KO (mem_KOne.2 fun i j => (hx i j).trans_le hγ)
    obtain ⟨y, rfl⟩ := h1
    have h2 : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k).det = algebraMap 𝒪[k] k (y : Matrix (Fin N) (Fin N) 𝒪[k]).det :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h2]
    exact (Valuation.integer.integers (ValuativeRel.valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)
  have hbi : ∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g := by
    intro x hx y hy g
    rw [hf, hf]
    have hd : ValuativeRel.valuation k ((x * g * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
        ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
        hK0val x hx, hK0val y hy, one_mul, mul_one]
    rw [hd]
    split_ifs
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hsub y hy).1, (hsub x hx).2]
    · rfl
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_
    have hc : Continuous fun y : GL (Fin N) k => g⁻¹ * y := continuous_const.mul continuous_id
    have : ∀ᶠ y in nhds g, g⁻¹ * y ∈ K0 :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [inv_mul_cancel]
        exact (GlobalTheory.CentralExponent.isOpen_cong γ hγ).mem_nhds K0.one_mem)
    filter_upwards [this] with y hy
    have := hbi 1 K0.one_mem (g⁻¹ * y) hy g
    rwa [one_mul, mul_inv_cancel_left] at this
  obtain ⟨C, hC, hCs⟩ := (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k N V π hπ).2 v l hl
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.T.central_translate_det_one_compact k N C hC
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro hD fun g hg => ?_
    rw [hf]
    split_ifs with h
    · by_contra h0
      obtain ⟨z, hz, c, hc, rfl⟩ := hCs g h0
      exact hg (hDs z hz c hc h)
    · rfl
  refine ⟨hlc, hcs, K0, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, hbi, ?_⟩
  intro a b e ha hb μ hμ u hu g h
  obtain ⟨huc, hum, hud, hup⟩ := GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport k N a b e u hu
  by_cases hg : ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1
  · refine GlobalTheory.T.integral_unipotentRadical_coefficient_coinvariant_eq_zero k N V π hsm a b μ hμ u huc hum (l ∘ₗ π (g * h⁻¹)) (π h v)
      (GlobalTheory.T.cuspidal_unipotent_vanishing k N V π hπ a b e ha hb u hu _) _ (hup f hcs g h) fun X => ?_
    have hd : ValuativeRel.valuation k ((g * (h⁻¹ * u X * h) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, hg, one_mul, mul_one]
      rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one]
    rw [hf, if_pos hd]
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
  · have : (fun X => f (g * (h⁻¹ * u X * h))) = fun _ => 0 := by
      funext X
      rw [hf, if_neg]
      intro hd
      apply hg
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, mul_one] at hd
      rwa [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one, mul_one] at hd
    rw [this, integral_zero]

end GlobalTheory.CuspCutCoef
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.origin_ideal_extension_prime : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  first | (exact @GlobalTheory.OriginPrimes.origin_primes) | (exact GlobalTheory.OriginPrimes.origin_primes) | (intros; apply GlobalTheory.OriginPrimes.origin_primes <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.freeEtaleSheaf_excision_shortExact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ (w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0), (ShortComplex.mk _ _ w).ShortExact := by
  first | (exact @GlobalTheory.EtC.MVFree.shortExact) | (exact GlobalTheory.EtC.MVFree.shortExact) | (intros; apply GlobalTheory.EtC.MVFree.shortExact <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_torsor_descent_directedUnion_subring : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  first | (exact @GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (exact GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (intros; apply GlobalTheory.TorsorUnionDescent.exists_stage_torsor  <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  first | (exact @GlobalTheory.exists_strictlyHenselian_normal_between) | (exact GlobalTheory.exists_strictlyHenselian_normal_between) | (intros; apply GlobalTheory.exists_strictlyHenselian_normal_between  <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bOne_isGood | exact GlobalTheory.HeckeTwo.bOne_isGood | (intros; apply GlobalTheory.HeckeTwo.bOne_isGood <;> assumption)
end
