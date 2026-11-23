module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

section

open Matrix UpperTheory.V.Weyl

private theorem UpperTheory.V.Weyl.top_weight_lie_action (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ)
    (h : Ξ.IsTop ν v) (a b : Fin n) (hab : a ≤ b) (f : ℂ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (hfe : ∀ t : ℂ, ∏ k, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • single a b (1 : ℂ)) k k ^ ν k = f t) :
    Ξ.E a b *ᵥ v = f' • v := by
  have hc := UpperTheory.V.Weyl.curve n Ξ (fun t => 1 + t • single a b (1 : ℂ)) (single a b 1) (by simp) (by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (single a b (1 : ℂ) i j)).const_add
      ((1 : Matrix (Fin n) (Fin n) ℂ) i j))
  funext i
  have h1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) ((Ξ.E a b *ᵥ v) i) 0 := by
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hc i j).mul_const (v j)
  have h2 : (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) = fun t => f t * v i := by
    funext t
    rw [h _ ?_, hfe]
    · rfl
    · intro p q hpq
      have : ¬ (a = p ∧ b = q) := by
        rintro ⟨rfl, rfl⟩
        exact absurd hab (not_le.mpr hpq)
      simp [Matrix.one_apply_ne hpq.ne', Matrix.single_apply, this]
  rw [h2] at h1
  exact h1.unique (hf.mul_const (v i))

theorem UpperTheory.V.Weyl.topLie :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), Ξ.IsTop ν v →
      (∀ a, Ξ.E a a *ᵥ v = (ν a : ℂ) • v) ∧ ∀ a b, a < b → Ξ.E a b *ᵥ v = 0 := by
  intro n Ξ ν v h
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a a le_rfl (fun t => (1 + t) ^ ν a) _ ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_pow (ν a)
    · intro t
      rw [Finset.prod_eq_single a]
      · simp
      · intro k _ hk
        simp [Matrix.single_apply, hk.symm]
      · simp
  · have := UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a b hab.le (fun _ => 1) 0 (hasDerivAt_const _ _) (by
      intro t
      refine Finset.prod_eq_one fun k _ => ?_
      have : ¬ (a = k ∧ b = k) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [Matrix.single_apply, this])
    simpa using this
end

section

open Matrix UpperTheory.V.Weyl

private theorem hasDerivAt_mul_mul_entry {n : ℕ} (P Q : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (P' Q' Y : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0)
    (hQ : ∀ i j, HasDerivAt (fun t => Q t i j) (Q' i j) 0) (p q : Fin n) :
    HasDerivAt (fun t => (P t * Y * Q t) p q) ((P' * Y * Q 0 + P 0 * Y * Q') p q) 0 := by
  have h : HasDerivAt (fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q)
      (∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q)) 0 :=
    HasDerivAt.fun_sum fun m _ =>
      (HasDerivAt.fun_sum fun l _ => (hP p l).mul_const (Y l m)).mul (hQ m q)
  have e : (P' * Y * Q 0 + P 0 * Y * Q') p q =
      ∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simp only [Matrix.mul_apply]
  have ef : (fun t => (P t * Y * Q t) p q) = fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q := by
    funext t
    simp only [Matrix.mul_apply]
  rw [e, ef]
  exact h

private theorem pre_D_eq_sum_single {n : ℕ} (Ξ : Pre n) (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin Ξ.d) :
    Ξ.D M i k = ∑ p, ∑ q, M p q * Ξ.D (Matrix.single p q 1) i k := by
  have hM : M = ∑ p, ∑ q, M p q • Matrix.single p q (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [hM]

  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem UpperTheory.V.Weyl.bracket :
    ∀ (n : ℕ) (Ξ : Pre n) (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ),
      Ξ.E a b * Ξ.D Y - Ξ.D Y * Ξ.E a b = Ξ.D (Matrix.single a b 1 * Y - Y * Matrix.single a b 1) := by
  intro n Ξ a b Y
  obtain ⟨P, Q, hP0, hQ0, hQP, hd⟩ := invCurve n a b
  set s : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hs
  set c : Matrix (Fin n) (Fin n) ℂ := s * Y - Y * s with hc
  have hE : ∀ t, Ξ.mat (P t) * Ξ.D Y = Ξ.D (P t * Y * Q t) * Ξ.mat (P t) := fun t =>
    adEq n Ξ (P t) Y (P t * Y * Q t) (by rw [Matrix.mul_assoc (P t * Y), hQP t, Matrix.mul_one])
  have hmat := curve n Ξ P s hP0 (fun i j => (hd i j).1)
  have hM : ∀ p q, HasDerivAt (fun t => (P t * Y * Q t) p q) (c p q) 0 := by
    intro p q
    have h := hasDerivAt_mul_mul_entry P Q s (-s) Y
      (fun i j => (hd i j).1) (fun i j => by simpa using (hd i j).2) p q
    simpa [hP0, hQ0, hc, sub_eq_add_neg, Matrix.mul_neg] using h
  have hdD : ∀ i k, HasDerivAt (fun t => Ξ.D (P t * Y * Q t) i k) (Ξ.D c i k) 0 := by
    intro i k
    have h : HasDerivAt (fun t => ∑ p, ∑ q, (P t * Y * Q t) p q * Ξ.D (Matrix.single p q 1) i k)
        (∑ p, ∑ q, c p q * Ξ.D (Matrix.single p q 1) i k) 0 :=
      HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ => (hM p q).mul_const _
    rw [pre_D_eq_sum_single Ξ c i k]
    convert h using 1
    funext t
    exact pre_D_eq_sum_single Ξ _ i k
  ext i j
  have hL : HasDerivAt (fun t => (Ξ.mat (P t) * Ξ.D Y) i j)
      (∑ k, Ξ.D s i k * Ξ.D Y k j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hmat i k).mul_const _
  have hR : HasDerivAt (fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j)
      (∑ k, (Ξ.D c i k * Ξ.mat (P 0) k j + Ξ.D (P 0 * Y * Q 0) i k * Ξ.D s k j)) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hdD i k).mul (hmat k j)
  have hfun : (fun t => (Ξ.mat (P t) * Ξ.D Y) i j) =
      fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j :=
    funext fun t => by rw [hE t]
  rw [hfun] at hL
  have hu := hL.unique hR
  simp only [hP0, hQ0, Matrix.mul_one, Matrix.one_mul, map_one, Finset.sum_add_distrib] at hu
  simp only [Matrix.sub_apply, Pre.E, Matrix.mul_apply]
  rw [hu]
  simp [Matrix.one_apply, s]
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.preSub :
    ∀ (n : ℕ) (Ξ : Pre n) (S : Submodule ℂ (Fin Ξ.d → ℂ)), (∀ y, ∀ v ∈ S, Ξ.mat y *ᵥ v ∈ S) →
      ∃ (Ξ' : Pre n) (A : Matrix (Fin Ξ.d) (Fin Ξ'.d) ℂ) (B : Matrix (Fin Ξ'.d) (Fin Ξ.d) ℂ),
        Ξ'.d = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ ∀ X, Ξ.D X * A = A * Ξ'.D X := by
  intro n Ξ S hS
  obtain ⟨d', A, B, ρ', hd, hBA, hA, hρ, hcomm⟩ :=
    UpperTheory.V.Weyl.subMat (Matrix (Fin n) (Fin n) ℂ) Ξ.d Ξ.mat S hS
  have hpoly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g,
      ρ' g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    choose p hp using Ξ.poly
    intro i j
    refine ⟨∑ l, (∑ k, MvPolynomial.C (B i k) * p k l) * MvPolynomial.C (A l j), fun g => ?_⟩
    rw [hρ]

    simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hp]
  let Ξ' : Pre n := ⟨d', ρ', hpoly⟩
  refine ⟨Ξ', A, B, hd, hBA, hA, fun X => ?_⟩
  have h0 : (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) 0 = 1 := by simp
  have hc : ∀ a b, HasDerivAt (fun t : ℂ => ((1 : Matrix (Fin n) (Fin n) ℂ) + t • X) a b) (X a b) 0 := by
    intro a b
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X a b)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
  have h1 := UpperTheory.V.Weyl.curve n Ξ _ X h0 hc
  have h2 := UpperTheory.V.Weyl.curve n Ξ' _ X h0 hc
  ext i j
  have e1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • X) * A) i j) ((Ξ.D X * A) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h1 i k).mul_const (A k j)
  have e2 : HasDerivAt (fun t : ℂ => (A * ρ' (1 + t • X)) i j) ((A * Ξ'.D X) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h2 k j).const_mul (A i k)
  simp only [hcomm] at e1
  exact e1.unique e2
end
