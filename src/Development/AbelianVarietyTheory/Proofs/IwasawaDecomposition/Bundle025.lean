module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Order.Ring.Canonical

@[expose] public section

section

noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.SuperTrace

variable {n : ℕ}

def Sg (m : ℕ) (z : Big n) : Prop :=
  ∀ a : Fin n, ((1 : Ext n) ⊗ₜ vec n a) * z = (-1) ^ m * (z * ((1 : Ext n) ⊗ₜ vec n a))

theorem sg_zero (m : ℕ) : Sg m (0 : Big n) := by intro a; simp

theorem sg_add {m : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg m w) : Sg m (z + w) := by
  intro a; rw [mul_add, hz a, hw a, add_mul, mul_add]

theorem sg_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → Big n) (h : ∀ i ∈ s, Sg m (f i)) :
    Sg m (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using sg_zero m
  | cons x s hx ih =>
    rw [Finset.sum_cons]
    exact sg_add (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sg_mul {m l : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg l w) : Sg (m + l) (z * w) := by
  intro a
  have hc : Commute ((-1 : Big n) ^ l) z := (Commute.neg_one_left z).pow_left l
  rw [← mul_assoc, hz a, mul_assoc, mul_assoc, hw a, pow_add, ← mul_assoc z, ← hc.eq]
  simp only [mul_assoc]

theorem sg_one : Sg 0 (1 : Big n) := by intro a; simp

theorem sg_left (x : Ext n) : Sg 0 (x ⊗ₜ (1 : Ext n)) := by
  intro a; simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem sg_right (b : Fin n) : Sg 1 ((1 : Ext n) ⊗ₜ vec n b) := by
  intro a
  simp [Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n a b, TensorProduct.tmul_neg]

def MSg {r s : Type*} (m : ℕ) (M : Matrix r s (Big n)) : Prop := ∀ i j, Sg m (M i j)

theorem msg_mul {r s t : Type*} [Fintype s] {m l : ℕ} {M : Matrix r s (Big n)}
    {N : Matrix s t (Big n)} (hM : MSg m M) (hN : MSg l N) : MSg (m + l) (M * N) := by
  intro i j; rw [Matrix.mul_apply]; exact sg_sum _ _ _ fun k _ => sg_mul (hM i k) (hN k j)

theorem msg_one {r : Type*} [Fintype r] [DecidableEq r] : MSg 0 (1 : Matrix r r (Big n)) := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · exact sg_one
  · exact sg_zero 0

theorem msg_pow {r : Type*} [Fintype r] [DecidableEq r] {M : Matrix r r (Big n)} (hM : MSg 1 M)
    (j : ℕ) : MSg j (M ^ j) := by
  induction j with
  | zero => simpa using (msg_one : MSg 0 (1 : Matrix r r (Big n)))
  | succ j ih => rw [pow_succ]; exact msg_mul ih hM

theorem pow_mul_left {p q : ℕ} {R : Type*} [Semiring R] (A : Matrix (Fin p) (Fin q) R)
    (B : Matrix (Fin q) (Fin p) R) (m : ℕ) : (A * B) ^ m * A = A * (B * A) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc A B A]

theorem trace_swap {p q : ℕ} (A : Matrix (Fin p) (Fin q) (Big n)) (B : Matrix (Fin q) (Fin p) (Big n))
    (hA : MSg 0 A) (hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a) (m : ℕ) :
    ((B * A) ^ (m + 1)).trace = (-1) ^ m * ((A * B) ^ (m + 1)).trace := by
  have hB1 : MSg 1 B := by
    intro b i; obtain ⟨a, ha⟩ := hB b i; rw [ha]; exact sg_right a
  have hY : MSg m (A * (B * A) ^ m) := by
    simpa using msg_mul hA (msg_pow (by simpa using msg_mul hB1 hA) m)
  have h1 : (B * A) ^ (m + 1) = B * (A * (B * A) ^ m) := by
    rw [pow_succ', Matrix.mul_assoc]
  have h2 : (A * B) ^ (m + 1) = (A * (B * A) ^ m) * B := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_left]
  generalize A * (B * A) ^ m = Y at hY h1 h2
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨a, ha⟩ := hB b i
  rw [ha, hY i b a]

theorem val_trace {r : Type*} [Fintype r] (M : Matrix r r (EvenPart n)) :
    ((EvenPart n).val M.trace) = (M.map (EvenPart n).val).trace := by

  simp [Matrix.trace, map_sum]

theorem val_pow {r : Type*} [Fintype r] [DecidableEq r] (M : Matrix r r (EvenPart n)) (k : ℕ) :
    (M ^ k).map (EvenPart n).val = (M.map (EvenPart n).val) ^ k :=
  map_pow ((EvenPart n).val.toRingHom.mapMatrix) M k

end GlobalTheory.GrassModel.SuperTrace

open GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace in
theorem GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar {n p q : ℕ}
    (e : Fin p × Fin q → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    ((blockPoly e).map (toEven n) ^ k).trace + ((-blockPolyBar e).map (toEven n) ^ k).trace = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set A : Matrix (Fin p) (Fin q) (Big n) := Matrix.of fun i b => vec n (e (i, b)) ⊗ₜ (1 : Ext n)
  set B : Matrix (Fin q) (Fin p) (Big n) := Matrix.of fun b j => (1 : Ext n) ⊗ₜ vec n (e (j, b))
  have hA : MSg 0 A := fun i b => sg_left _
  have hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a := fun b i => ⟨e (i, b), rfl⟩
  have hL : ((blockPoly e).map (toEven n)).map (EvenPart n).val = A * B := by
    ext i j

    simp [A, B, blockPoly, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hD : (Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = B * A := by
    ext i j

    simp [A, B, blockPolyBar, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hneg : (-blockPolyBar e).map (toEven n) = -((blockPolyBar e).map (toEven n)) := by
    ext i j; simp
  apply Subtype.val_injective
  show (EvenPart n).val (_ + _) = (EvenPart n).val 0
  rw [map_add (f := _), map_zero, hneg, ← Matrix.trace_transpose (( -_ ) ^ _), Matrix.transpose_pow,
    Matrix.transpose_neg, val_trace, val_trace, val_pow, val_pow, hL]
  rw [show (-Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = -(B * A) by
    rw [← hD]; ext i j; simp]
  rcases Nat.even_or_odd (m + 1) with h | h
  · rw [h.neg_pow, trace_swap A B hA hB m]
    have : Odd m := by rcases h with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    rw [this.neg_one_pow]; simp
  · rw [h.neg_pow, Matrix.trace_neg, trace_swap A B hA hB m]
    have : Even m := by rcases h with ⟨t, ht⟩; exact ⟨t, by omega⟩
    rw [this.neg_one_pow]; simp
end
end

section

noncomputable section

namespace GlobalTheory.NormalDescent

open CategoryTheory Polynomial TensorProduct

theorem charK_map_of_isPushout {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  haveI : Module.Finite A B := hφ
  haveI : Module.Finite A' B' := hφ'
  letI : Algebra K K' := ι.toAlgebra
  letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a
  let e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B' :=
    AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv
  unfold charK
  change (Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly =
    (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')
  rw [← LinearMap.charpoly_baseChange, ← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), hs, ht]
  | tmul c' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [tmul_add, map_add (f := _), hs, ht]
    | tmul c x =>
      simp [e, IsBaseChange.equiv_tmul]
      rfl

end GlobalTheory.NormalDescent
end
end

section

namespace GlobalTheory.LowestKType

open Formalism.IndefR.IndefiniteWeightData Formalism.IndefR.IndefiniteWeightData.WeightData

variable {D : WeightData}

lemma r_eq (h : D.Hyp) : D.r = D.p + D.q := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.r WeightData.p WeightData.q
  omega

lemma nV_eq (h : D.Hyp) : D.nV = D.p + D.q + D.t := by
  unfold WeightData.nV
  rw [r_eq h]

lemma nV_cast (h : D.Hyp) : (D.nV : ℚ) = D.p + D.q + D.t := by
  rw [nV_eq h]; push_cast; ring

lemma lam_tail (h : D.Hyp) (c : ℕ) : D.lam (D.p + c) = -D.b (D.j + c) := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.lam WeightData.p
  rw [if_neg (by omega)]
  congr 2
  omega

lemma lam_step (h : D.Hyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.r) :
    (D.lam (i + 1) : ℚ) + 1 ≤ D.lam i := by
  have : D.lam (i + 1) + 1 ≤ D.lam i := h.2.2.2.2.2.1 i h1 h2
  exact_mod_cast this

lemma aMinus_rev (c : ℕ) (hc : c ≤ D.q + 1) :
    D.aMinus (D.q + 1 - c) = ((D.b (D.j + c) : ℚ) - D.e) + (1 - (D.t : ℚ) - 2 * (c : ℚ)) / 2 := by
  have : D.q + 1 - (D.q + 1 - c) = c := by omega
  unfold WeightData.aMinus
  rw [this]

lemma exists_half_r (h : D.Hyp) : ∃ u : ℕ, (D.q : ℚ) = 2 * u + 1 - D.p := by
  obtain ⟨u, hu⟩ := h.2.2.2.1
  rw [r_eq h] at hu
  have : (D.p : ℚ) + D.q = 2 * u + 1 := by exact_mod_cast hu
  exact ⟨u, by linarith⟩

lemma weightData_t_odd (h : D.Hyp) : ∃ w : ℕ, (D.t : ℚ) = 2 * w + 1 := by
  obtain ⟨u, hu⟩ := h.2.2.2.2.1
  exact ⟨u, by exact_mod_cast hu⟩

lemma aPlus_int (h : D.Hyp) (i : ℕ) : ∃ z : ℤ, D.aPlus i = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.lam i + D.e - w - 1 + i - D.p, ?_⟩
  unfold WeightData.aPlus
  rw [nV_cast h, hu, hw]
  push_cast
  ring

lemma aMinus_int (h : D.Hyp) (s : ℕ) : ∃ z : ℤ, D.aMinus s = z := by
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.b (D.j + (D.q + 1 - s)) - D.e - w - ((D.q + 1 - s : ℕ) : ℤ), ?_⟩
  unfold WeightData.aMinus
  generalize D.q + 1 - s = c
  rw [hw]
  push_cast
  ring

lemma theta_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.thetaWt i + ((D.p : ℚ) - D.q) / 2 - D.e + D.rhoNV i = D.uSideTarget i := by
  rw [nV_eq h] at h2
  unfold WeightData.thetaWt WeightData.rhoNV WeightData.uSideTarget
  by_cases hi : i ≤ D.p
  · simp only [if_pos hi]
    unfold WeightData.aPlus
    ring
  · by_cases hi' : i ≤ D.p + D.t
    · simp only [if_neg hi, if_pos hi']
      rw [nV_cast h]
      ring
    · obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      simp only [if_neg hi, if_neg hi', e1]
      rw [aMinus_rev c (by omega), nV_cast h]
      push_cast
      ring

lemma lamPrime_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.lamPrime i + D.rhoNV i = D.uSideTarget i - 1 / 2 := by
  rw [← theta_param h i h2]
  unfold WeightData.lamPrime WeightData.dTau
  ring

lemma dTau_int (h : D.Hyp) : ∃ z : ℤ, D.dTau = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  refine ⟨D.p - u - 1 - D.e, ?_⟩
  unfold WeightData.dTau
  rw [hu]; push_cast; ring

lemma target_step (h : D.Hyp) (hg : D.GapHyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.nV) :
    D.uSideTarget (i + 1) + 1 ≤ D.uSideTarget i := by
  have hr := r_eq h
  rw [nV_eq h] at h2
  have ht : 1 ≤ D.t := h.2.2.2.2.1.pos
  unfold WeightData.uSideTarget
  rcases lt_trichotomy i D.p with hi | hi | hi
  · have a1 : i ≤ D.p := by omega
    have a2 : i + 1 ≤ D.p := by omega
    simp only [if_pos a1, if_pos a2]
    exact lam_step h i h1 (by omega)
  · subst hi
    have a2 : ¬ D.p + 1 ≤ D.p := by omega
    have a3 : D.p + 1 ≤ D.p + D.t := by omega
    have h4 := lam_tail h 0
    simp only [add_zero] at h4
    simp only [if_pos (le_refl D.p), if_neg a2, if_pos a3]
    rw [h4]
    have := hg.1
    push_cast
    linarith
  · have a1 : ¬ i ≤ D.p := by omega
    have a2 : ¬ i + 1 ≤ D.p := by omega
    simp only [if_neg a1, if_neg a2]
    rcases lt_trichotomy i (D.p + D.t) with hi' | hi' | hi'
    · have a3 : i ≤ D.p + D.t := by omega
      have a4 : i + 1 ≤ D.p + D.t := by omega
      simp only [if_pos a3, if_pos a4]
      push_cast
      linarith
    · subst hi'
      have a4 : ¬ D.p + D.t + 1 ≤ D.p + D.t := by omega
      have e1 : D.p + D.t + 1 - D.p - D.t = 1 := by omega
      have hq : D.q = D.m - D.j := rfl
      have := hg.2 (by omega)
      simp only [if_pos (le_refl (D.p + D.t)), if_neg a4, e1]
      push_cast
      linarith
    · have a3 : ¬ i ≤ D.p + D.t := by omega
      have a4 : ¬ i + 1 ≤ D.p + D.t := by omega
      simp only [if_neg a3, if_neg a4]
      obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      have e2 : D.p + D.t + c + 1 - D.p - D.t = c + 1 := by omega
      have h3 := lam_step h (D.p + c) (by omega) (by omega)
      rw [add_assoc, lam_tail h, lam_tail h] at h3
      rw [e1, e2]
      push_cast at h3
      linarith

theorem thetaSide : ThetaSideStatement := by
  intro D h hg
  refine ⟨fun i _ h2 => theta_param h i h2, fun i _ h2 => lamPrime_param h i h2, dTau_int h,
    ?_, ?_, ?_⟩
  · intro i _ _
    obtain ⟨d, hd⟩ := dTau_int h
    unfold WeightData.lamPrime WeightData.thetaWt
    rw [hd]
    split_ifs
    · obtain ⟨z, hz⟩ := aPlus_int h i
      exact ⟨z + d, by rw [hz]; push_cast; ring⟩
    · exact ⟨d, by ring⟩
    · obtain ⟨z, hz⟩ := aMinus_int h (D.q + 1 - (i - D.p - D.t))
      exact ⟨-z + d, by rw [hz]; push_cast; ring⟩
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    have h4 := lamPrime_param h i h2.le
    have h5 := lamPrime_param h (i + 1) h2
    unfold WeightData.rhoNV at h4 h5
    push_cast at h5
    linarith
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    rw [lamPrime_param h i h2.le, lamPrime_param h (i + 1) h2]
    linarith

end GlobalTheory.LowestKType
end

section

namespace GlobalTheory.MemGlintOfEntries

theorem mem_glint_of_entries {K : Type} [inst : Field K] {n : ℕ} (O : Subring K)
    (g : GL (Fin n) K)
    (h : ∀ (i j : Fin n), (↑g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h' : ∀ (i j : Fin n), (↑g⁻¹ : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩
  let B : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h' i j⟩
  have hA : O.subtype.mapMatrix A = (↑g : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hB : O.subtype.mapMatrix B = (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hinj : Function.Injective
      (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) K) := by
    intro X Y hXY
    ext i j
    exact congrFun (congrFun hXY i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul g
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.MemGlintOfEntries
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_monomial_of_multiplicative_of_single_eq_zpow : ∀ (n : ℕ) (χ : (Fin n → ℂ) → ℂ), χ 1 = 1 → (∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t) → (∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k) → ∃ μ : Fin n → ℤ, ∀ d : Fin n → ℂ, (∀ i, d i ≠ 0) → χ d = ∏ i, d i ^ μ i := by
  first | exact @GlobalTheory.laurentMonomial_of_multiplicative | exact GlobalTheory.laurentMonomial_of_multiplicative | (intros; apply GlobalTheory.laurentMonomial_of_multiplicative <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  first | exact @GlobalTheory.exists_fin_reps_projective_finrank_le | exact GlobalTheory.exists_fin_reps_projective_finrank_le | (intros; apply GlobalTheory.exists_fin_reps_projective_finrank_le <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.finitely_many_iso_classes_projective_numberField : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  first | exact @GlobalTheory.ProjModFinIso.finitely_many_iso_classes | exact GlobalTheory.ProjModFinIso.finitely_many_iso_classes | (intros; apply GlobalTheory.ProjModFinIso.finitely_many_iso_classes <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (ι : Type) [Finite ι] (f : ι → V → ℂ), (∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ)) → (∀ i, ∃ v, f i v ≠ 0) → ∃ v, ∀ i, f i v ≠ 0 := by
  first | exact @GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | exact GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | (intros; apply GlobalTheory.exists_common_nonzero_of_polynomial_on_lines <;> assumption)
end
