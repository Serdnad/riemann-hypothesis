module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section

section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

variable {A : Type} [CommRing A] {a r t : ℕ}

private theorem yc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.yc P (z.1, (z.2 - z.1 * Y₀) * S * D) =
      (GlobalTheory.CompanionTheory.NullFr.yc P z - Y₀) * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.yc]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc, hP,
    Matrix.smul_mul, Matrix.one_mul, hY₀]

private theorem vc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.vc P (z.1, (z.2 - z.1 * Y₀) * S * D) = GlobalTheory.CompanionTheory.NullFr.vc P z * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.vc]
  rw [yc_sub_mul_mul_mul_eq e P z hP Y₀ hY₀ S D, ← Matrix.mul_assoc z.1,
    ← Matrix.mul_assoc z.1, ← Matrix.sub_mul, ← Matrix.sub_mul, Matrix.mul_sub z.1,
    sub_sub_sub_cancel_right]

theorem mul_gU_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (d : Fin t → A) (p : Fin m) (j : Fin t) :
    (M * gU i d) p j = M p j + if j = i then ∑ k, d k * M p k else 0 := by
  rw [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : j = i
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.of_apply, if_pos h, mul_comm]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.of_apply, if_neg h, mul_zero]

theorem mul_gD_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (u : A) (p : Fin m) (j : Fin t) :
    (M * gD i u) p j = if j = i then u * M p i else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.gD, Matrix.mul_diagonal]
  by_cases h : j = i
  · subst h
    simp [mul_comm]
  · simp [h, Function.update_apply]

theorem mul_gU_gD_apply {m : ℕ} (M : Fx A m t) (i : Fin t) (c : Fin t → A) (u' : A) (p : Fin m)
    (j : Fin t) :
    (M * gU i (-c) * gD i u') p j =
      if j = i then u' * (M p i - ∑ k, c k * M p k) else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gD_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · rw [if_pos h, if_pos h, if_pos rfl]
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp only [if_neg h, add_zero]

theorem gU_neg_mul (i : Fin t) (c : Fin t → A) (hc : c i = 0) : gU i (-c) * gU i c = 1 := by
  refine Matrix.ext fun p j => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · subst h
    simp [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.one_apply, mul_add, Finset.sum_add_distrib, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', hc]
  · simp [GlobalTheory.CompanionTheory.NullFr.gU, h]

theorem gD_mul (i : Fin t) (u' u : A) (h : u' * u = 1) : gD i u' * gD i u = 1 := by
  refine Matrix.ext fun p q => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.gD, GlobalTheory.CompanionTheory.NullFr.gD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi
      simp [h]
    · simp [Function.update_apply, hpi]
  · simp [hpq]

end GlobalTheory.CompanionTheory.NullFr.CoverStep

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

theorem point_eq_translate : ∀ {A : Type} [CommRing A] {a r t : ℕ} (e f : A) (_ : e * e = e) (_ : f * e = f) (_ : f * f = f) (P : Fx A a r → Fx A r a)
    (i : Fin t) (C : Set A) (z : Fx A a r × Fx A a t) (_ : z ∈ admitted e P) (_ : ∀ p q, z.1 p q ∈ C)
    (_ : ∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C)
    (_ : ∀ p k, k ≠ i → vc P z p k ∈ C) (_ : ∀ p, (1 - f) * vc P z p i ∈ C)
    (c : Fin t → A) (_ : c i = 0) (_ : ∀ k, f * c k = c k) (_ : ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k)
    (u : Aˣ) (_ : (1 - f) * (u : A) = 1 - f)
    (c₀ c₁ : Fin t → A) (_ : c₀ i = 0) (_ : ∀ k, f * c₀ k = c₀ k) (_ : c₁ i = 0)
    (_ : ∀ k, f * c₁ k = c₁ k ∧ c₁ k ∈ C) (_ : ∀ k, c k = c₀ k + u * c₁ k)
    (y₀ y₁ : Fin r → A) (_ : ∀ l, f * y₀ l = y₀ l) (_ : ∀ l, f * y₁ l = y₁ l ∧ y₁ l ∈ C)
    (_ : ∀ l, f * yc P z l i - ∑ k, c₀ k * yc P z l k = y₀ l + u * y₁ l),
    ∃ w ∈ Piece e f P i C, z = (w.1, w.2 * gD i (u : A) * gU i c₀ + w.1 * yU i y₀) := by
  intro A _ a r t e f he hfe hff P i C z hz hz1 hY hKo hKi c hci hfc hfK u hu c₀ c₁ hc₀i hfc₀
    hc₁i hc₁ hc y₀ y₁ hfy₀ hy₁ hy
  simp only [GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq] at hz
  obtain ⟨hez1, hez2, hP⟩ := hz
  have hey₀ : ∀ l, e * y₀ l = y₀ l := fun l => by
    rw [← hfy₀ l, ← mul_assoc, mul_comm e f, hfe]
  have hY₀ : e • GlobalTheory.CompanionTheory.NullFr.yU i y₀ = GlobalTheory.CompanionTheory.NullFr.yU i y₀ := by
    refine Matrix.ext fun l j => ?_
    simp only [GlobalTheory.CompanionTheory.NullFr.yU, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact hey₀ l
    · exact mul_zero e
  have hY₀i : ∀ l, GlobalTheory.CompanionTheory.NullFr.yU i y₀ l i = y₀ l := fun l => by
    simp [GlobalTheory.CompanionTheory.NullFr.yU]
  have hu' : (1 - f) * ((u⁻¹ : Aˣ) : A) = 1 - f := by
    conv_lhs => rw [← hu]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h1fc₀ : ∀ k, (1 - f) * c₀ k = 0 := fun k => by
    rw [sub_mul, one_mul, hfc₀, sub_self]
  have h1fy₀ : ∀ l, (1 - f) * y₀ l = 0 := fun l => by
    rw [sub_mul, one_mul, hfy₀, sub_self]
  have hsum : ∀ l, ∑ k, c₀ k * (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
    intro l
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · simp [hk, hc₀i]
    · simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
  have key : ∀ l, f * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) =
      (u : A) * y₁ l := by
    intro l
    rw [mul_sub, mul_sub, hfy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, hfc₀]
    rw [sub_right_comm, hy l, add_sub_cancel_left]
  have key2 : ∀ l, (1 - f) * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l -
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) = (1 - f) * GlobalTheory.CompanionTheory.NullFr.yc P z l i := by
    intro l
    rw [mul_sub, mul_sub, h1fy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
  have hD : GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A) * GlobalTheory.CompanionTheory.NullFr.gD i (u : A) = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gD_mul i _ _ u.inv_mul
  have hS : GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) * GlobalTheory.CompanionTheory.NullFr.gU i c₀ = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gU_neg_mul i c₀ hc₀i
  have hco := yc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  have hcm := vc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  refine ⟨(z.1, (z.2 - z.1 * GlobalTheory.CompanionTheory.NullFr.yU i y₀) * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
    GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)), ?_, ?_⟩
  · simp only [GlobalTheory.CompanionTheory.NullFr.Piece, GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq]
    rw [hco, hcm]
    refine ⟨⟨hez1, ?_, hP⟩, hz1, ?_, ?_, ?_, c₁, hc₁i, hc₁, ?_⟩
    · rw [← Matrix.smul_mul, ← Matrix.smul_mul, smul_sub, ← Matrix.smul_mul, hez2, hez1]
    · intro l k
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
      by_cases hk : k = i
      · rw [if_pos hk, hsum l, Matrix.sub_apply, hY₀i l]
        refine ⟨?_, ?_⟩
        · rw [mul_left_comm, key l, ← mul_assoc, Units.inv_mul, one_mul]
          exact (hy₁ l).2
        · rw [← mul_assoc, hu', key2 l]
          exact (hY l i).2
      · have hE : (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
            GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
          simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
        rw [if_neg hk, hE]
        exact hY l k
    · intro p k hk
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_neg hk]
      exact hKo p k hk
    · intro p
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, ← mul_assoc, hu', mul_sub,
        Finset.mul_sum]
      simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
      exact hKi p
    · intro p
      have hR : ∑ k, c₁ k * (GlobalTheory.CompanionTheory.NullFr.vc P z * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
          GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) p k = ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
        by_cases hk : k = i
        · simp [hk, hc₁i]
        · rw [if_neg hk]
      have hL : f * (GlobalTheory.CompanionTheory.NullFr.vc P z p i - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k) =
          (u : A) * ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        rw [mul_sub, hfK p, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, hfc₀, ← sub_mul, hc k, add_sub_cancel_left, mul_assoc]
      rw [hR, GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, mul_left_comm, hL,
        ← mul_assoc, Units.inv_mul, one_mul]
  · refine Prod.ext rfl ?_
    dsimp only
    rw [Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) (GlobalTheory.CompanionTheory.NullFr.gD i (u : A)),
      hD, Matrix.mul_one, Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀)) (GlobalTheory.CompanionTheory.NullFr.gU i c₀), hS,
      Matrix.mul_one, sub_add_cancel]

end GlobalTheory.CompanionTheory.NullFr.CoverStep
end

section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gD_mul_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u v : A) :
    gD i u * gD i v = gD i (u * v) := by
  unfold gD
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem gD_one {A : Type} [CommRing A] {t : ℕ} (i : Fin t) : gD i (1 : A) = 1 := by
  unfold gD
  have h : Function.update (1 : Fin t → A) i 1 = 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [h]
  exact Matrix.diagonal_one

theorem det_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : A) : (gD i u).det = u := by
  unfold gD
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem exists_gl_gD : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : Aˣ),
    ∃ g : GL (Fin t) A, g.1 = gD i (u : A) ∧ Matrix.GeneralLinearGroup.det g = u := by
  intro A _ t i u
  refine ⟨⟨GlobalTheory.CompanionTheory.NullFr.gD i (u : A), GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A), ?_, ?_⟩, rfl, ?_⟩
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.mul_inv, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.inv_mul, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.CompanionTheory.NullFr.det_gD i (u : A)

end GlobalTheory.CompanionTheory.NullFr
end

section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Packing

theorem exists_max_card {α : Type} (Q : Finset α → Prop) (B : ℕ) (h0 : ∃ P, Q P)
    (hB : ∀ P, Q P → P.card ≤ B) : ∃ P, Q P ∧ ∀ P', Q P' → P'.card ≤ P.card := by
  obtain ⟨P₀, hP₀⟩ := h0
  have hne : {n : ℕ | ∃ P, Q P ∧ P.card = n}.Nonempty := ⟨P₀.card, P₀, hP₀, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ P, Q P ∧ P.card = n} := by
    refine ⟨B, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact hB P hP
  obtain ⟨P, hP, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨P, hP, fun P' hP' => ?_⟩
  rw [hcard]
  exact le_csSup hbdd ⟨P', hP', rfl⟩

theorem measure_unit_image {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K : Set A} (hK : IsCompact K) :
    h ((fun x : A => (u : A) * x) '' K) = md u * h K := by
  have hc : Continuous fun x : A => (u : A) * x := continuous_const.mul continuous_id
  have hinj : Function.Injective fun x : A => (u : A) * x := fun x y hxy => by
    simpa using congrArg (fun z => ((u⁻¹ : Aˣ) : A) * z) hxy
  have hKu : IsCompact ((fun x : A => (u : A) * x) '' K) := hK.image hc
  have key := congrArg (fun μ : Measure A => μ ((fun x : A => (u : A) * x) '' K))
    (hmd h inferInstance u)
  rw [Measure.map_apply hc.measurable hKu.measurableSet, Set.preimage_image_eq _ hinj,
    Measure.smul_apply, smul_eq_mul] at key
  have hmd0 : ((md u : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    intro h0
    rw [ENNReal.coe_eq_zero] at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  rw [key, ← mul_assoc, ENNReal.mul_inv_cancel hmd0 ENNReal.coe_ne_top, one_mul]

theorem card_mul_le {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K L : Set A} (hK : IsCompact K) (P : Finset A)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K))
    (hL : ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L) :
    (P.card : ℝ≥0∞) * (md u * h K) ≤ h L := by
  classical
  have hcont : ∀ p : A, Continuous fun x : A => p + (u : A) * x := fun p =>
    continuous_const.add (continuous_const.mul continuous_id)
  have hmT : ∀ p : A, h ((fun x : A => p + (u : A) * x) '' K) = md u * h K := by
    intro p
    have e : (fun x : A => p + (u : A) * x) '' K =
        (fun y => -p + y) ⁻¹' ((fun x : A => (u : A) * x) '' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by abel⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, by rw [hxy]; abel⟩
    rw [e, measure_preimage_add, GlobalTheory.CompanionTheory.NullFr.Packing.measure_unit_image hmd h u hK]
  have hsub : (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) ⊆ L := by
    refine Set.iUnion₂_subset fun p hp => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hL p hp w hw
  calc (P.card : ℝ≥0∞) * (md u * h K)
      = ∑ p ∈ P, h ((fun x : A => p + (u : A) * x) '' K) := by
        rw [Finset.sum_congr rfl (fun p _ => hmT p), Finset.sum_const, nsmul_eq_mul]
    _ = h (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) :=
        (measure_biUnion_finset (fun p hp q hq hpq => hdisj p hp q hq hpq)
          (fun p _ => (hK.image (hcont p)).measurableSet)).symm
    _ ≤ h L := measure_mono hsub

theorem net : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (md : Aˣ →* ℝ≥0) (_ : IsHaarMod md) (f : A) (_ : f * f = f) (C U : Set A) (_ : IsCompact C) (_ : U ∈ 𝓝 (0 : A)),
    ∃ (κ : ℝ≥0) (V : Set A), V ∈ 𝓝 (0 : A) ∧ ∀ u : Aˣ, (1 - f) * (u : A) = 1 - f → f * (u : A) ∈ V →
      ∃ N : Finset A, (∀ p ∈ N, f * p = p ∧ p ∈ C) ∧ (N.card : ℝ≥0) * md u ≤ κ ∧
        ∀ c ∈ C, f * c = c → ∃ p ∈ N, ∃ w ∈ U, f * w = w ∧ c = p + u * w := by
  intro A _ _ _ _ _ _ _ _ md hmd f _ C U hC hU
  classical
  have hU' : U ∈ 𝓝 ((0 : A) - 0) := by rwa [sub_zero]
  have h0 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_sub.tendsto ((0 : A), (0 : A)) hU'
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨K, hK0, hKW, hK⟩ := local_compact_nhds (Filter.inter_mem hW₁ hW₂)
  have hKU : ∀ a ∈ K, ∀ b ∈ K, a - b ∈ U := fun a ha b hb =>
    hW (Set.mk_mem_prod (hKW ha).1 (hKW hb).2)
  obtain ⟨V, hV0, -, hV⟩ := local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : A))
  obtain ⟨L, hLdef⟩ : ∃ L : Set A,
      L = (fun q : A × A × A => q.1 + q.2.1 * q.2.2 + (1 - f) * q.2.2) '' (C ×ˢ V ×ˢ K) :=
    ⟨_, rfl⟩
  have hLc : IsCompact L := by
    rw [hLdef]
    exact (hC.prod (hV.prod hK)).image (by fun_prop)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure A, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hKpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK0
  have hKfin : μ K < ⊤ := hK.measure_lt_top
  have hLfin : μ L < ⊤ := hLc.measure_lt_top
  refine ⟨(μ L / μ K).toNNReal, V, hV0, ?_⟩
  intro u hu1 hfu
  have hmd0 : md u ≠ 0 := by
    intro h0
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hm0 : (md u : ℝ≥0∞) * μ K ≠ 0 := mul_ne_zero (by exact_mod_cast hmd0) hKpos.ne'
  have hmtop : (md u : ℝ≥0∞) * μ K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin.ne
  have hLmem : ∀ P : Finset A, (∀ p ∈ P, f * p = p ∧ p ∈ C) →
      ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L := by
    intro P hP p hp w hw
    rw [hLdef]
    refine ⟨(p, f * u, w), ⟨(hP p hp).2, hfu, hw⟩, ?_⟩
    show p + f * u * w + (1 - f) * w = p + u * w
    rw [← hu1]
    ring
  have hB : ∀ P : Finset A, ((∀ p ∈ P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)) →
      P.card ≤ ⌈(μ L / ((md u : ℝ≥0∞) * μ K)).toReal⌉₊ := by
    intro P hP
    have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hP.2 (hLmem P hP.1)
    have h1 : (P.card : ℝ≥0∞) ≤ μ L / ((md u : ℝ≥0∞) * μ K) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 hc
    have h2 : (P.card : ℝ) ≤ (μ L / ((md u : ℝ≥0∞) * μ K)).toReal := by
      simpa using ENNReal.toReal_mono (ENNReal.div_ne_top hLfin.ne hm0) h1
    exact_mod_cast h2.trans (Nat.le_ceil _)
  obtain ⟨P, ⟨hPC, hPdisj⟩, hmax⟩ :=
    GlobalTheory.CompanionTheory.NullFr.Packing.exists_max_card (hB := hB) (h0 := ⟨∅, by simp⟩)
  refine ⟨P, hPC, ?_, ?_⟩
  · have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hPdisj (hLmem P hPC)
    have h2 : (((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞) ≤ μ L / μ K := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKfin.ne)]
      push_cast
      rw [mul_assoc]
      exact hc
    calc (P.card : ℝ≥0) * md u = ((((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞)).toNNReal := by
          rw [ENNReal.toNNReal_coe]
      _ ≤ (μ L / μ K).toNNReal :=
          ENNReal.toNNReal_mono (ENNReal.div_ne_top hLfin.ne hKpos.ne') h2
  · intro c hc hfc
    by_cases hcP : c ∈ P
    · exact ⟨c, hcP, 0, mem_of_mem_nhds hU, by simp, by simp⟩
    · obtain ⟨p, hp, hpc⟩ : ∃ p ∈ P, ¬ Disjoint ((fun x : A => p + (u : A) * x) '' K)
          ((fun x : A => c + (u : A) * x) '' K) := by
        by_contra hcon
        push_neg at hcon
        have hQ : (∀ p ∈ insert c P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ insert c P, ∀ q ∈ insert c P,
            p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K)
              ((fun x : A => q + (u : A) * x) '' K) := by
          refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨hfc, hc⟩
            · exact hPC p hp'
          · rcases Finset.mem_insert.1 hp with rfl | hp' <;>
              rcases Finset.mem_insert.1 hq with rfl | hq'
            · exact absurd rfl hpq
            · exact (hcon q hq').symm
            · exact hcon p hp'
            · exact hPdisj p hp' q hq' hpq
        have hle := hmax _ hQ
        rw [Finset.card_insert_of_notMem hcP] at hle
        omega
      obtain ⟨x, ⟨k₁, hk₁, hx₁⟩, ⟨k₂, hk₂, hx₂⟩⟩ := Set.not_disjoint_iff.1 hpc
      have hx₁' : p + (u : A) * k₁ = x := hx₁
      have hx₂' : c + (u : A) * k₂ = x := hx₂
      have hw : (u : A) * (k₁ - k₂) = c - p := by linear_combination hx₁' - hx₂'
      have hfp : f * p = p := (hPC p hp).1
      refine ⟨p, hp, k₁ - k₂, hKU k₁ hk₁ k₂ hk₂, ?_, by rw [hw]; ring⟩
      calc f * (k₁ - k₂) = ((u⁻¹ : Aˣ) : A) * ((u : A) * (f * (k₁ - k₂))) := by simp
        _ = ((u⁻¹ : Aˣ) : A) * (f * ((u : A) * (k₁ - k₂))) := by ring
        _ = ((u⁻¹ : Aˣ) : A) * ((u : A) * (k₁ - k₂)) := by rw [hw, mul_sub f c p, hfc, hfp]
        _ = k₁ - k₂ := by simp

end GlobalTheory.CompanionTheory.NullFr.Packing
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValPowDvd

theorem dvd_of_pow_mul_dvd_pow : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  intro S _ ϖ hϖ hV z m d hd hdiv
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨e, he, h1, h2⟩ := hV (ϖ ^ m) z ⟨m, Ideal.subset_span (Set.mem_insert _ _)⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : (e * ϖ ^ m) ^ (d' + 1) = (c' * z) ^ (d' + 1) := by rw [hc']
  rw [mul_pow, mul_pow, hw, he.pow_succ_eq d', ← pow_mul] at h3
  have key : (e - w * c' ^ (d' + 1)) * ϖ ^ (m * (d' + 1)) = 0 := by linear_combination h3
  have he' : e = w * c' ^ (d' + 1) :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hϖ (m * (d' + 1)))).2 _ key)
  have hee : e * e = e := he.eq
  exact ⟨e * w * c' ^ d' + c, by
    linear_combination (-1 : S) * hc + (-z) * hee + (z * e) * he' + (e * w * c' ^ d') * hc' +
      (w * c' ^ d' * ϖ ^ m) * hee⟩

end GlobalTheory.CompanionTheory.ValPowDvd
end
