module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.RealPlaceAnalysis.Bundle005
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx

private theorem isLocallyConstant_indicator_const_of_isClopen {X : Type} [TopologicalSpace X] {B : Set X}
    (hB : IsClopen B) (c : ℂ) : IsLocallyConstant (B.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨B, hB.isOpen, hx, fun y hy => ?_⟩
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · refine ⟨Bᶜ, hB.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero k)ˣ)
  refine SigmaCompactSpace.of_countable
    (Set.range fun m : ℤ => {x : k | valuation k x ≤ ((g ^ m : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨m, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x = 0
    · subst hx
      refine Set.mem_sUnion.mpr ⟨_, ⟨0, rfl⟩, ?_⟩
      rw [Set.mem_ofPred_eq, map_zero]
      exact zero_le
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (hg (Units.mk0 (valuation k x) ((map_ne_zero (valuation k)).mpr hx)))
      refine Set.mem_sUnion.mpr ⟨_, ⟨m, rfl⟩, ?_⟩
      rw [Set.mem_ofPred_eq, hm, Units.val_mk0]


open GlobalTheory.SplitWeil.FourierPi in
theorem exists_SB_supported_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by
  intro k _ _ _ _ _ _ n _ _ ν _ U hU
  have := sigmaCompactSpace_of_isNonarchimedeanLocalField k
  obtain ⟨s, hsU⟩ := exists_box_subset (k := k) (n := n) hU
  have hBo : IsOpen (box (k := k) n s) := isOpen_box s
  have hBc : IsCompact (box (k := k) n s) := isCompact_box s
  have hBcl : IsClosed (box (k := k) n s) := isClosed_set_pi fun _ _ =>
    AddSubgroup.isClosed_of_isOpen
      { carrier := cball s
        zero_mem' := by
          show valuation k (0 : k) ≤ valuation k (s : k)
          rw [map_zero]
          exact zero_le
        add_mem' := add_mem_cball
        neg_mem' := neg_mem_cball } (isOpen_cball s)
  have hBm : MeasurableSet (box (k := k) n s) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball s).measurableSet
  have h0 : (0 : n → k) ∈ box (k := k) n s := by
    intro i _
    show valuation k (0 : k) ≤ valuation k (s : k)
    rw [map_zero]
    exact zero_le
  have hpos : 0 < (Measure.pi fun _ : n => ν) (box n s) := hBo.measure_pos _ ⟨0, h0⟩
  have hfin : (Measure.pi fun _ : n => ν) (box n s) < ⊤ := hBc.measure_lt_top
  have hreal : (Measure.pi fun _ : n => ν).real (box n s) ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  set c : ℂ := (((Measure.pi fun _ : n => ν).real (box n s) : ℝ) : ℂ)⁻¹ with hc
  refine ⟨⟨(box (k := k) n s).indicator fun _ => c,
    isLocallyConstant_indicator_const_of_isClopen ⟨hBcl, hBo⟩ c,
    HasCompactSupport.intro' hBc hBcl fun y hy => Set.indicator_of_notMem hy _⟩, ?_, ?_⟩
  · intro y hy
    show (box (k := k) n s).indicator (fun _ => c) y = 0
    exact Set.indicator_of_notMem (fun hb => hy (hsU hb)) _
  · show ∫ y, (box (k := k) n s).indicator (fun _ => c) y ∂(Measure.pi fun _ => ν) = 1
    rw [integral_indicator_const c hBm, Complex.real_smul, hc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hreal)]

end GlobalTheory.RootEx
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL

structure SmRep (G : Type) [Group G] [TopologicalSpace G] : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : IsSmooth ρ

attribute [instance] SmRep.acg SmRep.mod

def SmRep.ofIrr {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) : SmRep G :=
  ⟨σ.V, σ.ρ, σ.smooth⟩

section Inhabitant

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Inhabitant

end GlobalTheory.SmGL
end
end

section

open Formalism.REAL Finset

namespace GlobalTheory.TracedComatrix

theorem epow_succ_left {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∀ (k : ℕ) (a b : Fin n), epow E (k + 1) a b = ∑ c, E a c * epow E k c b := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp [epow]
  | succ k ih =>
    intro a b
    calc epow E (k + 1 + 1) a b = ∑ c, epow E (k + 1) a c * E c b := rfl
      _ = ∑ c, (∑ d, E a d * epow E k d c) * E c b :=
          Finset.sum_congr rfl fun c _ => by rw [ih a c]
      _ = ∑ d, E a d * ∑ c, epow E k d c * E c b := by
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ d, E a d * epow E (k + 1) d b := rfl

theorem key {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (N : ℕ)
    (j i : Fin n) :
    ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i =
      algebraMap ℂ A (x ^ (N + 1)) * (if j = i then 1 else 0) +
        algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i := by
  have h1 : ∀ k, ∑ l, Tm E x j l * epow E k l i = algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i := by
    intro k
    rw [epow_succ_left]
    simp [Tm, add_mul, Finset.sum_add_distrib, ite_mul]
  have h2 : ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i
      = ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * ∑ l, Tm E x j l * epow E k l i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
  rw [h2]
  simp_rw [h1]
  set a : ℕ → A := fun k => algebraMap ℂ A ((-1) ^ k * x ^ (N + 1 - k)) * epow E k j i with ha
  have h3 : ∀ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) *
      (algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i) = a k - a (k + 1) := by
    intro k hk
    have hk' : N + 1 - k = (N - k) + 1 := by
      have := Finset.mem_range.mp hk; omega
    simp only [ha, hk', Nat.add_sub_add_right, mul_add, ← mul_assoc, ← map_mul, sub_eq_add_neg,
      ← neg_mul, ← map_neg]
    congr 3 <;> ring
  rw [Finset.sum_congr rfl h3, Finset.sum_range_sub']
  simp only [ha, Nat.sub_self, pow_zero, mul_one, one_mul, Nat.sub_zero, sub_eq_add_neg, ← neg_mul, ← map_neg]
  congr 2
  congr 1
  ring

theorem traced_comatrix : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  intro A _ _ m E hE u N
  set C : Fin (m + 1) → Fin (m + 1) → A := fun i j =>
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u with hC
  set P : Fin (m + 1) → Fin (m + 1) → A := fun l i =>
    ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * epow E k l i with hP
  have hQ := qComatrix A m E hE u
  have S1 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
    simp only [hC, hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    congr 1
    simp only [hP, etr, Finset.mul_sum]
    exact Finset.sum_comm
  have S2 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i := by
    have h : ∀ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
        ∑ j, C i j * (algebraMap ℂ A ((u - m) ^ (N + 1)) * (if j = i then 1 else 0) +
          algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i) := by
      intro i
      calc ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i
          = ∑ j, C i j * ∑ l, Tm E (u - (m : ℂ)) j l * P l i := by
            simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
            exact Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun j _ => congrArg (C i j * ·) (key E (u - (m : ℂ)) N j i)
    simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.commutes]
      simp [hC, ← two_mul, pow_mul]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← mul_assoc, ← Algebra.commutes, hC]
  exact S2.symm.trans S1

end GlobalTheory.TracedComatrix
end
