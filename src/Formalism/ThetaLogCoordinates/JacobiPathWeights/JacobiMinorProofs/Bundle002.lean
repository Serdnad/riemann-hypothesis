module

import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle003
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle004
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A1hw

theorem mem_can {n : ℕ} {μN : Fin n → ℤ} (h : Antitone μN) (c : ℤ) (m : Fin n) :
    m ∈ canIdx μN c ↔ if 1 ≤ c then c ≤ μN m else μN m < c := by
  unfold canIdx
  split_ifs with hc
  · simp only [mem_filter, mem_univ, true_and]
    exact (Paths.le_iff_lt_colHeight h c m).symm
  · simp only [mem_filter, mem_univ, true_and]
    rw [← not_le, Paths.le_iff_lt_colHeight h c m, not_lt]

theorem isIndex_can {n : ℕ} (μN : Fin n → ℤ) : IsIndex μN (canIdx μN) := by
  apply Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.canIdx_isIndex <;> assumption

theorem map_step {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ} (up : Bool)
    (K : Form A n) (K' : Form A' n) (Xv : Fin n → A) (hK : ∀ J, φ (K J) = K' J) (J : Finset (Fin n)) :
    φ (stepF up K Xv J) = stepF up K' (fun a => φ (Xv a)) J := by
  unfold stepF
  cases up

  · simp only [Bool.false_eq_true, if_false, contrF, map_sum, map_mul, map_intCast, hK]

  · simp only [if_true, wedgeF, map_sum, map_mul, map_intCast, hK]

theorem map_pathWord {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xr : ℕ → Fin n → A) :
    ∀ (j : ℕ) (J : Finset (Fin n)),
      φ (pathWord isVec μ c Xr j J) = pathWord isVec μ c (fun i a => φ (Xr i a)) j J := by
  intro j
  induction j with
  | zero =>
    intro J
    show φ (if J = ∅ then 1 else 0) = if J = ∅ then 1 else 0
    split <;> simp
  | succ j ih =>
    intro J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, pathWord, if_pos hch, if_pos hch]
      exact ih J
    · rw [pathWord, pathWord, if_neg hch, if_neg hch]
      exact map_step φ _ _ _ _ ih J

theorem act_pathWord (hw : FactX2wedge) (hc : FactX2contr) {A : Type} [CommRing A] {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xc Xe : ℕ → Fin n → A)
    (g : (Matrix (Fin n) (Fin n) A)ˣ)
    (h1 : ∀ i, (isVec i == decide (1 ≤ c)) = true → Xe i = Matrix.vecMul (Xc i) (↑g : Matrix _ _ A))
    (h2 : ∀ i, (isVec i == decide (1 ≤ c)) = false →
      Xe i = Matrix.vecMul (Xc i) (↑g⁻¹ : Matrix _ _ A).transpose) :
    ∀ j : ℕ, pathWord isVec μ c Xe j = actF (pathWord isVec μ c Xc j) (↑g : Matrix _ _ A) := by
  intro j
  induction j with
  | zero => exact (actF_oneF _).symm
  | succ j ih =>
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, pathWord, if_pos hch, if_pos hch]
      exact ih
    · rw [pathWord, pathWord, if_neg hch, if_neg hch, ih]
      unfold stepF
      cases hup : (isVec j == decide (1 ≤ c))
      · simp only [Bool.false_eq_true, if_false]
        rw [hc, h2 j hup]
      · simp only [if_true]
        rw [hw, h1 j hup]

end A1hw

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace ExponentSetCounting

variable {n : ℕ}

def ContP (i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n))) : Prop :=
  x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2

def expSet (n i N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {β | ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0}

theorem shift_inj (n i : ℕ) : Function.Injective (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem expSet_subset (n i N : ℕ) (B : ℕ → ℕ) :
    expSet n i N B ⊆ Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2)) ''
      {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0} := by
  intro β hβ
  have hβ' : ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0 := hβ
  have hsupp : ↑β.support ⊆ Set.range (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
    intro p hp
    obtain ⟨j, a⟩ := p
    have hpa : β (j, a) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hij : i ≤ j := by
      by_contra hlt
      have h0 := hβ' j
      rw [if_neg (fun h => hlt h.1)] at h0
      exact hpa ((Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a))
    exact ⟨(j - i, a), Prod.ext (show i + (j - i) = j by omega) rfl⟩
  refine ⟨Finsupp.comapDomain _ β (fun _ _ _ _ h => shift_inj n i h), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    intro j
    show ∑ a, β (i + j, a) = _
    rw [hβ' (i + j)]
    by_cases h : j < N - i
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · apply Finsupp.mapDomain_comapDomain
    · exact shift_inj n i
    · exact hsupp

theorem expSet_finite (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) : (expSet n i N B).Finite :=
  ((hR n (N - i) (fun j => B (i + j))).2.1.image _).subset (expSet_subset n i N B)

theorem expSet_card (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) :
    (expSet n i N B).ncard ≤ ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  have hfin : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.Finite :=
    (hR n (N - i) (fun j => B (i + j))).2.1
  have hcard : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard =
      ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) :=
    (hR n (N - i) (fun j => B (i + j))).1
  calc (expSet n i N B).ncard
      ≤ ((Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2))) ''
          {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}).ncard :=
        Set.ncard_le_ncard (expSet_subset n i N B) (hfin.image _)
    _ ≤ {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard :=
        Set.ncard_image_le hfin
    _ = ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) := hcard
    _ = ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
        (Finset.prod_Ico_eq_prod_range (fun l => (n + B l - 1).choose (B l)) i N).symm

theorem psiFam_mem (k : Type) [Field k] (N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    psiFam k n N isVec B x ∈ polB k n N B := by
  rw [polB, Submodule.mem_iInf]
  intro j
  exact (pathProductDegrees k n N isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1).2 j

end ExponentSetCounting

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end
