module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign
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

@[expose] public section

section

noncomputable section

open Matrix

namespace FockRL

def jsgn {p q : ℕ} : FockH1Action.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : FockH1Action.Jm p q = Matrix.diagonal (jsgn (p := p) (q := q)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FockH1Action.Jm, FockH1Action.Jpq, jsgn,
      Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp_all

theorem conjR_apply {p q : ℕ} (Z : FockH1Action.Mat p q) (a b : FockH1Action.Ix p q) :
    FockH1Action.conjR Z a b = -(jsgn a * star (Z b a) * jsgn b) := by
  simp only [FockH1Action.conjR, FockH1Action.adjZ,
    Jm_eq_diagonal, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply]

theorem conjR_apply_of_not {p q : ℕ} (Z : FockH1Action.Mat p q) {a b : FockH1Action.Ix p q}
    (h : ¬ FockH1Action.sameBlock a b) : FockH1Action.conjR Z a b = (starRingEnd ℂ) (Z b a) := by
  rw [conjR_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [FockH1Action.sameBlock, jsgn]

theorem sameBlock_symm {p q : ℕ} {a b : FockH1Action.Ix p q} (h : FockH1Action.sameBlock a b) :
    FockH1Action.sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [FockH1Action.sameBlock]

theorem conjR_isPC {p q : ℕ} (Z : FockH1Action.Mat p q) (hZ : FockH1Action.IsPC Z) :
    FockH1Action.IsPC (FockH1Action.conjR Z) := by
  intro a b hab
  rw [conjR_apply, hZ b a (sameBlock_symm hab)]
  simp

theorem linePos_left {p q r s : ℕ} (a a' : FockH1Action.Ix p q) (b : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a', b) : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock a a' := by
  rcases a with a | a <;> rcases a' with a' | a' <;> rcases b with b | b <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

theorem linePos_right {p q r s : ℕ} (a : FockH1Action.Ix p q) (b b' : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a, b') : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock b b' := by
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

theorem fockAct1_eq (p q r s : ℕ) (Z : FockH1Action.Mat p q) : FockH1Action.fockAct1 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s)) := by
  rfl

theorem fockAct2_eq (p q r s : ℕ) (Z : FockH1Action.Mat r s) : FockH1Action.fockAct2 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z) := by
  rfl

theorem kroneckerMap_one_right_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨by simpa using h, hb⟩
  · simp at h

theorem kroneckerMap_one_left_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat r s) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z (a, b) (a', b') ≠ 0) :
    Z b b' ≠ 0 ∧ a = a' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with ha
  · exact ⟨by simpa using h, ha⟩
  · simp at h

theorem kroneckerProperties : MatStep := by
  intro p q r s
  refine ⟨fockAct1_eq p q r s, fockAct2_eq p q r s, ?_, ?_, ?_, ?_,
    conjR_isPC, conjR_isPC, ?_, ?_⟩
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    have hs : FockH1Action.sameBlock a a' := by
      by_contra hn
      exact hz (hZ a a' hn)
    exact (linePos_left a a' b).2 hs
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    have hs : FockH1Action.sameBlock b b' := by
      by_contra hn
      exact hz (hZ b b' hn)
    exact (linePos_right a b b').2 hs
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    exact hz (hZ a a' ((linePos_left a a' b).1 heq))
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    exact hz (hZ b b' ((linePos_right a b b').1 heq))
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases hb : b = b'
    · subst hb
      have hn : ¬ FockH1Action.sameBlock a' a := fun hs => by
        have := (linePos_left a a' b).2 (sameBlock_symm hs)
        rw [h1, h2] at this
        simp at this
      simp [conjR_apply_of_not Z hn]
    · have hb' : ¬ b' = b := fun e => hb e.symm
      simp [hb, hb']
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases ha : a = a'
    · subst ha
      have hn : ¬ FockH1Action.sameBlock b' b := fun hs => by
        have := (linePos_right a b b').2 (sameBlock_symm hs)
        rw [h1, h2] at this
        simp at this
      simp [conjR_apply_of_not Z hn]
    · have ha' : ¬ a' = a := fun e => ha e.symm
      simp [ha, ha']

end FockRL
end
end

section

noncomputable section

namespace FockRaiseLowGrade

open MvPolynomial FockH1Action

variable {σ : Type*}

theorem hc_hc (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by
  classical
  rw [homogeneousComponent_of_mem (homogeneousComponent_mem n P)]

theorem eq_zero_of_hc (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by
  calc x = ∑ i ∈ Finset.range (x.totalDegree + 1), homogeneousComponent i x :=
        (sum_homogeneousComponent x).symm
    _ = 0 := Finset.sum_eq_zero (fun i _ => h i)

theorem sum_hc_of_le (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by
  have hsub : Finset.range (P.totalDegree + 1) ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  rw [← Finset.sum_subset hsub ?_]
  · exact sum_homogeneousComponent P
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    apply homogeneousComponent_eq_zero
    omega

theorem plus_eq (R L : Module.End ℂ (MvPolynomial σ ℂ))
    (hR : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → R P ∈ homog σ (d + 2))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : plusPart (R + L) P = R P := by
  classical
  have hterm : ∀ d, homogeneousComponent (d + 2) ((R + L) (homogeneousComponent d P)) =
      R (homogeneousComponent d P) := by
    intro d
    have hmem := hR d _ (homogeneousComponent_mem d P)
    rw [LinearMap.add_apply, map_add (f := _), hL, hc_hc,
      if_neg (show ¬ (d + 2 + 2 = d) by omega), map_zero, add_zero,
      homogeneousComponent_of_mem hmem, if_pos rfl]
  have hsupp : (Function.support fun d => R (homogeneousComponent d P)) ⊆
      ↑(Finset.range (P.totalDegree + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have h0 : homogeneousComponent d P = 0 := by
      apply homogeneousComponent_eq_zero
      omega
    rw [h0, map_zero]

  rw [FockH1Action.plusPart, finsum_congr hterm, finsum_eq_sum_of_support_subset _ hsupp,
  ← map_sum R, sum_homogeneousComponent]

private theorem apply_homogeneousComponent_eq_zero_of_lt_two (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (Q : MvPolynomial σ ℂ) (k : ℕ) (hk : k < 2) : L (homogeneousComponent k Q) = 0 := by
  apply eq_zero_of_hc
  intro e
  rw [hL, hc_hc, if_neg (show ¬ (e + 2 = k) by omega), map_zero]

theorem minus_eq (R L : Module.End ℂ (MvPolynomial σ ℂ))
    (hR : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → R P ∈ homog σ (d + 2))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : minusPart (R + L) P = L P := by
  classical
  have hterm : ∀ d, homogeneousComponent d ((R + L) (homogeneousComponent (d + 2) P)) =
      L (homogeneousComponent (d + 2) P) := by
    intro d
    have hmem := hR (d + 2) _ (homogeneousComponent_mem (d + 2) P)
    rw [LinearMap.add_apply, map_add (f := _), hL, hc_hc, if_pos rfl,
      homogeneousComponent_of_mem hmem]
    split_ifs with hc
    · exact absurd hc (by omega)
    · rw [zero_add]
  have hsupp : (Function.support fun d => L (homogeneousComponent (d + 2) P)) ⊆
      ↑(Finset.range (P.totalDegree + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have h0 : homogeneousComponent (d + 2) P = 0 := by
      apply homogeneousComponent_eq_zero
      omega
    rw [h0, map_zero]
  rw [FockH1Action.minusPart, finsum_congr hterm, finsum_eq_sum_of_support_subset _ hsupp]
  calc ∑ d ∈ Finset.range (P.totalDegree + 1), L (homogeneousComponent (d + 2) P)
      = ∑ i ∈ Finset.range (P.totalDegree + 1 + 1 + 1), L (homogeneousComponent i P) := by
        rw [Finset.sum_range_succ' _ (P.totalDegree + 1 + 1),
          Finset.sum_range_succ' _ (P.totalDegree + 1),
          apply_homogeneousComponent_eq_zero_of_lt_two L hL P 0 (by norm_num)]
        simp only [zero_add, apply_homogeneousComponent_eq_zero_of_lt_two L hL P 1 (by norm_num), add_zero]
        try rfl
    _ = L P := by

        rw [← map_sum L, sum_hc_of_le P (P.totalDegree + 1 + 1 + 1) (by omega)]

theorem raisingLoweringSplit : FockRL.PMSplit := by
  intro σ R L hR hL P
  exact ⟨plus_eq R L hR hL P, minus_eq R L hR hL P⟩

end FockRaiseLowGrade
end
end

section

namespace FockRL

theorem gradedOscillatorProperty_of (hK : KCStep) (hP : PCStep) (hA : AdjStep) (hM : MatStep) : FockH1Action.H1 := by
  intro p q r s
  obtain ⟨e1, e2, k1, k2, o1, o2, c1, c2, a1, a2⟩ := hM p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ d P hP'
    rw [e1]; exact hK p q r s _ (k1 Z hZ) d P hP'
  · intro Z hZ d P hP'
    rw [e2]; exact hK p q r s _ (k2 Z hZ) d P hP'
  · intro Z hZ P
    rw [e1]; exact hP p q r s _ (o1 Z hZ) P
  · intro Z hZ P
    rw [e2]; exact hP p q r s _ (o2 Z hZ) P
  · intro Z hZ P Q
    rw [e1, e1]; exact hA p q r s _ _ (o1 Z hZ) (o1 _ (c1 Z hZ)) (a1 Z) P Q
  · intro Z hZ P Q
    rw [e2, e2]; exact hA p q r s _ _ (o2 Z hZ) (o2 _ (c2 Z hZ)) (a2 Z) P Q

end FockRL
end
