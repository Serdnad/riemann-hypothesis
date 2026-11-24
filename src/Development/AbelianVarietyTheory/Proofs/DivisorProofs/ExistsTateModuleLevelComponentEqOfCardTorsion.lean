module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open GlobalTheory.HTLat

namespace GlobalTheory

theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  apply _root_.GlobalTheory.TateFree.exists_pow_eq <;> assumption

theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
