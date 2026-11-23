module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SatakeDualWeyl.Statement

@[expose] public section

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem ker_map_subset_range_map_of_mul_eq_smul :
    ∀ {O : Type} [CommRing O] [IsDomain O] {k : Type} [Field k] (r : O →+* k),
      Function.Surjective r → ∀ {n : ℕ} (M N : Matrix (Fin n) (Fin n) O) (π : O), π ≠ 0 →
      (∀ t : O, r t = 0 → ∃ s, t = π * s) → M * N = π • (1 : Matrix (Fin n) (Fin n) O) →
      ∀ (v : Fin n → k), N.map r *ᵥ v = 0 → ∃ u, v = M.map r *ᵥ u := by
  intro O _ _ k _ r hr n M N π hπ hker hMN v hv
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (x : Fin n → O),
      (fun i => r ((A *ᵥ x) i)) = A.map r *ᵥ (fun i => r (x i)) := by
    intro A x
    funext i

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  set v' : Fin n → O := fun i => Function.surjInv hr (v i) with hv'def
  have hv' : (fun i => r (v' i)) = v := funext fun i => Function.surjInv_eq hr (v i)
  have h0 : ∀ i, r ((N *ᵥ v') i) = 0 := by
    intro i
    have := congrFun (hmap N v') i
    rw [this, hv', hv]
    rfl
  choose w hw using fun i => hker _ (h0 i)
  have hNw : N *ᵥ v' = π • w := by
    funext i; simp [hw i]
  have key : π • v' = π • (M *ᵥ w) := by
    calc π • v' = (π • (1 : Matrix (Fin n) (Fin n) O)) *ᵥ v' := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (M * N) *ᵥ v' := by rw [hMN]
      _ = M *ᵥ (N *ᵥ v') := by rw [Matrix.mulVec_mulVec]
      _ = π • (M *ᵥ w) := by rw [hNw, Matrix.mulVec_smul]
  have hvw : v' = M *ᵥ w := smul_right_injective (Fin n → O) hπ key
  refine ⟨fun i => r (w i), ?_⟩
  rw [← hmap, ← hvw, hv']

end GlobalTheory
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem adjoin_range_GL_eq_top (R : Type) [CommRing R] (n : ℕ) :
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  set S := Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ)
  have hoff : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1:R) ∈ S := by
    intro i j hij
    have hu : IsUnit (Matrix.transvection i j (1:R)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)
    have hmem : Matrix.transvection i j (1:R) ∈ S :=
      Algebra.subset_adjoin ⟨hu.unit, Set.mem_univ _, rfl⟩
    have : Matrix.single i j (1:R) = Matrix.transvection i j 1 - 1 := by
      simp [Matrix.transvection]
    rw [this]; exact S.sub_mem hmem S.one_mem
  have hall : ∀ i j : Fin n, Matrix.single i j (1:R) ∈ S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases h : ∃ k, k ≠ i
      · obtain ⟨k, hk⟩ := h
        have : Matrix.single i i (1:R) = Matrix.single i k 1 * Matrix.single k i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [this]; exact S.mul_mem (hoff _ _ (Ne.symm hk)) (hoff _ _ hk)
      · push_neg at h
        have : Matrix.single i i (1:R) = 1 := by
          ext a b
          rw [h a, h b]; simp
        rw [this]; exact S.one_mem
    · exact hoff i j hij
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Matrix.single i j 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]; exact S.smul_mem (hall i j) _

end GlobalTheory
end
