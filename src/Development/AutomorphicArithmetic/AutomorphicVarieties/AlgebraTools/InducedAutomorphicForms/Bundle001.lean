module

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
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IsIrreducibleIff

@[expose] public section

section

open UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.indTwo :
    ∀ {R G n : Type} [CommRing R] [Group G] [Fintype n] [DecidableEq n] (H : Subgroup G) (s : G), H.index = 2 → s ∉ H → ∀ r : H →* GL n R, ∃ I : G →* GL (n ⊕ n) R, (∀ h h' : H, (h' : G) = s⁻¹ * h * s → (I h : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks (r h : Matrix n n R) 0 0 (r h' : Matrix n n R)) ∧ ∀ t : H, (t : G) = s * s → (I s : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks 0 (r t : Matrix n n R) 1 0 := by
  intro R G n _ _ _ _ H s hH hs r
  classical
  obtain ⟨r0, hin, hout⟩ : ∃ r0 : G → Matrix n n R,
      (∀ h : H, r0 h = (r h : Matrix n n R)) ∧ ∀ g, g ∉ H → r0 g = 0 := by
    refine ⟨fun g => if h : g ∈ H then (r ⟨g, h⟩ : Matrix n n R) else 0, ?_, ?_⟩
    · intro h
      simp only [dif_pos h.2]
    · intro g hg
      simp only [dif_neg hg]
  have hs' : s⁻¹ ∉ H := fun h => hs (by simpa using h)
  have hm : ∀ a b : G, a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hH
  have hmul : ∀ a b : G, a ∈ H → b ∈ H → r0 (a * b) = r0 a * r0 b := by
    intro a b ha hb
    have h1 := hin ⟨a, ha⟩
    have h2 := hin ⟨b, hb⟩
    have h3 := hin (⟨a, ha⟩ * ⟨b, hb⟩)
    rw [map_mul, Units.val_mul, ← h1, ← h2] at h3
    exact h3
  have hone : r0 1 = 1 := by
    have := hin 1
    rw [map_one] at this
    simpa using this
  have key : ∀ a b : G, r0 (a * b) = r0 a * r0 b + r0 (a * s) * r0 (s⁻¹ * b) := by
    intro a b
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
    · rw [hmul a b ha hb, hout (a * s) (by rw [hm]; tauto), zero_mul, add_zero]
    · rw [hout (a * b) (by rw [hm]; tauto), hout b hb, hout (a * s) (by rw [hm]; tauto)]
      simp
    · rw [hout (a * b) (by rw [hm]; tauto), hout a ha, hout (s⁻¹ * b) (by rw [hm]; tauto)]
      simp
    · rw [hout a ha, zero_mul, zero_add,
        ← hmul _ _ (by rw [hm]; tauto) (by rw [hm]; tauto)]
      congr 1
      group
  let M : G →* Matrix (n ⊕ n) (n ⊕ n) R :=
    { toFun := fun g => Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s))
      map_one' := by
        rw [one_mul, mul_one, inv_mul_cancel, hone, hout s hs, hout _ hs', Matrix.fromBlocks_one]
      map_mul' := by
        intro a b
        rw [Matrix.fromBlocks_multiply]
        have e1 := key a b
        have e2 := key a (b * s)
        have e3 := key (s⁻¹ * a) b
        have e4 := key (s⁻¹ * a) (b * s)
        simp only [mul_assoc] at e1 e2 e3 e4 ⊢
        rw [e1, e2, e3, e4] }
  have hM : ∀ g, (M.toHomUnits g : Matrix (n ⊕ n) (n ⊕ n) R) =
      Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s)) := fun g => rfl
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · intro h h' hh
    have h2 := h.2
    rw [hM, ← hh, hin, hin, hout (h * s) (by rw [hm]; tauto),
      hout (s⁻¹ * h) (by rw [hm]; tauto)]
  · intro t ht
    rw [hM, ← ht, hin, inv_mul_cancel, one_mul, hone, hout s hs]
end

section

open UpperTheory.V.AlgebraTools

private lemma indSymp_two {R : Type} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A.transpose * !![0, 1; -1, 0] * A = A.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem UpperTheory.V.AlgebraTools.indSymp :
    ∀ {R G : Type} [CommRing R] [Group G] (H : Subgroup G) (s : G), H.index = 2 → s ∉ H → ∀ (r : H →* GL (Fin 2) R) (θ : G →* Rˣ) (I : G →* GL (Fin 2 ⊕ Fin 2) R), (∀ h : H, (r h : Matrix (Fin 2) (Fin 2) R).det = θ h) → (∀ h h' : H, (h' : G) = s⁻¹ * h * s → (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = Matrix.fromBlocks (r h : Matrix (Fin 2) (Fin 2) R) 0 0 (r h' : Matrix (Fin 2) (Fin 2) R)) → (∀ t : H, (t : G) = s * s → (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = Matrix.fromBlocks 0 (r t : Matrix (Fin 2) (Fin 2) R) 1 0) → ∀ g, (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * Matrix.fromBlocks !![0, 1; -1, 0] 0 0 ((θ s : R) • !![0, 1; -1, 0]) * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ g : R) • Matrix.fromBlocks !![0, 1; -1, 0] 0 0 ((θ s : R) • !![0, 1; -1, 0]) := by
  intro R G _ _ H s hi hs r θ I hdet hH hS
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hi
  set J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0] with hJ
  have h2 : ∀ A : Matrix (Fin 2) (Fin 2) R, A.transpose * J * A = A.det • J :=
    fun A => indSymp_two A
  set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
    Matrix.fromBlocks J 0 0 ((θ s : R) • J) with hB
  have key1 : ∀ h ∈ H, (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
      (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ h : R) • B := by
    intro h hh
    have hh' : s⁻¹ * h * s ∈ H := by simpa using hN.conj_mem h hh s⁻¹
    have e := hH ⟨h, hh⟩ ⟨_, hh'⟩ rfl
    have d1 := hdet ⟨h, hh⟩
    have d2 := hdet ⟨_, hh'⟩
    have d3 : θ (s⁻¹ * h * s) = θ h := by
      simp only [map_mul, map_inv]
      rw [mul_right_comm, inv_mul_cancel, one_mul]
    simp only [d3] at d1 d2 e
    rw [e, hB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      smul_zero, Matrix.mul_smul, Matrix.smul_mul, h2, d1, d2]
    rw [smul_comm (θ s : R)]
  have key2 : (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
      (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ s : R) • B := by
    have ht : s * s ∈ H := Subgroup.mul_self_mem_of_index_two hi s
    have e := hS ⟨_, ht⟩ rfl
    have d := hdet ⟨_, ht⟩
    simp only [map_mul, Units.val_mul] at d
    rw [e, hB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      smul_zero, Matrix.mul_smul, Matrix.smul_mul, h2, d, smul_smul]
  intro g
  by_cases hg : g ∈ H
  · exact key1 g hg
  · have hh : g * s⁻¹ ∈ H := by
      rw [Subgroup.mul_mem_iff_of_index_two hi]
      simp [hg, hs]
    have eg : g = (g * s⁻¹) * s := by group
    have k := key1 _ hh
    generalize g * s⁻¹ = h at eg k
    subst eg
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.transpose_mul]
    calc _ = (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose *
          ((I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
          (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) *
          (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [k, Matrix.mul_smul, Matrix.smul_mul, key2, smul_smul]
end
