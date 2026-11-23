module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.CharP.Lemmas
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Rt.pow_graded {k : Type} [Field k] (h : Fin 4 → ℕ) (N : M4 k)
    (hN : ∀ i j, h j ≤ h i → N i j = 0) (n : ℕ) : ∀ i j, h j < h i + n → (N ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ n ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : h m < h i + n
    · rw [ih i m hm, zero_mul]
    · rw [hN m j (by omega), mul_zero]

private theorem UpperTheory.V.Ws.Rt.pow_char_graded {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (S : Finset (ℤ × ℤ)) (h : Fin 4 → ℕ) (hl : ∀ i, h i < l) (hS : ∀ i j, i ≠ j → h j ≤ h i → wt i j ∉ S)
    (X : M4 k) (h1 : ∀ i, X i i = 1) (hX : SuppM S X) : X ^ l = 1 := by
  obtain ⟨N, hNdef⟩ : ∃ N : M4 k, N = X - 1 := ⟨_, rfl⟩
  have hXN : X = 1 + N := by rw [hNdef]; abel
  have hN : ∀ i j, h j ≤ h i → N i j = 0 := by
    intro i j hij
    rw [hNdef, Matrix.sub_apply]
    by_cases hij' : i = j
    · subst hij'
      rw [h1, Matrix.one_apply_eq, sub_self]
    · rw [hX i j hij' (hS i j hij' hij), Matrix.one_apply_ne hij', sub_self]
  have hNl : N ^ l = 0 := by
    ext i j
    rw [Matrix.zero_apply]
    exact UpperTheory.V.Ws.Rt.pow_graded h N hN l i j (by have := hl j; omega)
  haveI : CharP (Matrix (Fin 4) (Fin 4) k) l := inferInstance
  rw [hXN, add_pow_char_of_commute (p := l) (h := Commute.one_left N), one_pow, hNl, add_zero]

theorem UpperTheory.V.Ws.Rt.unipPow :
    ∀ (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (X : M4 k), (∀ i, X i i = 1) →
      ((5 ≤ l ∧ (SuppM nP X ∨ SuppM nM X)) ∨ (3 ≤ l ∧ SuppM qQ X)) → X ^ l = 1 := by
  intro k _ l _ _ X h1 h
  rcases h with ⟨hl, h | h⟩ | ⟨hl, h⟩
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l nP ![3, 1, 2, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l nM ![3, 2, 1, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l qQ ![2, 1, 1, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.muTriv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) (k : Type) [Field k] [CharP k l]
      (ψ : Γ →* k), IsLocallyConstant ψ → ∀ s ∈ muOf l H, ψ s = 1 := by
  intro l _ Γ _ _ _ H k _ _ ψ hψ s hs
  obtain ⟨-, a, ha⟩ := hs
  have hcl : IsClosed ((ψ.ker : Subgroup Γ) : Set Γ) := by
    have e : ((ψ.ker : Subgroup Γ) : Set Γ) = {x | ψ x = 1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [e]
    exact hψ.isClosed_fiber 1
  have hle : ⁅H, H⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    calc ψ g₁ * ψ g₂ * ψ g₁⁻¹ * ψ g₂⁻¹ = ψ (g₁ * g₁⁻¹) * ψ (g₂ * g₂⁻¹) := by
          rw [map_mul, map_mul]; ring
      _ = 1 := by simp
  have hm := Subgroup.topologicalClosure_minimal _ hle hcl ha
  rw [MonoidHom.mem_ker, map_pow] at hm
  have h0 : (ψ s - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, hm, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h0)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [Field k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) :
    IsUp (A * B) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hA i m h, zero_mul]
    · rw [hB m j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun m _ hm => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hm with h | h
    · rw [hA i m h, zero_mul]
    · rw [hB m i h, mul_zero]

private theorem up_inv {k : Type} [Field k] {A B : M4 k} (hA : IsUp A) (h : A * B = 1) : IsUp B := by
  have hA' : Matrix.BlockTriangular A id := fun i j hij => hA i j hij
  haveI : Invertible A := invertibleOfRightInverse A B h
  have h1 := Matrix.blockTriangular_inv_of_blockTriangular hA'
  rw [Matrix.inv_eq_right_inv h] at h1
  exact fun i j hij => h1 hij

theorem UpperTheory.V.Ws.Rt.flagMove :
    ∀ (k : Type) [Field k] (X X' Z n n' : M4 k), X * X' = 1 → IsLow n → IsLow n' → IsUp (adj n' * X * n) → IsUp (adj n * Z * n) →
      IsUp (adj n' * (X * Z * X') * n') ∧ ∀ i, (adj n' * (X * Z * X') * n') i i = (adj n * Z * n) i i := by
  intro k _ X X' Z n n' hX hn hn' hB hY
  have h1 : adj n * n = 1 := by simpa [IsGSp] using hn.1
  have h2 : adj n' * n' = 1 := by simpa [IsGSp] using hn'.1
  have h3 : n * adj n = 1 := mul_eq_one_comm.mp h1
  have h4 : ∀ W : M4 k, n * (adj n * W) = W := fun W => by rw [← mul_assoc, h3, one_mul]
  have h5 : ∀ W : M4 k, X * (X' * W) = W := fun W => by rw [← mul_assoc, hX, one_mul]
  have hBB : (adj n' * X * n) * (adj n * X' * n') = 1 := by
    simp only [mul_assoc, h4, h5, h2]
  have hB' := up_inv hB hBB
  have e : adj n' * (X * Z * X') * n' = (adj n' * X * n) * (adj n * Z * n) * (adj n * X' * n') := by
    simp only [mul_assoc, h4]
  rw [e]
  have p1 := up_mul hB hY
  have p2 := up_mul p1.1 hB'
  refine ⟨p2.1, fun i => ?_⟩
  have q := (up_mul hB hB').2 i
  rw [hBB, Matrix.one_apply_eq] at q
  rw [p2.2, p1.2]
  linear_combination (-(adj n * Z * n) i i) * q
end
