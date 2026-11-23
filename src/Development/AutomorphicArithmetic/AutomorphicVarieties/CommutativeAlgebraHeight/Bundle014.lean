module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle011
public import Mathlib.Algebra.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle007
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
import Mathlib.RingTheory.TwoSidedIdeal.Instances
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem UpperTheory.V.CA.d_tr_coeff {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (x : E) (i : ℕ) (hi : i ≤ n) : (D.D A[X] (1 + X ⊗ₜ x)).coeff i = D.lam i x := by
  rw [(d_chi D x).2.2.1, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff, hi]

private theorem UpperTheory.V.CA.d_tr_dual {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (hn : 1 ≤ n) (x : E) :
    D.D (DualNumber A) (1 + DualNumber.eps ⊗ₜ x) = 1 + D.tr x • DualNumber.eps := by
  have h := D.nat A[X] (DualNumber A) (aeval DualNumber.eps) (1 + X ⊗ₜ x)
  rw [map_add (f := _), map_one, Algebra.TensorProduct.map_tmul, aeval_X, AlgHom.id_apply] at h
  rw [h, (d_chi D x).2.2.1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', (d_chi D x).1]
  have h2 : ∀ k : ℕ, (DualNumber.eps : DualNumber A) ^ (k + 1 + 1) = 0 := fun k => by
    rw [pow_succ, pow_succ, mul_assoc, DualNumber.eps_mul_eps, mul_zero]

  simp only [map_add (f := _), map_sum, map_mul, map_pow, aeval_X, aeval_C, h2, mul_zero, Finset.sum_const_zero]
  simp [Det.tr, Algebra.smul_def, add_comm]

theorem UpperTheory.V.CA.d_tr :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (1 ≤ n → ∃ t : E →ₗ[A] A, ∀ x, t x = D.tr x) ∧ (∀ i x y, D.lam i (x * y) = D.lam i (y * x)) ∧ (1 ≤ n → D.tr 1 = n) := by
  intro n A E _ _ _ D
  refine ⟨fun hn => ⟨⟨⟨D.tr, fun x y => ?_⟩, fun a x => ?_⟩, fun _ => rfl⟩, fun i x y => ?_, fun hn => ?_⟩
  · have h : (1 + DualNumber.eps ⊗ₜ (x + y) : DualNumber A ⊗[A] E) =
        (1 + DualNumber.eps ⊗ₜ x) * (1 + DualNumber.eps ⊗ₜ y) := by
      rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, DualNumber.eps_mul_eps, zero_tmul,
        tmul_add]
      simp only [one_mul, mul_one, add_zero]
      abel
    have h2 := congrArg (D.D (DualNumber A)) h
    rw [map_mul, d_tr_dual D hn, d_tr_dual D hn, d_tr_dual D hn] at h2
    have h3 := congrArg TrivSqZeroExt.snd h2
    simpa [add_comm] using h3
  · simpa [Det.tr] using (d_chi D x).2.2.2.2.2.2 a 1 hn
  · have h : ∀ j ≤ n, D.lam j (x * y) = D.lam j (y * x) := fun j hj => by
      have := d_comm D A[X] (X ⊗ₜ x) (1 ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      rw [← d_tr_coeff D _ j hj, ← d_tr_coeff D _ j hj, this]
    have h2 : D.chi (x * y) = D.chi (y * x) := by
      rw [(d_chi D (x * y)).2.1, (d_chi D (y * x)).2.1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
    rw [Det.lam, Det.lam, h2]
  · rw [Det.tr, ← d_tr_coeff D 1 1 hn]
    have h : (1 + X ⊗ₜ 1 : A[X] ⊗[A] E) = (1 + X : A[X]) • 1 := by
      rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, add_tmul]
    simp only [h, D.homog, map_one, mul_one, coeff_one_add_X_pow, Nat.choose_one_right]
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem mem_iff {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] [Algebra A B] (D : GDet n A G)
    (x : MonoidAlgebra B G) :
    x ∈ TwoSidedIdeal.span (D.map (algebraMap A B)).CH ↔ toT A G B x ∈
      Submodule.span B ((fun z : MonoidAlgebra A G => (1 : B) ⊗ₜ[A] z) ''
        (TwoSidedIdeal.span D.CH : Set (MonoidAlgebra A G))) := by
  rw [← d_toDet_CH, ← d_toDet_CH, d_toDet_map, ← SetLike.mem_coe (p := Submodule.span B _),
    ← (d_chS D.toDet B).2.1, SetLike.mem_coe]
  obtain ⟨-, -, h1, h2⟩ := d_pull (D.toDet.baseChange B) (toT A G B)
  refine ⟨h1 x, fun h => ?_⟩
  obtain ⟨y, hy, e⟩ := (h2 fun z => ⟨_, toT_ofT z⟩).2 _ h
  have : y = x := by rw [← ofT_toT (A := A) y, e, ofT_toT]
  exact this ▸ hy

private theorem map_mem {A B : Type} [Ring A] [Ring B] (f : A →+* B) (S : Set A) (z : A)
    (hz : z ∈ TwoSidedIdeal.span S) : f z ∈ TwoSidedIdeal.span (f '' S) := by
  induction hz using TwoSidedIdeal.span_induction with
  | mem x hx => exact TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  | right_absorb b x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hx

theorem UpperTheory.V.CA.g_chmap :
    ∀ {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B), TwoSidedIdeal.span (D.map f).CH = TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' D.CH) := by
  intro n A B G _ _ _ D f
  letI : Algebra A B := f.toAlgebra
  change TwoSidedIdeal.span (D.map (algebraMap A B)).CH =
    TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap A B) '' D.CH)
  have e : ∀ z : MonoidAlgebra A G, ofT A G B (1 ⊗ₜ z) = MonoidAlgebra.mapRingHom G (algebraMap A B) z :=
    fun z => by rw [ofT_tmul, one_smul]
  apply le_antisymm
  · intro x hx
    rw [mem_iff] at hx
    rw [← ofT_toT (A := A) x]
    generalize toT A G B x = w at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [e]
      exact map_mem _ _ z hz
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_iff, ← e, toT_ofT]
    exact Submodule.subset_span ⟨z, TwoSidedIdeal.subset_span hz, rfl⟩
end
