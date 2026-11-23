module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Module.PID
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Galois.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Data.ZMod.QuotientGroup
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

@[expose] public section

section

open scoped TensorProduct
open Function

namespace GlobalTheory

noncomputable def crtAlgEquiv (A : Type) [CommRing A] (ι : Type) [Fintype ι] (I : ι → Ideal A)
    (hI : Pairwise (IsCoprime on I)) (hbot : ⨅ i, I i = ⊥) : A ≃ₐ[A] (Π i, A ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := (RingEquiv.quotientBot A).symm.trans
    ((Ideal.quotEquivOfEq hbot.symm).trans (Ideal.quotientInfRingEquivPiQuotient I hI)))
    (fun x => by ext i; rfl)

theorem matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A Λ _ _ _ ι _ I hI hbot n he
  classical
  let c := crtAlgEquiv A ι I hI hbot
  let e : ∀ i, (A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i) := fun i => (he i).some
  exact ⟨(Algebra.TensorProduct.rid A A Λ).symm
    |>.trans (Algebra.TensorProduct.congr AlgEquiv.refl c)
    |>.trans (Algebra.TensorProduct.piRight A A Λ (fun i => A ⧸ I i))
    |>.trans (AlgEquiv.piCongrRight (fun i => (Algebra.TensorProduct.comm A Λ (A ⧸ I i)).trans ((e i).restrictScalars A)))
    |>.trans (Matrix.piAlgEquiv A).symm
    |>.trans (AlgEquiv.mapMatrix c.symm)⟩

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem lu_diag_mul_upper {R : Type} [CommRing R] {m : ℕ} (M N : Matrix (Fin m) (Fin m) R)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) (i : Fin m) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hM i k h, zero_mul]
    · rw [hN k i h, mul_zero]
  · simp

theorem lu_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (A₁ A₂ N₁ U N₀ : Matrix (Fin m) (Fin m) R),
    (∀ i j, i < j → A₁ i j = 0) → (∀ i j, i < j → A₂ i j = 0) → (∀ i j, j < i → N₁ i j = 0) →
    (∀ i, N₁ i i = 1) → (∀ i j, j < i → U i j = 0) → (∀ i, U i i = 1) →
    (∀ i j, j < i → N₀ i j = 0) → (∀ i, N₀ i i = 1) → A₁ * A₂ * N₁ = U * N₀ → N₁ = U * N₀ := by
  intro R _ m A₁ A₂ N₁ U N₀ h1 h2 hN1 hN1d hU hUd hN0 hN0d h
  have hA : ∀ i j, i < j → (A₁ * A₂) i j = 0 := by
    intro i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge i k with hk | hk
    · rw [h1 i k hk, zero_mul]
    · rw [h2 k j (lt_of_le_of_lt hk hij), mul_zero]
  have hbt : N₁.BlockTriangular id := fun i j hij => hN1 i j hij
  have hdet : N₁.det = 1 := by
    rw [det_of_upperTriangular hbt]; simp [hN1d]
  letI : Invertible N₁ := invertibleOfIsUnitDet N₁ (by rw [hdet]; exact isUnit_one)
  have hinv : N₁⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular hbt
  have hinv' : ∀ i j, j < i → N₁⁻¹ i j = 0 := fun i j hij => hinv hij
  have hinvd : ∀ i, N₁⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (mul_inv_of_invertible N₁) i) i
    rw [lu_diag_mul_upper N₁ N₁⁻¹ hN1 hinv' i, hN1d, one_mul] at this
    simpa using this
  have hV : ∀ i j, j < i → (U * N₀) i j = 0 := by
    have : (U * N₀).BlockTriangular id :=
      BlockTriangular.mul (fun i j hij => hU i j hij) (fun i j hij => hN0 i j hij)
    exact fun i j hij => this hij
  have hVd : ∀ i, (U * N₀) i i = 1 := by
    intro i; rw [lu_diag_mul_upper U N₀ hU hN0 i, hUd, hN0d, one_mul]
  have hAeq : A₁ * A₂ = U * N₀ * N₁⁻¹ := by
    rw [← h, mul_inv_cancel_right_of_invertible]
  have hA1 : A₁ * A₂ = 1 := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [hA i j hij, one_apply_ne (ne_of_lt hij)]
    · subst hij
      rw [hAeq, lu_diag_mul_upper _ _ hV hinv' i, hVd, hinvd, one_mul, one_apply_eq]
    · rw [hAeq, one_apply_ne (ne_of_gt hij)]
      have : (U * N₀ * N₁⁻¹).BlockTriangular id :=
        BlockTriangular.mul (fun a b hab => hV a b hab) hinv
      exact this hij
  rw [hA1, one_mul] at h
  exact h

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_int_matrix_transpose_mul_eq_smul_one (s : ℕ) :
    ∃ x : Matrix (Fin 4) (Fin 4) ℤ, x.transpose * x = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
      x * x.transpose = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares s
  have h' : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (s : ℤ) := by
    exact_mod_cast h
  refine ⟨!![(a:ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring

end GlobalTheory
end

section

open scoped Matrix
open Polynomial

namespace GlobalTheory.CyclicVector

theorem exists_linearIndependent_iterates_of_linearIndependent_pow {K : Type} [Field K] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) K)
    (hg : LinearIndependent K (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → K, LinearIndependent K (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  refine ⟨v, ?_⟩
  rw [Fintype.linearIndependent_iff] at hg ⊢
  intro c hc
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have haq : aeval g q = ∑ j : Fin r, c j • g ^ (j : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [haq, Matrix.sum_mulVec]
    have hs : ∀ j : Fin r, (c j • g ^ (j : ℕ)) *ᵥ v = c j • (g ^ (j : ℕ) *ᵥ v) := fun j => by
      ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    simpa [hs] using hc
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  exact hg c (haq ▸ hq)

end GlobalTheory.CyclicVector
end

section

namespace GlobalTheory.ColumnSumLemma
open Matrix
theorem colSum {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem main : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by
  intro A _ n r C I y
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact Finsupp.notMem_support_iff.mp (fun h => hk (hl h))
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩
    · by_contra h
      exact (Finsupp.mem_support_iff.mp hk) (ha k h)
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; simp
end GlobalTheory.ColumnSumLemma
end

section

open CategoryTheory Limits

namespace GlobalTheory

theorem index_range_eq_card_ker_of_finite {D : Type} [AddCommGroup D] [Finite D] (f : D →+ D) :
    f.range.index = Nat.card f.ker := by
  have h1 := f.range.card_mul_index
  have h2 := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h2
  have h3 : 0 < Nat.card f.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left h3
  rw [h1, mul_comm, h2]

theorem card_quot_smul_eq_of_equiv_prod {M D : Type} [AddCommGroup M] [AddCommGroup D] [Finite D]
    {n : ℕ} (e : M ≃+ (Fin n → ℤ) × D) (p : ℕ) (hp : p ≠ 0) :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  let f : D →+ D := zsmulAddGroupHom (p : ℤ)
  have hf : ∀ d, f d = (p : ℤ) • d := fun d => rfl
  have hrank : Module.finrank ℤ M = n := by
    rw [e.toIntLinearEquiv.finrank_eq]
    have hD : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n → ℤ) D)) = 0 := by
      rw [Module.rank_eq_zero_iff_isTorsion]
      intro x
      refine ⟨⟨(Nat.card D : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      · exact_mod_cast (Nat.card_pos (α := D)).ne'
      · have hx : x.1.1 = 0 := x.2
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · simp [Submonoid.smul_def, hx]
        · simp [Submonoid.smul_def]
    have : Module.rank ℤ ((Fin n → ℤ) × D) = n := by
      rw [← (LinearMap.fst ℤ (Fin n → ℤ) D).rank_range_add_rank_ker, hD,
        LinearMap.range_eq_top.2 LinearMap.fst_surjective]
      simp
    simp [Module.finrank, this]
  have hker : Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(e x.1).2, ?_⟩
        invFun := fun d => ⟨e.symm (0, d.1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : (p : ℤ) • x.1 = 0 := x.2
      have := congrArg (fun y => (e y).2) hx
      simpa [hf] using this
    · have hd : (p : ℤ) • d.1 = 0 := d.2
      change (p : ℤ) • e.symm (0, d.1) = 0
      rw [← map_zsmul, Prod.smul_mk, hd, smul_zero]
      exact map_zero _
    · intro x
      have hx : (p : ℤ) • x.1 = 0 := x.2
      have h1 : (p : ℤ) • (e x.1).1 = 0 := by
        have := congrArg (fun y => (e y).1) hx
        simpa only [map_zsmul, map_zero, Prod.smul_fst, Prod.fst_zero] using this
      have h2 : (e x.1).1 = 0 := (smul_eq_zero.1 h1).resolve_left hp'
      apply Subtype.ext
      change e.symm (0, (e x.1).2) = x.1
      rw [← h2]
      exact e.symm_apply_apply _
    · intro d
      apply Subtype.ext
      simp
  have hrange : (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup =
      ((AddSubgroup.pi Set.univ fun _ : Fin n => AddSubgroup.zmultiples (p : ℤ)).prod
        f.range).comap e.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [AddSubgroup.mem_comap]
      change e ((p : ℤ) • y) ∈ _
      rw [map_zsmul]
      refine ⟨fun i _ => ⟨(e y).1 i, ?_⟩, ⟨(e y).2, rfl⟩⟩
      simp [mul_comm]
    · rintro ⟨h1, d, hd⟩
      have h1' : ∀ i, ∃ k : ℤ, k • (p : ℤ) = (e x).1 i := fun i => h1 i (Set.mem_univ i)
      choose k hk using h1'
      refine ⟨e.symm (k, d), ?_⟩
      change (p : ℤ) • e.symm (k, d) = x
      rw [← map_zsmul, AddEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => ?_) hd
      rw [← hk i]
      simp [mul_comm]
  have hq : Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup.index := rfl
  rw [hq, hrange, AddSubgroup.index_comap_of_surjective _ e.surjective, AddSubgroup.index_prod,
    AddSubgroup.index_pi, index_range_eq_card_ker_of_finite, hker, hrank, mul_comm]
  simp [Int.index_zmultiples]

theorem card_quot_prime_smul_eq_card_ker_mul_pow_finrank (M : Type) [AddCommGroup M]
    [inst : Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨n, ι, _, q, hq, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ k i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ k i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact card_quot_smul_eq_of_equiv_prod
    (e.trans ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl _)))
    p (Fact.out : p.Prime).ne_zero

end GlobalTheory
end

section

open CategoryTheory Limits

namespace GlobalTheory

theorem ideal_span_natCast_smul_top_eq_range (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    (Ideal.span {(p : ℤ)}) • (⊤ : Submodule ℤ M) =
      LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, Nat.cast_smul_eq_nsmul]

noncomputable def intQuotSpanNatLinearEquivZMod (p : ℕ) :
    (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃ₗ[ℤ] ZMod p :=
  LinearEquiv.ofBijective (Int.quotientSpanNatEquivZMod p).toRingHom.toIntAlgHom.toLinearMap
    (Int.quotientSpanNatEquivZMod p).bijective

theorem card_zmod_tensor_eq_card_quot (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  rw [← Nat.card_congr ((intQuotSpanNatLinearEquivZMod p).rTensor M).toEquiv,
    Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {(p : ℤ)})).toEquiv,
    ideal_span_natCast_smul_top_eq_range]

theorem card_zmod_tensor_eq_card_quot' : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ),
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) :=
  fun M _ _ p => card_zmod_tensor_eq_card_quot M p

end GlobalTheory
end

section

namespace GlobalTheory

theorem galois_of_finite_generating_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  intro K K' _ _ i hfin Γ _ s hs hfix
  letI := i.toAlgebra
  haveI : FiniteDimensional K K' := hfin
  let t : Γ → (K' ≃ₐ[K] K') := fun g => AlgEquiv.ofRingEquiv (f := s g) (hs g)
  let H : Subgroup (K' ≃ₐ[K] K') := Subgroup.closure (Set.range t)
  have hH : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : ∀ g, s g y = y := fun g => hy ⟨t g, Subgroup.subset_closure ⟨g, rfl⟩⟩
    obtain ⟨x, rfl⟩ := hfix y h1
    exact IntermediateField.algebraMap_mem _ x
  have hG : IsGalois K K' := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff, ← hH]
    exact IntermediateField.fixedField_le le_top
  refine ⟨hG, ?_⟩
  intro σ hσ
  have hHtop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hH, IntermediateField.fixingSubgroup_bot]
  let σ' : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := σ) hσ
  have hmem : σ' ∈ Submonoid.closure (Set.range t) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    show σ' ∈ H
    rw [hHtop]; exact Subgroup.mem_top _
  let φ : (K' ≃ₐ[K] K') →* (K' ≃+* K') :=
    { toFun := fun τ => τ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmap := Submonoid.mem_map_of_mem φ hmem
  rw [MonoidHom.map_mclosure, ← Set.range_comp] at hmap
  have hc : (φ ∘ t) = s := by
    funext g; ext y; rfl
  have hσ' : φ σ' = σ := by ext y; rfl
  rwa [hc, hσ'] at hmap

end GlobalTheory
end

section

namespace GlobalTheory

theorem _root_.GlobalTheory.finiteGalois_fractionRing_of_isFractionRing :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  intro A K L _ _ _ _ _ _ _ _ _ _ h
  let e : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  letI alg : Algebra (FractionRing A) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hmap : ∀ y : FractionRing A, algebraMap (FractionRing A) L y = algebraMap K L (e y) :=
    fun _ => rfl
  have hcomp : (algebraMap (FractionRing A) L).comp (e.symm.toRingEquiv : K →+* FractionRing A) =
      ((RingEquiv.refl L : L ≃+* L) : L →+* L).comp (algebraMap K L) := by
    ext x; simp [hmap]
  refine ⟨alg, IsScalarTower.of_algebraMap_eq fun a => ?_, ?_, ?_, ?_⟩
  · rw [hmap, AlgEquiv.commutes, h]
  · exact Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp
  · exact IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv) (g := RingEquiv.refl L) hcomp
  · intro σ x
    have := σ.commutes (e.symm x)
    simpa [hmap] using this

end GlobalTheory
end
