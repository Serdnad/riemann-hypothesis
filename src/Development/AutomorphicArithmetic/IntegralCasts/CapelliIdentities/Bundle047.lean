module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Vandermonde
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Yha6.main :
    ∀ (Λ : Type) [inst : AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ),
      (∀ (v : Λ) (n : ℤ), n ≠ (0 : ℤ) → n • v ∈ N → v ∈ N) →
        ∃ (k : ℕ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
          Function.Injective f ∧ Submodule.span ℤ (Set.range fun (i : Fin k) ↦ (b : Fin n → Λ) (f i)) = N := by
  intro Λ _ _ _ N hsat
  obtain ⟨k, snf⟩ := Submodule.smithNormalForm (Module.finBasis ℤ Λ) N
  refine ⟨k, _, snf.bM, snf.f, snf.f.injective, ?_⟩
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i h
    have h1 := snf.snf i
    rw [h, zero_smul] at h1
    exact snf.bN.ne_zero i (Subtype.ext h1)
  have hmem : ∀ i, snf.bM (snf.f i) ∈ N := by
    intro i
    apply hsat _ (snf.a i) (ha i)
    rw [← snf.snf i]
    exact (snf.bN i).2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (Set.range snf.bN) := by
      rw [snf.bN.span_eq]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span N.subtype hx'
    simp only [Submodule.subtype_apply] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Submodule.subtype_apply, snf.snf i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end

section

open Matrix

private theorem eig_sum_zero {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O) (hal : Function.Injective al)
    (u : Fin n → Fin n → O) (hu : ∀ i, A.mulVec (u i) = al i • u i) (hs : ∑ i, u i = 0) :
    ∀ i, u i = 0 := by
  have hk : ∀ k : ℕ, ∑ i, al i ^ k • u i = 0 := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih =>
      have h := congrArg A.mulVec ih
      rw [Matrix.mulVec_zero, Matrix.mulVec_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hu, smul_smul, pow_succ]
  intro i
  funext j
  have h : (fun i => u i j) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hal
    intro k
    have := congrFun (hk k) j
    simpa [Finset.sum_apply, mul_comm] using this
  exact congrFun h i

theorem UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc :
    ∀ {O : Type} [inst : CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O),
      Function.Injective al →
        A.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : O → Polynomial O) (al i)) →
          ∃ (v : Fin n → O),
            ∀ (Y : Matrix (Fin n) (Fin n) O),
              A * Y = Y * A → Y.mulVec v = (0 : Fin n → O) → Y = (0 : Matrix (Fin n) (Fin n) O) := by
  intro O _ _ n A al hal hc
  have hw : ∀ i, ∃ w : Fin n → O, w ≠ 0 ∧ A.mulVec w = al i • w := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (al i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hc, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨w, hw0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hw
    rw [← hw]
    funext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose w hw0 hw using hw
  refine ⟨∑ i, w i, fun Y hY hv => ?_⟩
  have hYw : ∀ i, Y.mulVec (w i) = 0 := by
    apply eig_sum_zero A al hal (fun i => Y.mulVec (w i))
    · intro i
      rw [Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    · rw [← Matrix.mulVec_sum, hv]
  have hdet : (Matrix.of w).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have h := eig_sum_zero A al hal (fun i => c i • w i)
      (fun i => by rw [Matrix.mulVec_smul, hw, smul_comm])
      (by
        funext j
        have := congrFun hc j
        simpa [Matrix.vecMul, dotProduct, Finset.sum_apply] using this)
    funext i
    exact (smul_eq_zero.mp (h i)).resolve_right (hw0 i)
  ext r j
  have h : Y r = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have := congrFun (hYw i) r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact congrFun h j
end

section

theorem UpperTheory.Reformulated.B.Qi37.eig_ex :
    ∀ {k : Type} [inst : Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k)
    (a : Fin n → k),
    P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : k → Polynomial k) (a i)) →
      ∀ (i : Fin n), ∃ (v : Fin n → k), v ≠ (0 : Fin n → k) ∧ P.mulVec v = a i • v := by
  intro k _ n P a h i
  have hroot : P.charpoly.eval (a i) = 0 := by
    rw [h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
  rw [← hv0]
  ext j
  simp [Matrix.mulVec_diagonal]
end

section

theorem UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt.{u_1, u_2} :
    ∀ {k : Type u_1} {ι : Type u_2} [inst : Field k] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι]
    (M : Matrix ι ι k) {c : k},
    c ≠ (0 : k) →
      (c • M).charpoly =
        (Polynomial.C : k → Polynomial k) (c ^ Fintype.card ι) *
          M.charpoly.comp ((Polynomial.C : k → Polynomial k) c⁻¹ * Polynomial.X) := by
  intro k ι _ _ _ M c hc
  have h1 : M.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) =
      ((Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)).mapMatrix M.charmatrix).det := by
    rw [← RingHom.map_det]
    rfl
  have h2 : (Polynomial.C c : Polynomial k) * Polynomial.C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_eq, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_mul]
    rw [mul_sub, ← mul_assoc, h2, one_mul]
  · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_ne _ _ _ hij, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.neg_comp, Polynomial.C_comp, Polynomial.C_mul, mul_neg]
end

section

theorem UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K),
    Function.Injective α →
      P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (α i)) →
        ∃ (V : Matrix (Fin n) (Fin n) K), IsUnit V ∧ P * V = V * Matrix.diagonal α := by
  intro K _ n P α hα hP
  have h1 : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧ P.mulVec v = α i • v := by
    intro i
    have h0 : P.charpoly.eval (α i) = 0 := by
      rw [hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using h1
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' P) α hα v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hv i
  refine ⟨(Matrix.of v).transpose, ?_, ?_⟩
  · exact Matrix.linearIndependent_cols_iff_isUnit.mp hli
  · ext j i
    have h := congrFun (hv i) j
    rw [Matrix.mul_diagonal]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
end

section

theorem UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE :
    ∀ {κ : Type} [inst : Field κ]
    (M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) (α : Fin (2 : ℕ) → κ),
    Function.Injective α →
      M.charpoly = ∏ i : Fin (2 : ℕ), (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (α i)) →
        ∃ (P : GL (Fin (2 : ℕ)) κ),
          M * (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) =
            (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) * Matrix.diagonal α := by
  intro κ _ M α hα h
  classical
  have hv : ∀ i : Fin 2, ∃ v : Fin 2 → κ, v ≠ 0 ∧ M.mulVec v = α i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin 2) (α i) - M).det = 0 := by
      rw [← Matrix.eval_charpoly, h, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) α hα v fun i =>
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hv i), hv0 i⟩
  have hu : IsUnit (Matrix.of v).transpose :=
    Matrix.linearIndependent_cols_iff_isUnit.1 hli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext j i
  have := congrFun (hv i) j
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
end

section

open scoped ContDiff

namespace UpperTheory.Reformulated.B.ConjugateOfRoots

theorem conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ := by
  have hv : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧
      (N : Matrix (Fin n) (Fin n) K).mulVec v = d i • v := by
    intro i
    have h := hN i
    rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent'
      (Matrix.toLin' (N : Matrix (Fin n) (Fin n) K)) d hd v fun i => ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv i]
  have hP : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  obtain ⟨g, hg⟩ := hP
  refine ⟨g, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hD]
  ext i j
  have h := congrFun (hv j) i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.ConjugateOfRoots
end

section

private theorem UpperTheory.valuation_perm_term {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (σ : Equiv.Perm ι) :
    v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ∏ i, v (M (σ i) i) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]

private theorem UpperTheory.valuation_det_le_one_of_entries_le_one' {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  rw [UpperTheory.valuation_perm_term]
  exact Finset.prod_le_one' fun i _ => h1 _ _

private theorem UpperTheory.val_det_eq_one_iff {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) :
    v M.det = 1 ↔ ∀ i, v (M i i) = 1 := by
  have hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 →
      v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ j hj
    rw [UpperTheory.valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj
  have hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ hσ
    have : ∃ j, j < σ j := by
      by_contra hcon
      push Not at hcon
      apply hσ
      ext i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rcases (hcon i).lt_or_eq with h | h
        · exact σ.injective (ih _ h)
        · exact h
    obtain ⟨j, hj⟩ := this
    exact hlt σ j (h2 _ _ hj)
  constructor
  · intro h i
    by_contra hne
    have hi : v (M i i) < 1 := lt_of_le_of_ne (h1 _ _) hne
    refine absurd h (ne_of_lt ?_)
    rw [Matrix.det_apply]
    refine v.map_sum_lt one_ne_zero fun σ _ => ?_
    by_cases h' : σ = 1
    · exact hlt σ i (by simpa [h'] using hi)
    · exact hσ σ h'
  · intro h
    have h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1 := by
      rw [UpperTheory.valuation_perm_term]
      exact Finset.prod_eq_one fun i _ => h i
    rw [Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]
    intro σ hσ'
    rw [h0]
    exact hσ σ (by simpa using hσ')

private theorem UpperTheory.prod_lt_of_strictMono {Γ ι : Type} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrder ι] (f : ι → Γ) (hf : StrictMono f) (h0 : ∀ i, 0 < f i) (S T : Finset ι)
    (hc : S.card = T.card) (hne : S ≠ T) (hT : ∀ i j, i ∉ T → j ∈ T → i < j) :
    ∏ i ∈ S, f i < ∏ i ∈ T, f i := by
  have hc' : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hc
  have hS : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hT' : (T \ S).Nonempty := by
    rw [← Finset.card_pos, ← hc', Finset.card_pos]
    exact hS
  obtain ⟨c, hcm, hcmax⟩ := Finset.exists_max_image (S \ T) id hS
  have key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i := by
    calc ∏ i ∈ S \ T, f i ≤ ∏ _i ∈ S \ T, f c :=
          Finset.prod_le_prod' fun i hi => hf.monotone (hcmax i hi)
      _ = ∏ _i ∈ T \ S, f c := by simp [hc']
      _ < _ := Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => h0 c)
          (fun i hi => hf (hT _ _ (Finset.mem_sdiff.1 hcm).2 (Finset.mem_sdiff.1 hi).1)) hT'
  rw [← Finset.prod_inter_mul_prod_diff S T, ← Finset.prod_inter_mul_prod_diff T S,
    Finset.inter_comm T S]
  exact mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)

theorem UpperTheory.charpoly_coeff_valuation :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ)
        (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        (∀ i j, v (M i j) ≤ 1) → (∀ i j, j < i → v (M i j) < 1) → v M.det = 1 →
        StrictMono (fun i => v (d i)) → (∀ i, d i ≠ 0) →
        ∀ k ≤ n, v ((Matrix.diagonal d * M).charpoly.coeff k) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v (d i) := by
  intro K Γ _ _ v n M d h1 h2 hdet hmono hd k hk
  have hdiag := (UpperTheory.val_det_eq_one_iff v M h1 h2).1 hdet
  have hminor : ∀ S : Finset (Fin n),
      v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det
        = (∏ i ∈ S, v (d i)) *
          v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
    intro S
    have : (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)
        = Matrix.of fun i j : S => d i *
          (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j := by
      ext i j
      simp
    rw [this, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]
  set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT
  have hcard : T.card = n - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => k ≤ i.val)
    have h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k := by
      simp only [not_le]
      rw [Fin.card_filter_val_lt, min_eq_right hk]
    rw [h', Finset.card_univ, Fintype.card_fin, ← hT] at h
    omega
  have hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n)
      (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i) := by
    rw [hminor, (UpperTheory.val_det_eq_one_iff v
      (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)) (fun i j => h1 _ _)
      (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)
  rw [Fintype.card_fin, Nat.sub_sub_self hk] at hc
  have hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n)) := by
    simp [hcard]
  rw [hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]
  intro S hS
  rw [hTval, hminor]
  simp only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS
  refine lt_of_le_of_lt
    (mul_le_of_le_one_right' (UpperTheory.valuation_det_le_one_of_entries_le_one' v _ fun i j => h1 _ _)) ?_
  refine UpperTheory.prod_lt_of_strictMono (fun i => v (d i)) hmono
    (fun i => zero_lt_iff.2 ((v.ne_zero_iff).2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_
  intro i j hi hj
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
  exact Fin.lt_def.2 (lt_of_lt_of_le hi hj)
end

section

namespace YgbHelp

private lemma detT {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    M.det = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

end YgbHelp

theorem UpperTheory.Reformulated.B.Ygb2.main :
    ∀ {R : Type} [inst : CommRing R] {r n : ℕ} (B : Matrix (Fin r) (Fin n) R) (C : Matrix (Fin n) (Fin r) R),
      (B * C).det = ∑ f : Fin r → Fin n, (∏ i : Fin r, B i (f i)) * (C.submatrix f id).det := by
  intro R inst r n B C
  rw [YgbHelp.detT]
  simp_rw [YgbHelp.detT, Matrix.mul_apply, Fintype.prod_sum, Finset.mul_sum, Matrix.submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring
end
