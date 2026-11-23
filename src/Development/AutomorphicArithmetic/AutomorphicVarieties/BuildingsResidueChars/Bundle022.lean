module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem one_tmul_add_tmul_mul_I_eq_smul_of_sq_eq_one {R : Type} [CommRing R] [Algebra ℝ R] (g : ℂ →ₗ[ℝ] R) (σ z : ℂ)
    (hσ : σ * σ = 1) :
    (1 : ℂ) ⊗ₜ[ℝ] g z + (σ * Complex.I) ⊗ₜ[ℝ] g (z * Complex.I) =
      ((z.re : ℂ) - σ * z.im * Complex.I) •
        ((1 : ℂ) ⊗ₜ[ℝ] g 1 + (σ * Complex.I) ⊗ₜ[ℝ] g Complex.I) := by
  have h1 : g z = z.re • g 1 + z.im • g Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    apply Complex.ext <;> simp
  have h2 : g (z * Complex.I) = z.re • g Complex.I + (-z.im) • g 1 := by
    rw [← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    apply Complex.ext <;> simp
  have hc : ∀ (c : ℂ) (u : R), c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
    intro c u
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, h2]
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul]
  rw [hc (σ * Complex.I) (g 1), hc (σ * Complex.I) (g Complex.I)]
  simp only [← algebraMap_smul ℂ z.re, ← algebraMap_smul ℂ z.im, ← algebraMap_smul ℂ (-z.im)]
  match_scalars <;> simp only [Complex.coe_algebraMap, Complex.ofReal_neg] <;>
    first
    | ring1
    | linear_combination (z.im * σ * σ) * Complex.I_mul_I - z.im * hσ

private theorem idem_lemma_2 (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    Nonempty (Idem ((A → ℝ) × (B → ℂ)) (A ⊕ (B × Bool))) := by
  let σ : Bool → ℂ := fun s => if s then 1 else -1
  have hσ : ∀ s, σ s * σ s = 1 := by
    intro s
    cases s <;> simp [σ]
  let g : B → ℂ →ₗ[ℝ] ((A → ℝ) × (B → ℂ)) := fun b =>
    (LinearMap.inr ℝ (A → ℝ) (B → ℂ)).comp (LinearMap.single ℝ (fun _ : B => ℂ) b)
  have hg : ∀ b w, g b w = ((0 : A → ℝ), Pi.single b w) := fun b w => rfl
  have hgmul : ∀ b u v, g b u * g b v = g b (u * v) := by
    intro b u v
    rw [hg, hg, hg]
    refine Prod.ext (by simp) (funext fun i => ?_)
    by_cases h : i = b
    · subst h
      simp
    · simp [h]
  have hgmul' : ∀ b b' u v, b ≠ b' → g b u * g b' v = 0 := by
    intro b b' u v hb
    rw [hg, hg]
    refine Prod.ext (by simp) (funext fun i => ?_)
    by_cases h : i = b
    · subst h
      simp [hb]
    · simp [h]
  have hc : ∀ (c : ℂ) (u : (A → ℝ) × (B → ℂ)), c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
    intro c u
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨{
    e := Sum.elim (fun a => (1 : ℂ) ⊗ₜ[ℝ] ((Pi.single a 1, 0) : (A → ℝ) × (B → ℂ)))
      (fun p => (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g p.1 1 + (σ p.2 * Complex.I) ⊗ₜ[ℝ] g p.1 Complex.I))
    ch := Sum.elim
      (fun a => (algebraMap ℝ ℂ).comp ((Pi.evalRingHom (fun _ : A => ℝ) a).comp (RingHom.fst _ _)))
      (fun p => if p.2 then (starRingEnd ℂ).comp ((Pi.evalRingHom (fun _ : B => ℂ) p.1).comp (RingHom.snd _ _))
        else (Pi.evalRingHom (fun _ : B => ℂ) p.1).comp (RingHom.snd _ _))
    mul_e := ?_
    orth := ?_
    sum := ?_ }⟩
  · rintro (a | ⟨b, s⟩) x
    · simp only [Sum.elim_inl, RingHom.comp_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have hx : x * ((Pi.single a 1, 0) : (A → ℝ) × (B → ℂ)) =
          x.1 a • ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        by_cases h : i = a
        · subst h
          simp
        · simp [h]
      rw [hx, TensorProduct.tmul_smul, algebraMap_smul]
      rfl
    · simp only [Sum.elim_inr]
      rw [mul_smul_comm, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp only [one_mul]
      have hx : ∀ w : ℂ, x * g b w = g b (x.2 b * w) := by
        intro w
        rw [hg, hg]
        refine Prod.ext (by simp) (funext fun i => ?_)
        by_cases h : i = b
        · subst h
          simp
        · simp [h]
      rw [hx, hx, mul_one, one_tmul_add_tmul_mul_I_eq_smul_of_sq_eq_one (g b) (σ s) (x.2 b) (hσ s), smul_comm]
      congr 1
      cases s
      · simp [σ]
        all_goals (apply Complex.ext <;> simp)
      · simp [σ]
        all_goals (apply Complex.ext <;> simp)
  · rintro (a | ⟨b, s⟩) (a' | ⟨b', s'⟩) hne
    · have ha : a ≠ a' := fun h => hne (by rw [h])
      simp only [Sum.elim_inl]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) * (Pi.single a' 1, 0) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        by_cases h : i = a
        · subst h
          simp [ha]
        · simp [h]
      rw [h0, TensorProduct.tmul_zero]
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [mul_smul_comm, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ∀ w, ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) * g b' w = 0 := by
        intro w
        rw [hg]
        exact Prod.ext (by simp) (by simp)
      rw [h0, h0]
      simp
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [smul_mul_assoc, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ∀ w, g b w * ((Pi.single a' (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) = 0 := by
        intro w
        rw [hg]
        exact Prod.ext (by simp) (by simp)
      rw [h0, h0]
      simp
    · simp only [Sum.elim_inr]
      rw [smul_mul_smul_comm]
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul]
      by_cases hb : b = b'
      · subst hb
        have hs : s ≠ s' := fun h => hne (by rw [h])
        have hc2 : ∀ (c d : ℂ) (u : (A → ℝ) × (B → ℂ)), (c * d) ⊗ₜ[ℝ] u = (c * d) • ((1 : ℂ) ⊗ₜ[ℝ] u) :=
          fun c d u => hc _ _
        simp only [hgmul, hc2]
        simp only [mul_one, one_mul, Complex.I_mul_I, map_neg, TensorProduct.tmul_neg]
        cases s <;> cases s' <;> simp only [ne_eq, not_true_eq_false, Bool.false_eq_true,
          not_false_eq_true, Bool.true_eq_false] at hs <;> simp only [σ, if_true, Bool.false_eq_true, if_false] <;>
          match_scalars <;>
          first
          | ring1
          | linear_combination (1 / 4 : ℂ) * Complex.I_mul_I
          | linear_combination (-1 / 4 : ℂ) * Complex.I_mul_I
      · simp only [hgmul' b b' _ _ hb, TensorProduct.tmul_zero, add_zero, smul_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool]
    have hb : ∀ b, (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g b 1 + (σ true * Complex.I) ⊗ₜ[ℝ] g b Complex.I) +
        (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g b 1 + (σ false * Complex.I) ⊗ₜ[ℝ] g b Complex.I) =
        (1 : ℂ) ⊗ₜ[ℝ] g b 1 := by
      intro b
      rw [hc (σ true * Complex.I), hc (σ false * Complex.I)]
      simp only [σ, if_true, Bool.false_eq_true, if_false]
      module
    simp only [hb]
    rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_add,
      Algebra.TensorProduct.one_def]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [hg, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [hg, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem UpperTheory.exists_idempotent_decomposition_mixedSpace :
    ∀ (K : Type) [Field K] [NumberField K], ∃ (ι : Type) (_ : Fintype ι), Nonempty (Idem (mixedSpace K) ι) := by
  intro K _ _
  classical
  exact ⟨_, inferInstance, idem_lemma_2 {w : InfinitePlace K // w.IsReal} {w : InfinitePlace K // w.IsComplex}⟩
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem single_comm {R : Type} [CommRing R] {n : ℕ} (i j k m : Fin n) (x y : R) :
    (Matrix.single i j x * Matrix.single k m y : Matrix (Fin n) (Fin n) R) =
      if j = k then Matrix.single i m (x * y) else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_single_same _ _ _ _ _
  · ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hj : j = t
    · subst hj
      simp only [Ne.symm h, false_and, if_false, mul_zero]
    · simp [hj]

private theorem unitMap_comm {R : Type} [CommRing R] [Algebra ℝ R] {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (hl : IsLie l) (i j k m : Fin n)
    (a b : ℂ ⊗[ℝ] R) :
    unitMap l i j a * unitMap l k m b - unitMap l k m b * unitMap l i j a =
      (if j = k then unitMap l i m (a * b) else 0) - (if m = i then unitMap l k j (a * b) else 0) := by
  have hmain : ∀ (c d : ℂ) (x y : R),
      unitMap l i j (c ⊗ₜ x) * unitMap l k m (d ⊗ₜ y) - unitMap l k m (d ⊗ₜ y) * unitMap l i j (c ⊗ₜ x) =
        (if j = k then unitMap l i m ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) -
          (if m = i then unitMap l k j ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) := by
    intro c d x y
    simp only [unitMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, smul_mul_smul_comm]
    rw [mul_comm d c, ← smul_sub, hl, single_comm, single_comm, mul_comm y x]
    split_ifs <;> simp [map_sub, smul_sub]
  rw [← sub_eq_zero]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul d y => rw [sub_eq_zero]; exact hmain c d x y
    | add b₁ b₂ h₁ h₂ =>
      have h := congrArg₂ (· + ·) h₁ h₂
      simp only [add_zero] at h
      refine Eq.trans ?_ h
      split_ifs <;> simp only [map_add (f := _), mul_add, add_mul] <;> abel
  | add a₁ a₂ h₁ h₂ =>
    have h := congrArg₂ (· + ·) h₁ h₂
    simp only [add_zero] at h
    refine Eq.trans ?_ h
    split_ifs <;> simp only [map_add (f := _), mul_add, add_mul] <;> abel

theorem UpperTheory.gen_glRelations_and_commute_of_isLie :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A), IsLie l → (∀ τ, Formalism.REAL.GlRel (gen D l τ)) ∧ ∀ τ σ, τ ≠ σ → ∀ i j k m, Commute (gen D l τ i j) (gen D l σ k m) := by
  intro R _ _ ι _ n A _ _ _ _ D l hl
  have idem : ∀ τ, D.e τ * D.e τ = D.e τ := by
    intro τ
    calc D.e τ * D.e τ = D.e τ * ∑ σ, D.e σ := by
          rw [Finset.mul_sum, Finset.sum_eq_single τ]
          · intro σ _ h
            exact D.orth τ σ (Ne.symm h)
          · simp
      _ = D.e τ := by rw [D.sum, mul_one]
  refine ⟨fun τ => ?_, fun τ σ h i j k m => ?_⟩
  · intro a b c d
    simp only [gen]
    rw [unitMap_comm l hl, idem]
  · unfold Commute SemiconjBy
    rw [← sub_eq_zero]
    simp only [gen]
    rw [unitMap_comm l hl, D.orth τ σ h]
    simp
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have h0 : ext0 (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a) (Fin.castAdd s c) =
          ((m : Matrix (Fin r) (Fin r) R) - 1) a c :=
        matrixExtendByZero_apply (e1 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply,
        Matrix.one_apply, Fin.castAdd_inj]
      ring
    | right d =>
      have := matrixExtendByZero_apply_of_outside_col (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a)
        (j := Fin.natAdd r d) (fun k h => cn_ne k d (by simpa [e1] using h.symm))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne]
  | right b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (i := Fin.natAdd r b)
      (fun k h => cn_ne k b (by simpa [e1] using h.symm)) j
    induction j using Fin.addCases with
    | left c => simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | right a =>
    induction j using Fin.addCases with
    | right c =>
      have h0 : ext0 (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a) (Fin.natAdd r c) =
          ((m : Matrix (Fin s) (Fin s) R) - 1) a c :=
        matrixExtendByZero_apply (e2 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
        Matrix.one_apply, Fin.natAdd_inj]
      ring
    | left d =>
      have := matrixExtendByZero_apply_of_outside_col (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a)
        (j := Fin.castAdd s d) (fun k h => cn_ne d k (by simpa [e2] using h))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne d a).symm]
  | left b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (i := Fin.castAdd s b)
      (fun k h => cn_ne b k (by simpa [e2] using h)) j
    induction j using Fin.addCases with
    | right c => simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne b c]
    | left d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩, ?_⟩
  ext i j
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply]
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have : ¬ (r ≤ ((Fin.castAdd s c : Fin (r + s)) : ℕ)) := by simp
      simp [this, Matrix.reindex_apply, Matrix.one_apply]
    | right d =>
      have h : ((Fin.castAdd s a : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r d : Fin (r + s)) : ℕ) := by
        simp
      rw [dite_eq_left h]
      simp [Matrix.reindex_apply, Matrix.one_apply, cn_ne]
  | right b =>
    have : ¬ (((Fin.natAdd r b : Fin (r + s)) : ℕ) < r) := by simp
    induction j using Fin.addCases with
    | left c => simp [this, Matrix.reindex_apply, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [this, Matrix.reindex_apply, Matrix.one_apply]

theorem UpperTheory.upperTriangular_eq_unipotent_mul_levi :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (b : GL (Fin (r + s)) R), b.val.IsUpperTriangular → ∃ (X : UPos (r + s) r → R) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), b = unipGL X * blk m₁ m₂ := by
  intro R _ r s b hb
  set M : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm b.val with hMdef
  have hC : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hMdef, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply hb
    simp [Fin.lt_def]
    omega
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hC]
    exact (Matrix.fromBlocks_toBlocks M).symm
  have hbM : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
    simp [hMdef]
  have hdet : IsUnit (Matrix.det M) := by
    rw [hMdef, Matrix.det_reindex_self]
    exact (Matrix.GeneralLinearGroup.det b).isUnit
  rw [hM, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit M.toBlocks₂₂.det := isUnit_of_mul_isUnit_right hdet
  obtain ⟨X, hX⟩ := unip_val (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹)
  refine ⟨X, Matrix.nonsingInvUnit _ hA, Matrix.nonsingInvUnit _ hD, ?_⟩
  have hmul : ∀ P Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv P * Matrix.reindex finSumFinEquiv finSumFinEquiv Q =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (P * Q) := by
    intro P Q
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  apply Units.ext
  rw [Units.val_mul, coe_unipGL, hX, blk, Units.val_mul, block_embedding_first_val, block_embedding_second_val, hbM, ← mul_assoc, hmul, hmul]
  congr 1
  conv_lhs => rw [hM]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have h1 : (Matrix.nonsingInvUnit _ hA : Matrix (Fin r) (Fin r) R) = M.toBlocks₁₁ := rfl
  have h2 : (Matrix.nonsingInvUnit _ hD : Matrix (Fin s) (Fin s) R) = M.toBlocks₂₂ := rfl
  rw [h1, h2]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem vecMul_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [CommRing R] (g : GL (Fin a) R) (y : Fin n → R) :
    y ᵥ* (emb e g).val = y + ((fun i => y (e i)) ᵥ* g.val - fun i => y (e i)) ᵥ* (inc e R)ᵀ := by
  have h : y ᵥ* inc e R = fun i => y (e i) := by
    ext i
    simp [inc, vecMul, dotProduct]
  rw [coe_emb, vecMul_add, vecMul_one, ext0, ← vecMul_vecMul, ← vecMul_vecMul, h, vecMul_sub, vecMul_one]

private theorem norm_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [NormedField R] (g : GL (Fin a) R)
    (hg : ∀ y, Reduction.euclidNorm (y ᵥ* g.val) = Reduction.euclidNorm y) (y : Fin n → R) :
    Reduction.euclidNorm (y ᵥ* (emb e g).val) = Reduction.euclidNorm y := by
  have h := hg fun i => y (e i)
  unfold Reduction.euclidNorm at h ⊢
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h
  congr 1
  rw [← Finset.sum_add_sum_compl (Finset.univ.map e), ← Finset.sum_add_sum_compl (Finset.univ.map e),
    Finset.sum_map, Finset.sum_map, ← h, vecMul_emb]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) (e j) = z j := fun z => by simp [inc, vecMul, dotProduct]
    rw [Pi.add_apply, this, Pi.sub_apply, add_sub_cancel]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : ∀ k, j ≠ e k := fun k hk => by simp [hk] at hj
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) j = 0 := fun z => by simp [inc, vecMul, dotProduct, hj']
    rw [Pi.add_apply, this, add_zero]

private theorem emb_transfer {a n : ℕ} (e : Fin a ↪ Fin n) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (g : GL (Fin a) R) (g' : GL (Fin a) S) (h' : GL (Fin n) S) (hg : ∀ i j, g'.val i j = f (g.val i j))
    (hh : ∀ i j, h'.val i j = f ((emb e g).val i j)) : h' = emb e g' := by
  have h1 : g' = Matrix.GeneralLinearGroup.map f g := Units.ext (Matrix.ext hg)
  have h2 : h' = Matrix.GeneralLinearGroup.map f (emb e g) := Units.ext (Matrix.ext hh)
  rw [h1, h2, emb_map]

private theorem int_emb {a n : ℕ} (e : Fin a ↪ Fin n) {F : Type} [Field F] [ValuativeRel F] (g : GL (Fin a) F)
    (hg : g ∈ GLnLocal.integralGL F a) : emb e g ∈ GLnLocal.integralGL F n := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨emb e u, emb_transfer e (ValuativeRel.valuation F).integer.subtype u _ _ (fun _ _ => rfl) (fun _ _ => rfl)⟩

theorem UpperTheory.blockEmbedding_adelic_norm_compat :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), ∀ k ∈ Reduction.maxCompact (K := K) (n := a), emb e k ∈ Reduction.maxCompact (K := K) (n := n) := by
  intro K _ _ a n e k hk
  rw [Reduction.mem_maxCompact] at hk ⊢
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [emb_transfer e (Reduction.infEval w) k (Reduction.infAt w k) (Reduction.infAt w (emb e k))
      (fun i j => Reduction.infAt_apply w k i j) (fun i j => Reduction.infAt_apply w _ i j), Reduction.mem_archCompact]
    exact norm_emb e _ (Reduction.mem_archCompact.1 (hk.1 w))
  · rw [emb_transfer e (Reduction.finEval v) k (Reduction.finAt v k) (Reduction.finAt v (emb e k))
      (fun i j => Reduction.finAt_apply v k i j) (fun i j => Reduction.finAt_apply v _ i j)]
    exact int_emb e _ (hk.2 v)
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.uAction_mem_unipotentInvariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (u : UEnv K n), ∀ ψ ∈ NInv K n r, uAction u ψ ∈ NInv K n r := by
  intro K _ _ n r u ψ hψ X g
  have h : ∀ y, ψ.1 (unipGL X * y) = ψ.1 y := hψ X
  have e : sliceL (unipGL X * g) ψ = sliceL g ψ :=
    Subtype.ext (funext fun x => by simp only [coe_sliceL, archSlice_apply, mul_assoc, h])
  simp only [coe_uAction, uActFun, e]
end
