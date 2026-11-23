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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def LowZ {n : ℕ} {R : Type} [CommRing R] (r : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0

private theorem LowZ.mul {n r : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : LowZ r M) (hN : LowZ r N) : LowZ r (M * N) := fun i j hi hj => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (k : ℕ) r with hk | hk
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j hk hj, mul_zero]

private theorem lower_zero_first_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin r) R) :
    LowZ r (emb (e1 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, extendByZero_apply_eq_zero_of_row_not_mem, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem lower_zero_second_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin s) R) :
    LowZ r (emb (e2 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, matrixExtendByZero_apply_of_outside_col, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem blockEntry_eq_sum {n r : ℕ} {S : Type} [CommRing S] (Y : UPos n r → S) :
    blockEntry Y = ∑ q : UPos n r, Matrix.single q.1.1 q.1.2 (Y q) := by
  ext i j
  rw [blockEntry_apply, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i, j), h⟩ : UPos n r)]
    · simp
    · intro q _ hq
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hq rfl
    · simp
  · symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h q.2

private theorem conj_blockEntry {n r : ℕ} {S : Type} [CommRing S] {M N : Matrix (Fin n) (Fin n) S}
    (hM : LowZ r M) (hN : LowZ r N) (Y : UPos n r → S) :
    M * blockEntry Y * N = blockEntry (fun p : UPos n r => ∑ q : UPos n r, M p.1.1 q.1.1 * N q.1.2 p.1.2 * Y q) := by
  ext i j
  have h0 : (M * blockEntry Y * N) i j = ∑ q : UPos n r, M i q.1.1 * N q.1.2 j * Y q := by
    rw [blockEntry_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_zero, ite_and, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_mul, zero_mul]
    ring
  rw [h0, blockEntry_apply]
  split_ifs with h
  · rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    rcases lt_or_ge (i : ℕ) r with hi | hi
    · rw [hN _ j q.2.2 (by omega), mul_zero, zero_mul]
    · rw [hM i _ hi q.2.1, zero_mul, zero_mul]

theorem UpperTheory.blockDiag_conj_unipotent_linear :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), ∃ c : UPos (r + s) r → UPos (r + s) r → R, ∀ (S : Type) [CommRing S] (f : R →+* S) (Y : UPos (r + s) r → S), Matrix.GeneralLinearGroup.map f (blk m₁ m₂) * unipGL Y = unipGL (fun p => ∑ q, f (c p q) * Y q) * Matrix.GeneralLinearGroup.map f (blk m₁ m₂) := by
  intro R _ r s m₁ m₂
  have h1 : LowZ r (blk m₁ m₂).val := (lower_zero_first_block_embedding m₁).mul (lower_zero_second_block_embedding m₂)
  have h2 : LowZ r ((blk m₁ m₂)⁻¹).val := by
    rw [blk, _root_.mul_inv_rev, ← map_inv, ← map_inv]
    exact (lower_zero_second_block_embedding _).mul (lower_zero_first_block_embedding _)
  generalize blk m₁ m₂ = m at h1 h2
  refine ⟨fun p q => m.val p.1.1 q.1.1 * (m⁻¹).val q.1.2 p.1.2, fun S _ f Y => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← map_inv]
  refine Units.ext ?_
  have hmm : m.val.map f * (m⁻¹).val.map f = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
  have h1' : LowZ r (m.val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h1 i j hi hj, map_zero]
  have h2' : LowZ r ((m⁻¹).val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h2 i j hi hj, map_zero]
  change m.val.map f * (1 + blockEntry Y) * (m⁻¹).val.map f = 1 + blockEntry _
  rw [mul_add, add_mul, mul_one, hmm, conj_blockEntry h1' h2']
  simp only [Matrix.map_apply, map_mul]
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.lieMap_eq_sum_idempotent_gen :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (X : Matrix (Fin n) (Fin n) R), l X = ∑ τ, ∑ i, ∑ j, D.ch τ (X i j) • gen D l τ i j := by
  intro R _ _ ι _ n A _ _ _ _ D l X
  have key : ∀ i j, ∑ τ, D.ch τ (X i j) • gen D l τ i j = l (Matrix.single i j (X i j)) := by
    intro i j

    simp only [gen, ← map_smul, ← map_sum, ← D.mul_e, ← Finset.mul_sum, D.sum, mul_one,
    unitMap_tmul, one_smul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]

  simp only [key, ← map_sum]
  congr 1
  exact Matrix.matrix_eq_sum_single X
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exp_block_extension (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) (Y : ArchMatrix K a) :
    (1 : ArchMatrix K n) + (show ArchMatrix K n from ext0 (R := mixedSpace K) e (NormedSpace.exp Y - 1 : ArchMatrix K a)) =
      NormedSpace.exp (show ArchMatrix K n from ext0 (R := mixedSpace K) e Y) := by
  have hsm : ∀ (c : ℝ) (Z : Matrix (Fin a) (Fin a) (mixedSpace K)), ext0 e (c • Z) = c • ext0 e Z := by
    intro c Z
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul]
  let g : ArchMatrix K a →ₗ[ℝ] ArchMatrix K n :=
    { toFun := fun X => ext0 (R := mixedSpace K) e X
      map_add' := fun X Z => matrixExtendByZero_add e X Z
      map_smul' := fun c X => hsm c X }
  have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hpow : ∀ k : ℕ, (g Y) ^ (k + 1) = g (Y ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ Y (k + 1)]
      exact matrixExtendByZero_mul e _ _
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map g hg
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (g Y)
  have h3 : HasSum (fun k : ℕ => if k = 0 then (1 - g 1 : ArchMatrix K n) else 0) (1 - g 1) :=
    hasSum_ite_eq 0 _
  have h4 := h1.add h3
  have heq : (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (g Y) ^ k) =
      fun k : ℕ => g (((k.factorial : ℝ)⁻¹) • Y ^ k) + if k = 0 then (1 - g 1) else 0 := by
    funext k
    cases k with
    | zero => simp
    | succ k => rw [if_neg (Nat.succ_ne_zero k), add_zero, map_smul, hpow]
  rw [heq] at h2
  have h5 := h2.unique h4
  have hsub : g (NormedSpace.exp Y - 1) = g (NormedSpace.exp Y) - g 1 := map_sub g _ _
  change (1 : ArchMatrix K n) + g (NormedSpace.exp Y - 1) = NormedSpace.exp (g Y)
  rw [hsub, h5]
  abel

private theorem UpperTheory.prodEquiv_apply_eq_map_fst_snd (K : Type) [Field K] [NumberField K] (m : ℕ)
    (g : AdelicGLn.AdelicGL K m) :
    AdelicGLn.prodEquiv K m g =
      (GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  ext i j <;> rfl

private theorem UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace (K : Type) [Field K] [NumberField K] (m : ℕ) (x : archGroup K m) :
    (archEquiv K m).symm x =
      GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom
        (show GL (Fin m) (mixedSpace K) from (x : (ArchMatrix K m)ˣ)) := by
  ext i j
  rfl

theorem UpperTheory.blockEmbedding_comm_infEmb_and_exp :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ x, emb e (infEmb K a x) = infEmb K n (embArch e x)) ∧ ∀ Y : Matrix (Fin a) (Fin a) (mixedSpace K), embArch e ((isExpLieAlgebra K a).expG ((isExpLieAlgebra K a).ofLie (toLie K a Y))) = (isExpLieAlgebra K n).expG ((isExpLieAlgebra K n).ofLie (toLie K n (ext0 e Y))) := by
  intro K _ _ a n e
  refine ⟨fun x => ?_, fun Y => ?_⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    have hx := prodEquiv_infEmb (K := K) (n := a) x
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd] at hx
    rw [Prod.mk.injEq] at hx
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd, prodEquiv_infEmb]
    refine Prod.ext ?_ ?_
    · refine (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.1).trans ?_)
      rw [UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace, UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace]
      exact (emb_map e _ _).symm
    · exact (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.2).trans (map_one _))
  · apply Subtype.ext
    apply Units.ext
    exact exp_block_extension K e Y
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem ent_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) {c : ℝ}
    (hc : 1 ≤ c) (h : ∀ i j, ‖g.val i j‖ ≤ c) (i j : Fin n) : ‖(emb e g).val i j‖ ≤ c := by
  have hone : ∀ p q : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) p q‖ ≤ c := by
    intro p q
    rw [Matrix.one_apply]
    split_ifs <;> simp [hc, zero_le_one.trans hc]
  show ‖((emb e g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c
  rw [coe_emb, Matrix.add_apply]
  by_cases hi : ∃ k, i = e k
  · by_cases hj : ∃ l, j = e l
    · obtain ⟨k, rfl⟩ := hi
      obtain ⟨l, rfl⟩ := hj
      simp only [matrixExtendByZero_apply, Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, add_sub_cancel]
      exact h k l
    · push_neg at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ i hj, add_zero]
      exact hone i j
  · push_neg at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, add_zero]
    exact hone i j

private theorem loc_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) :
    locHeight (emb e g) ≤ locHeight g := by
  apply locHeight_le (one_le_locHeight g)
  · exact ent_le e g (one_le_locHeight g) (norm_apply_le_locHeight g)
  · intro i j
    rw [← map_inv]
    exact ent_le e g⁻¹ (one_le_locHeight g) (norm_inv_apply_le_locHeight g) i j

theorem UpperTheory.height_blockEmbedding_le :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K a), AutomorphicForm.height (emb e g) ≤ AutomorphicForm.height g := by
  classical
  intro K _ _ a n e g
  have hfin : ∀ v, Reduction.finAt v (emb e g) = emb e (Reduction.finAt v g) := by
    intro v
    show Matrix.GeneralLinearGroup.map (Reduction.finEval v) (emb e g) = _
    rw [emb_map]
    rfl
  have hinf : ∀ w, Reduction.infAt w (emb e g) = emb e (Reduction.infAt w g) := by
    intro w
    show Matrix.GeneralLinearGroup.map (Reduction.infEval w) (emb e g) = _
    rw [emb_map]
    rfl
  unfold AutomorphicForm.height
  simp only [hfin, hinf]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀
    · intro w _
      exact pow_nonneg (locHeight_pos _).le _
    · intro w _
      exact pow_le_pow_left₀ (locHeight_pos _).le (loc_le e _) _
  · have h1 := finite_mulSupport_locHeight_finAt (emb e g)
    have h2 := finite_mulSupport_locHeight_finAt g
    simp only [hfin] at h1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx]),
      finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx])]
    apply Finset.prod_le_prod₀
    · intro v _
      exact (locHeight_pos _).le
    · intro v _
      exact loc_le e _
  · exact finprod_nonneg fun v => (locHeight_pos _).le
  · exact (zero_lt_one.trans_le (one_le_prod_locHeight g)).le
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem continuous_emb' {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a n : ℕ}
    (e : Fin a ↪ Fin n) : Continuous (emb e : GL (Fin a) R → GL (Fin n) R) := by
  refine Continuous.units_map (embM (R := R) e) ?_
  change Continuous fun X : Matrix (Fin a) (Fin a) R => 1 + inc e R * (X - 1) * (inc e R)ᵀ
  exact continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)

private theorem prodEquiv_eq (K : Type) [Field K] [NumberField K] (n : ℕ) (g : AdelicGLn.AdelicGL K n) :
    AdelicGLn.prodEquiv K n g =
      (Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  refine Prod.ext ?_ ?_
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_fst K n g i j
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_snd K n g i j

private theorem prodEquiv_emb (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K a) :
    AdelicGLn.prodEquiv K n (emb e g) =
      (emb e (AdelicGLn.prodEquiv K a g).1, emb e (AdelicGLn.prodEquiv K a g).2) := by
  rw [prodEquiv_eq, prodEquiv_eq]
  exact Prod.ext
    (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)
    (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)

theorem UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ y, emb e (finEmb K a y) = finEmb K n (emb e y)) ∧ (∀ γ, emb e (AdelicGLn.diagonal K a γ) = AdelicGLn.diagonal K n (emb e γ)) ∧ Continuous (emb e : AdelicGLn.FiniteAdelicGL K a → AdelicGLn.FiniteAdelicGL K n) := by
  intro K _ _ a n e
  refine ⟨fun y => ?_, fun γ => ?_, continuous_emb' e⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    rw [prodEquiv_emb, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
  · exact (emb_map e (algebraMap K (AdeleRing (𝓞 K) K)) γ).symm
end
