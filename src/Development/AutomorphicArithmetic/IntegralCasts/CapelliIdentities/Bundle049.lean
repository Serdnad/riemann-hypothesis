module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section


open Matrix in
private def Dz {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι E) : Prop :=
  ∃ g : Matrix ι ι E, g.det ≠ 0 ∧ ∃ D : ι → E, Matrix.conjTranspose g * T * g = Matrix.diagonal D

open Matrix in
private theorem Dz.of_submatrix {E ι κ : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {T : Matrix κ κ E}
    (h : Dz (T.submatrix e e)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨g.submatrix e.symm e.symm, ?_, D ∘ e.symm, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hg
  · have h1 : (g.submatrix e.symm e.symm)ᴴ * T * g.submatrix e.symm e.symm
        = (gᴴ * T.submatrix e e * g).submatrix e.symm e.symm := by
      rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _]
      simp [conjTranspose_submatrix]
    rw [h1, hD]
    ext a b
    simp [diagonal_apply]

open Matrix in
private theorem Dz.of_congr {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    {T P : Matrix ι ι E} (hP : P.det ≠ 0) (h : Dz (Pᴴ * T * P)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨P * g, ?_, D, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hP hg
  · rw [← hD, conjTranspose_mul]; simp only [Matrix.mul_assoc]

open Matrix in
private theorem Dz.sum {E A B : Type} [Field E] [StarRing E] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (hA : ∀ X : Matrix A A E, X.IsHermitian → Dz X)
    (hB : ∀ X : Matrix B B E, X.IsHermitian → Dz X)
    (T : Matrix (A ⊕ B) (A ⊕ B) E) (hT : T.IsHermitian) (hdet : T.toBlocks₁₁.det ≠ 0) :
    Dz T := by
  obtain ⟨X, Y, Z, W, rfl⟩ : ∃ X Y Z W, T = fromBlocks X Y Z W :=
    ⟨_, _, _, _, (fromBlocks_toBlocks T).symm⟩
  rw [toBlocks_fromBlocks₁₁] at hdet
  obtain ⟨h1, h2, h3, h4⟩ := (isHermitian_fromBlocks_iff).1 hT
  have hu : IsUnit X.det := isUnit_iff_ne_zero.2 hdet
  have hXX : X * X⁻¹ = 1 := mul_nonsing_inv X hu
  have hXi : X⁻¹ᴴ = X⁻¹ := by rw [conjTranspose_nonsing_inv, h1.eq]
  have hZ : Yᴴ = Z := h2
  subst hZ
  set U : Matrix (A ⊕ B) (A ⊕ B) E := fromBlocks 1 (-(X⁻¹ * Y)) 0 1 with hU
  have hUdet : U.det ≠ 0 := by
    rw [hU, det_fromBlocks_zero₂₁]; simp
  set S : Matrix B B E := W - Yᴴ * X⁻¹ * Y with hS
  have hSH : S.IsHermitian := by
    rw [IsHermitian, hS, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hXi, h4.eq, Matrix.mul_assoc]
  have key : Uᴴ * fromBlocks X Y Yᴴ W * U = fromBlocks X 0 0 S := by
    rw [hU, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hXi,
      h1.eq]
    have hXX' : X⁻¹ * X = 1 := nonsing_inv_mul X hu
    congr 1
    · simp
    · have hY : X * (X⁻¹ * Y) = Y := by rw [← Matrix.mul_assoc, hXX, Matrix.one_mul]
      simp [hY]
    · simp [Matrix.mul_assoc, hXX']
    · simp [Matrix.mul_assoc, hXX, hXX', hS, Matrix.add_mul, Matrix.mul_add]
      abel
  refine Dz.of_congr hUdet ?_
  rw [key]
  obtain ⟨gA, hgA, DA, hDA⟩ := hA X h1
  obtain ⟨gB, hgB, DB, hDB⟩ := hB S hSH
  refine ⟨fromBlocks gA (0 : Matrix A B E) (0 : Matrix B A E) gB, ?_, Sum.elim DA DB, ?_⟩
  · rw [det_fromBlocks_zero₂₁]; exact mul_ne_zero hgA hgB
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal]
    simp [hDA, hDB]

open Matrix in
private theorem Dz.pivot {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X)
    (T : Matrix ι ι E) (hT : T.IsHermitian) (i : ι) (hi : T i i ≠ 0) : Dz T := by
  let e : {a // a = i} ⊕ {a // ¬ a = i} ≃ ι := Equiv.sumCompl _
  refine Dz.of_submatrix e ?_
  refine Dz.sum ?_ (ih _ ?_) _ (hT.submatrix e) ?_
  · intro X _
    refine ⟨1, by simp, fun a => X a a, ?_⟩
    ext a b
    have : a = b := Subsingleton.elim _ _
    subst this
    simp
  · exact Fintype.card_subtype_lt (x := i) (by simp)
  · have : Unique {a // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun a => Subtype.ext a.2⟩
    rw [det_unique]
    have hdef : (((default : {a // a = i})) : ι) = i := (default : {a // a = i}).2
    simpa [e, toBlocks₁₁, hdef] using hi

open Matrix in
private theorem Dz.all {E : Type} [Field E] [StarRing E] [CharZero E] :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ T : Matrix ι ι E, T.IsHermitian → Dz T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ _ hcard T hT
  have ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X :=
    fun κ _ _ h X hX => IH _ (hcard ▸ h) κ rfl X hX
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact Dz.pivot ih T hT i hi
  push_neg at hd
  by_cases h0 : T = 0
  · subst h0
    exact ⟨1, by simp, 0, by ext i j; simp [Matrix.diagonal]⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (by ext a b; simpa using hc a b)
  have hne : j ≠ i := by
    rintro rfl
    exact hij (hd _)
  set c := (T i j)⁻¹ with hc
  set P : Matrix ι ι E := 1 + single j i c with hP
  have hPdet : P.det ≠ 0 := by
    have : P = transvection j i c := rfl
    rw [this, det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  have hji : T j i = star (T i j) := (hT.apply j i).symm
  have hval : (Pᴴ * T * P) i i = 2 := by
    have hPH : Pᴴ = 1 + single i j (star c) := by
      rw [hP, conjTranspose_add, conjTranspose_one, conjTranspose_single]
    rw [hPH, hP]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.mul_assoc, single_mul_apply_same, mul_single_apply_same]
    have h1 : T i j * c = 1 := mul_inv_cancel₀ hij
    have h2 : star c * T j i = 1 := by
      rw [hji, ← star_mul', mul_comm, h1, star_one]
    rw [h1, h2, hd i, hd j]
    norm_num
  refine Dz.of_congr hPdet (Dz.pivot ?_ _ ?_ i ?_)
  · exact ih
  · exact isHermitian_conjTranspose_mul_mul P hT
  · rw [hval]; exact two_ne_zero

theorem UpperTheory.hermitian_diagonalisation :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ i j, σ (T j i) = T i j) → T.det ≠ 0 → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), Matrix.transpose ((g : Matrix (Fin n) (Fin n) E).map σ) * T * (g : Matrix (Fin n) (Fin n) E) = Matrix.diagonal fun i => algebraMap F E (D i : F) := by
  intro F E _ _ _ _ σ hσ hfix n T hT hdet
  letI : StarRing E :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by
        show σ (a * b) = σ b * σ a
        rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hstar : ∀ x : E, star x = σ x := fun _ => rfl
  have hH : T.IsHermitian := by
    ext i j
    exact hT i j
  obtain ⟨g, hg, D, hD⟩ := Dz.all n (Fin n) (by simp) T hH
  have hct : Matrix.transpose (g.map σ) = Matrix.conjTranspose g := rfl
  have hDH : (Matrix.diagonal D).IsHermitian := by
    rw [← hD]
    have := Matrix.isHermitian_conjTranspose_mul_mul g hH
    exact this
  have hfixD : ∀ i, σ (D i) = D i := by
    intro i
    have := hDH.apply i i
    simpa [hstar] using this
  have hdD : ∀ i, D i ≠ 0 := by
    intro i h0
    have h1 : (Matrix.diagonal D).det = 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [← hD, Matrix.det_mul, Matrix.det_mul] at h1
    have h2 : (Matrix.conjTranspose g).det ≠ 0 := by
      rw [Matrix.det_conjTranspose]
      intro h3
      exact hg (by simpa using h3)
    exact mul_ne_zero (mul_ne_zero h2 hdet) hg h1
  choose d hd using fun i => hfix (D i) (hfixD i)
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    apply hdD i
    rw [← hd, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg, fun i => Units.mk0 (d i) (hd0 i), ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hg : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = g := rfl
  rw [hcoe, hct, hD]
  congr 1
  ext i
  simp [hd]
end

section

noncomputable def UpperTheory.Reformulated.B.Qe27.upperUni :
    (k : ℕ) → (A : Type) → [inst : CommRing A] → Set (GL (Fin k) A) :=
    fun (k : ℕ) (A : Type) [CommRing A] ↦
      {x : GL (Fin k) A |
        ∀ (i j : Fin k),
          (j < i → (↑x : Matrix (Fin k) (Fin k) A) i j = (0 : A)) ∧ (↑x : Matrix (Fin k) (Fin k) A) i i = (1 : A)}

private theorem UpperTheory.Reformulated.B.Qe27.diag_mul {k : ℕ} {A : Type} [CommRing A]
    (M N : Matrix (Fin k) (Fin k) A) (hM : M.BlockTriangular id) (hN : N.BlockTriangular id)
    (i : Fin k) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hM (show id j < id i from h), zero_mul]
  · rw [hN (show id i < id j from h), mul_zero]

private theorem UpperTheory.Reformulated.B.Qe27.mem_iff {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A ↔
      (x : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧
        ∀ i, (x : Matrix (Fin k) (Fin k) A) i i = 1 :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i _ => ⟨fun hij => h.1 hij, h.2 i⟩⟩

theorem UpperTheory.Reformulated.B.Qe27.closure_upperUni :
    ∀ {k : ℕ} (A : Type) [inst : CommRing A],
      ∀ x ∈ Subgroup.closure (UpperTheory.Reformulated.B.Qe27.upperUni k A), x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A := by
  intro k A _ x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff]
    exact ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  | mul y z _ _ hy hz =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy hz ⊢
    rw [Units.val_mul]
    refine ⟨hy.1.mul hz.1, fun i => ?_⟩
    rw [UpperTheory.Reformulated.B.Qe27.diag_mul _ _ hy.1 hz.1, hy.2, hz.2, one_mul]
  | inv y _ hy =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy ⊢
    have hinv : ((y⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id := by
      letI : Invertible (y : Matrix (Fin k) (Fin k) A) := y.invertible
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hy.1
    refine ⟨hinv, fun i => ?_⟩
    have h := UpperTheory.Reformulated.B.Qe27.diag_mul _ _ hy.1 hinv i
    rw [Units.mul_inv, Matrix.one_apply_eq, hy.2, one_mul] at h
    exact h.symm
end

section

noncomputable def UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR :
    {K : Type} → [inst : CommRing K] → Subring K → (n : ℕ) → Subgroup (GL (Fin n) K) :=
  fun {K} _ R n =>
  { carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ R) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ R}
    one_mem' := by
      have h : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) K) i j ∈ R := fun i j => by
        rw [Matrix.one_apply]
        split_ifs
        exacts [R.one_mem, R.zero_mem]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_one]
        exact h i j
      · rw [inv_one, Units.val_one]
        exact h i j
    mul_mem' := by
      rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (ha i k) (hb k j)
      · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (hb' i k) (ha' k j)
    inv_mem' := by
      rintro a ⟨ha, ha'⟩
      refine ⟨ha', fun i j => ?_⟩
      rw [inv_inv]
      exact ha i j }
end

section

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.irr_conj :
    ∀ {k : Type} [inst : Field k] {Γ : Type} [inst_1 : Group Γ] {n : ℕ} (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k),
      (∀ (x : Γ), (r' : Γ → GL (Fin n) k) x = g * (r : Γ → GL (Fin n) k) x * g⁻¹) →
        UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r' → UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r := by
  intro k _ Γ _ n r r' g h hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  have hgg : ∀ v : Fin n → k, (↑(g⁻¹) : Matrix (Fin n) (Fin n) k).mulVec
      ((↑g : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv r'
      (W.comap (Matrix.mulVecLin (↑(g⁻¹) : Matrix (Fin n) (Fin n) k))) := by
    intro x v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [h x, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg]
    exact hW x _ hv
  rcases hmin _ le_top hinv with h0 | h1
  · left
    rw [Submodule.eq_bot_iff] at h0 ⊢
    intro v hv
    have h2 : (↑g : Matrix (Fin n) (Fin n) k).mulVec v = 0 := by
      apply h0
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg]
      exact hv
    rw [← hgg v, h2, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h1 ⊢
    intro v
    have h2 := h1 ((↑g : Matrix (Fin n) (Fin n) k).mulVec v)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg] at h2
end

section

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.IrreducibleSubrep.irr_of_iso :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k},
      UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r → UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso r r' → UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r' := by
  intro Γ k _ _ n r r' hr hiso
  obtain ⟨hne, -, hmin⟩ := hr
  obtain ⟨g, hg⟩ := hiso
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
  have hcomm : ∀ s : Γ, (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  have hsec : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec
      (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv r
      (W'.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) := by
    intro s v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    exact hW' s _ hv
  rcases hmin _ le_top hinv with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w) (by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec]; exact hw)
    rw [← hsec w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec] at h0
end

section

noncomputable def UpperTheory.Reformulated.B.Qf5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.Qf5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Qf5.MatIrr U a → UpperTheory.Reformulated.B.Qf5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  have hcancel : ∀ w : Fin m → R,
      (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmem : ∀ v : Fin m → R,
      v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔
        (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W := fun v => Iff.rfl
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)),
      (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]
    exact hW g hg _ hv
  rcases hirr _ hinv with hb | ht
  · left
    rw [Submodule.eq_bot_iff] at hb ⊢
    intro w hw
    have h0 := hb ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) (by rw [hmem, hcancel]; exact hw)
    rw [← hcancel w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at ht ⊢
    intro w
    have h1 := (hmem _).1 (ht ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w))
    rwa [hcancel] at h1
end

section

theorem UpperTheory.Reformulated.B.Yhc6.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (m : ℕ),
      ((↑g : Matrix (Fin n) (Fin n) k) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) k)) ^ m =
        (↑g : Matrix (Fin n) (Fin n) k) * x ^ m * (↑g⁻¹ : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ _ _ n g x m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
end
