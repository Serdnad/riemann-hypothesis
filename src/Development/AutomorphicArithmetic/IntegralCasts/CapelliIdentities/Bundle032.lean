module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Qe13.aux1 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ),
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R)
          (0 : Matrix (Fin (1 : ℕ)) (Fin n) R) (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        (1 : Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R) := by
  intro R _ n
  exact Matrix.fromBlocks_one

theorem UpperTheory.Reformulated.B.Qe13.aux2 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R),
      Matrix.fromBlocks (A * B) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
          (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) *
          Matrix.fromBlocks B (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) := by
  intro R _ n A B
  rw [Matrix.fromBlocks_multiply]
  simp

noncomputable def UpperTheory.Reformulated.B.Qe13.blkHom :
    (R : Type) →
      [inst : CommRing R] → (n : ℕ) → Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R :=
    fun (R : Type) [CommRing R] (n : ℕ) ↦
      {
        toFun := fun (A : Matrix (Fin n) (Fin n) R) ↦
          Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R),
        map_one' := UpperTheory.Reformulated.B.Qe13.aux1 R n, map_mul' := UpperTheory.Reformulated.B.Qe13.aux2 R n :
        Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R }

noncomputable def UpperTheory.Reformulated.B.Qe13.embGL :
    (R : Type) → [inst : CommRing R] → (n N : ℕ) → n + (1 : ℕ) = N → GL (Fin n) R →* GL (Fin N) R :=
    fun (R : Type) [CommRing R] (n N : ℕ) (h : n + (1 : ℕ) = N) ↦
      Units.map
        ((↑(↑(Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))) :
                    Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →ₐ[R] Matrix (Fin N) (Fin N) R).toRingHom :
              Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →* Matrix (Fin N) (Fin N) R).comp
          (UpperTheory.Reformulated.B.Qe13.blkHom R n))

theorem UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A :
    ∀ {n : ℕ} (g : GL (Fin n) ℂ),
      (∀ (i j : Fin n), j < i → (↑g : Matrix (Fin n) (Fin n) ℂ) i j = (0 : ℂ)) →
        (∀ (i : Fin n), (↑g : Matrix (Fin n) (Fin n) ℂ) i i = (1 : ℂ)) →
          (Matrix.GeneralLinearGroup.det : GL (Fin (n + (1 : ℕ))) ℂ → ℂˣ)
              ((UpperTheory.Reformulated.B.Qe13.embGL ℂ n (n + (1 : ℕ)) rfl : GL (Fin n) ℂ → GL (Fin (n + (1 : ℕ))) ℂ) g) =
            (1 : ℂˣ) := by
  intro n g hlow hdiag
  have htri : (↑g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := fun i j hij => hlow i j hij
  have hg : (↑g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  apply Units.ext
  change Matrix.det (Matrix.reindex (finSumFinEquiv.trans (finCongr rfl)) (finSumFinEquiv.trans (finCongr rfl))
    (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin n) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hg, Matrix.det_one, mul_one]
end

section

open Matrix

open scoped MatrixOrder ComplexOrder in
private theorem UpperTheory.frame_pos {N j : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (K : Submodule ℂ (Fin N → ℂ)) (hS : S.IsHermitian) (hj : j ≤ Module.finrank ℂ K)
    (hK : ∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) :
    ∃ B : Matrix (Fin N) (Fin j) ℂ, Bᴴ * S * B = 1 ∧ ∀ v, B.mulVec v ∈ K := by
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank hj
  have hb' : LinearIndependent ℂ (fun i => (b i : Fin N → ℂ)) :=
    hb.map' K.subtype (Submodule.ker_subtype K)
  let C : Matrix (Fin N) (Fin j) ℂ := Matrix.of fun r i => (b i : Fin N → ℂ) r
  have hC : ∀ v, C.mulVec v = ∑ i, v i • (b i : Fin N → ℂ) := by
    intro v
    ext r
    simp [C, Matrix.mulVec, dotProduct, mul_comm]
  have hmem : ∀ v, C.mulVec v ∈ K := fun v => by
    rw [hC]
    exact K.sum_mem fun i _ => K.smul_mem _ (b i).2
  have hne : ∀ v, v ≠ 0 → C.mulVec v ≠ 0 := fun v hv h => by
    rw [hC] at h
    exact hv (funext (Fintype.linearIndependent_iff.mp hb' v h))
  have hH : (Cᴴ * S * C).IsHermitian := isHermitian_conjTranspose_mul_mul C hS
  have hG : (Cᴴ * S * C).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := hK _ (hmem x) (hne x hx)
    have h2 := hH.im_star_dotProduct_mulVec_self x
    have h3 : star x ⬝ᵥ (Cᴴ * S * C) *ᵥ x = star (C *ᵥ x) ⬝ᵥ S *ᵥ C *ᵥ x := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    rw [← h3] at h1
    exact Complex.pos_iff.mpr ⟨h1, Eq.symm h2⟩
  obtain ⟨D, hD, hGD⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨E, hE⟩ := hD.exists_right_inv
  refine ⟨C * E, ?_, fun v => ?_⟩
  · calc (C * E)ᴴ * S * (C * E) = Eᴴ * (Cᴴ * S * C) * E := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (D * E)ᴴ * (D * E) := by
          rw [hGD, star_eq_conjTranspose]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hE]; simp
  · rw [← mulVec_mulVec]
    exact hmem _

theorem UpperTheory.signature_block_diagonal :
    ∀ {N j j' : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (K K' : Submodule ℂ (Fin N → ℂ)),
        S.IsHermitian → j ≤ Module.finrank ℂ K → j' ≤ Module.finrank ℂ K' →
        (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) →
        (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) →
        (∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0) →
        ∃ A : Matrix (Fin N) (Fin j ⊕ Fin j') ℂ,
          A.conjTranspose * S * A = Matrix.fromBlocks 1 0 0 (-1) ∧
          (∀ v : Fin j → ℂ, A.mulVec (Sum.elim v (0 : Fin j' → ℂ)) ∈ K) ∧
          ∀ v : Fin j' → ℂ, A.mulVec (Sum.elim (0 : Fin j → ℂ) v) ∈ K' := by
  intro N j j' S K K' hS hj hj' hK hK' hO
  obtain ⟨B, hB, hBK⟩ := UpperTheory.frame_pos S K hS hj hK
  obtain ⟨B', hB', hBK'⟩ := UpperTheory.frame_pos (-S) K' hS.neg hj' (fun y hy h0 => by
    have := hK' y hy h0
    simpa [neg_mulVec] using this)
  have h22 : B'ᴴ * S * B' = -1 := by
    rw [← hB']
    simp
  have h21 : B'ᴴ * S * B = 0 := by
    ext a c
    have h := hO _ (hBK (Pi.single c 1)) _ (hBK' (Pi.single a 1))
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec] at h
    simpa [← Pi.single_star] using h
  have h12 : Bᴴ * S * B' = 0 := by
    have h := congrArg conjTranspose h21
    simpa [conjTranspose_mul, hS.eq, Matrix.mul_assoc] using h
  refine ⟨fromCols B B', ?_, fun v => ?_, fun v => ?_⟩
  · rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols,
      hB, h12, h21, h22]
  · simpa using hBK v
  · simpa using hBK' v
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qj14.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qj14.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qj14.Hpk k r + UpperTheory.Reformulated.B.Qj14.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qj14.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qj14.UH (UpperTheory.Reformulated.B.Qj14.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qj14.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qj14.Mat k r → UpperTheory.Reformulated.B.Qj14.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qj14.cayley_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Y : Matrix ι ι ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [hinv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Qj14.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qj14.Mat k r},
      UpperTheory.Reformulated.B.Qj14.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qj14.kap Y ∈ UpperTheory.Reformulated.B.Qj14.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qj14.cayley_form (UpperTheory.Reformulated.B.Qj14.Hpk k r) Y h hu
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qk20.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk20.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qk20.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qk20.Hpk k r + UpperTheory.Reformulated.B.Qk20.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk20.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qk20.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qk20.UH (UpperTheory.Reformulated.B.Qk20.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qk20.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qk20.Mat k r → UpperTheory.Reformulated.B.Qk20.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form {n : Type} [Fintype n] [DecidableEq n]
    (H Y : Matrix n n ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, one_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hinv, Matrix.conjTranspose_one, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.Qk20.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qk20.Mat k r},
      UpperTheory.Reformulated.B.Qk20.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qk20.kap Y ∈ UpperTheory.Reformulated.B.Qk20.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form (UpperTheory.Reformulated.B.Qk20.Hpk k r) Y h hu
end

section

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.piTensor :
    {F : Type} →
      [inst : Field F] →
        {α : Type} →
          {Γ X : α → Type} →
            [inst_1 : (a : α) → Group (Γ a)] →
              [inst_2 : (a : α) → AddCommGroup (X a)] →
                [inst_3 : (a : α) → _root_.Module F (X a)] →
                  ((a : α) → Representation F (Γ a) (X a)) →
                    Representation F ((a : α) → Γ a) (PiTensorProduct F fun (a : α) ↦ X a) :=
    fun {F : Type} [Field F] {α : Type} {Γ X : α → Type} [(a : α) → Group (Γ a)] [(a : α) → AddCommGroup (X a)]
        [(a : α) → _root_.Module F (X a)] (ρ : (a : α) → Representation F (Γ a) (X a)) ↦
      PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun (a : α) ↦ MonoidHom.comp (ρ a) (Pi.evalMonoidHom Γ a))

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one :
    {s : ℕ} →
      {G V : Fin s → Type} →
        [inst : (a : Fin s) → Group (G a)] →
          [inst_1 : (a : Fin s) → AddCommGroup (V a)] →
            [inst_2 : (a : Fin s) → _root_.Module ℂ (V a)] →
              ((a : Fin s) → Representation ℂ (G a) (V a)) → (a : Fin s) → Representation ℂ (G a) (PiTensorProduct ℂ V) :=
    fun {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)] [(a : Fin s) → AddCommGroup (V a)]
        [(a : Fin s) → _root_.Module ℂ (V a)] (σ : (a : Fin s) → Representation ℂ (G a) (V a)) (a : Fin s) ↦
      MonoidHom.comp (UpperTheory.Reformulated.B.SmoothTensorFactor.piTensor σ) (MonoidHom.mulSingle G a)

private lemma UpperTheory.Reformulated.B.SmoothTensorFactor.position_tprod {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)]
    [(a : Fin s) → AddCommGroup (V a)] [(a : Fin s) → _root_.Module ℂ (V a)]
    (σ : (a : Fin s) → Representation ℂ (G a) (V a)) (a : Fin s) (g : G a) (f : (i : Fin s) → V i) :
    UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun i => σ i ((Pi.mulSingle a g : (i : Fin s) → G i) i) (f i)) := by
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f) = _
  rw [PiTensorProduct.map_tprod]
  rfl

private lemma UpperTheory.Reformulated.B.SmoothTensorFactor.stab_mem_nhds {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)]
    [(a : Fin s) → AddCommGroup (V a)] [(a : Fin s) → _root_.Module ℂ (V a)]
    [(a : Fin s) → TopologicalSpace (G a)]
    (σ : (a : Fin s) → Representation ℂ (G a) (V a))
    (h : ∀ a, UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (σ a)) (a : Fin s) (v : PiTensorProduct ℂ V) :
    {g : G a | UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g v = v} ∈ nhds (1 : G a) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have hopen : {g : G a | σ a g (f a) = f a} ∈ nhds (1 : G a) :=
      (h a (f a)).mem_nhds (by simp)
    refine Filter.mem_of_superset hopen ?_
    intro g hg
    have hg' : σ a g (f a) = f a := hg
    have key : (fun i => σ i ((Pi.mulSingle a g : (i : Fin s) → G i) i) (f i)) = f := by
      funext i
      by_cases hi : i = a
      · subst hi
        simpa using hg'
      · simp [Pi.mulSingle_eq_of_ne hi]
    change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (r • PiTensorProduct.tprod ℂ f) = _
    rw [map_smul, UpperTheory.Reformulated.B.SmoothTensorFactor.position_tprod, key]
  | add x y hx hy =>
    refine Filter.mem_of_superset (Filter.inter_mem hx hy) ?_
    rintro g ⟨h1, h2⟩
    have h1' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g x = x := h1
    have h2' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g y = y := h2
    change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (x + y) = x + y
    rw [map_add (f := _), h1', h2']

theorem UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth :
    ∀ {s : ℕ} {G V : Fin s → Type} [inst : (a : Fin s) → Group (G a)] [inst_1 : (a : Fin s) → AddCommGroup (V a)]
      [inst_2 : (a : Fin s) → _root_.Module ℂ (V a)] [inst_3 : (a : Fin s) → TopologicalSpace (G a)]
      [∀ (a : Fin s), IsTopologicalGroup (G a)] (σ : (a : Fin s) → Representation ℂ (G a) (V a)),
      (∀ (a : Fin s), UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (σ a)) →
        ∀ (a : Fin s), UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a) := by
  intro s G V _ _ _ _ _ σ h a v
  let H : Subgroup (G a) :=
    { carrier := {g | UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g v = v}
      mul_mem' := by
        intro x y hx hy
        have hx' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x v = v := hx
        have hy' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a y v = v := hy
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy', hx']
      one_mem' := by
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := by
        intro x hx
        have hx' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x v = v := hx
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x⁻¹ v = v
        conv_lhs => rw [← hx']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact Subgroup.isOpen_of_mem_nhds H (g := 1) (UpperTheory.Reformulated.B.SmoothTensorFactor.stab_mem_nhds σ h a v)
end

section

theorem UpperTheory.Reformulated.B.DYha2.main :
    ∀ {X Y : Type} [inst : AddCommGroup X] [inst_1 : _root_.Module ℂ X] [inst_2 : AddCommGroup Y]
      [inst_3 : _root_.Module ℂ Y] {x : X} {y : Y}, x ≠ (0 : X) → y ≠ (0 : Y) → x ⊗ₜ[ℂ] y ≠ (0 : TensorProduct ℂ X Y) := by
  intro X Y _ _ _ _ x y hx hy h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℂ hy
  have key := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f g)) h
  simp only [TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at key
  exact (mul_ne_zero hf hg) key
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi25.UG :
    ℕ → Type :=
    fun (N : ℕ) ↦ ↥(Matrix.unitaryGroup (Fin N) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qi25.ent :
    {N : ℕ} → UpperTheory.Reformulated.B.Qi25.UG N → Fin N × Fin N → ℂ :=
    fun {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) (ij : Fin N × Fin N) ↦ (↑g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

noncomputable def UpperTheory.Reformulated.B.Qi25.IsPD :
    {N : ℕ} → (UpperTheory.Reformulated.B.Qi25.UG N → ℂ) → Prop :=
    fun {N : ℕ} (f : UpperTheory.Reformulated.B.Qi25.UG N → ℂ) ↦
      ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
        ∀ (g : UpperTheory.Reformulated.B.Qi25.UG N),
          f g * (↑g : Matrix (Fin N) (Fin N) ℂ).det ^ k =
            (MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g) : MvPolynomial (Fin N × Fin N) ℂ → ℂ) P

private theorem UpperTheory.Reformulated.B.Qi25.eval_det {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) :
    MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g)
        (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det =
      (↑g : Matrix (Fin N) (Fin N) ℂ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [UpperTheory.Reformulated.B.Qi25.ent]

theorem UpperTheory.Reformulated.B.Qi25.sum.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by
  intro N ι s F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, 0, fun g ↦ by simp⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨k, P, hP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨l, Q, hQ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨k + l,
      P * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ l
        + Q * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ k,
      fun g ↦ ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, UpperTheory.Reformulated.B.Qi25.eval_det, ← hP g, ← hQ g]
    simp only [Finset.sum_insert ha]
    ring
end
