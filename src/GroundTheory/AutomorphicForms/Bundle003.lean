module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Tactic.Continuity
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

section

open Matrix

namespace GroundTheory.Automorphic

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable (n) (R : Type*) [CommRing R]

def transvectionGL (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := TransvectionStruct.mul_inv t
  inv_val := TransvectionStruct.inv_mul t

@[simp]
theorem coe_transvectionGL (t : TransvectionStruct n R) :
    (transvectionGL n R t : Matrix n n R) = t.toMatrix := rfl

def elementarySubgroup : Subgroup (GL n R) :=
  Subgroup.closure (Set.range (transvectionGL n R))

variable {n R}

theorem transvectionGL_mem_elementarySubgroup (t : TransvectionStruct n R) :
    transvectionGL n R t ∈ elementarySubgroup n R :=
  Subgroup.subset_closure ⟨t, rfl⟩

theorem elementarySubgroup_le_ker_det :
    elementarySubgroup n R ≤ (Matrix.GeneralLinearGroup.det : GL n R →* Rˣ).ker := by
  rw [elementarySubgroup, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, TransvectionStruct.det]

theorem coe_list_prod_transvectionGL (L : List (TransvectionStruct n R)) :
    (((L.map (transvectionGL n R)).prod : GL n R) : Matrix n n R) =
      (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => simp [ih]

theorem list_prod_transvectionGL_mem (L : List (TransvectionStruct n R)) :
    (L.map (transvectionGL n R)).prod ∈ elementarySubgroup n R :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact transvectionGL_mem_elementarySubgroup t

theorem mul_transvection_apply (i j : n) (c : R) (M : Matrix n n R) (a b : n) :
    (M * transvection i j c) a b = if b = j then M a j + c * M a i else M a b := by
  split_ifs with h
  · subst h
    exact mul_transvection_apply_same i b a c M
  · exact mul_transvection_apply_of_ne i j a b h c M

theorem transvection_mul_eq_diagonal_update (i j : n) (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-(↑u⁻¹ : R)) * transvection i j (u : R) *
      transvection i j (-1) * transvection j i 1 * transvection i j (-1) =
      diagonal (Function.update (Function.update (1 : n → R) i u) j (↑u⁻¹ : R)) := by
  ext a b
  simp only [mul_transvection_apply]
  simp only [diagonal_apply, Function.update_apply, Pi.one_apply, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hbj : b = j <;> by_cases hbi : b = i <;> by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [hbj, hbi, hai, haj, hij, Ne.symm hij, @eq_comm _ i, @eq_comm _ j]
  all_goals (try ring_nf)
  all_goals (try simp)

def diagonalGL : (n → Rˣ) →* GL n R where
  toFun d :=
    { val := diagonal fun k => (d k : R)
      inv := diagonal fun k => (↑(d k)⁻¹ : R)
      val_inv := by simp [diagonal_mul_diagonal]
      inv_val := by simp [diagonal_mul_diagonal] }
  map_one' := by ext1; simp
  map_mul' d e := by ext1; simp [diagonal_mul_diagonal]

@[simp]
theorem coe_diagonalGL (d : n → Rˣ) :
    (diagonalGL d : Matrix n n R) = diagonal fun k => (d k : R) := rfl

theorem diagonal_update_mem_elementarySubgroup (i j : n) (hij : i ≠ j) (u : Rˣ) :
    diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) ∈ elementarySubgroup n R := by
  have h : diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) =
      transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨j, i, hij.symm, -(↑u⁻¹ : R)⟩ *
        transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ *
          transvectionGL n R ⟨j, i, hij.symm, 1⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ := by
    ext1
    simp only [Units.val_mul, coe_transvectionGL, TransvectionStruct.toMatrix_mk, coe_diagonalGL]
    rw [transvection_mul_eq_diagonal_update i j hij u]
    congr 1
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  rw [h]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact transvectionGL_mem_elementarySubgroup _

theorem diagonalGL_mem_elementarySubgroup {d : n → Rˣ} (hd : ∏ k, d k = 1) :
    diagonalGL d ∈ elementarySubgroup n R := by
  classical
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have : d = 1 := funext fun k => isEmptyElim k
    rw [this, map_one]
    exact one_mem _
  have hmem : ∀ i ∈ Finset.univ.erase i₀,
      Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹ ∈
        (elementarySubgroup n R).comap (diagonalGL (n := n) (R := R)) := fun i hi =>
    diagonal_update_mem_elementarySubgroup i i₀ (Finset.ne_of_mem_erase hi) (d i)
  have hprod := Subgroup.prod_mem _ hmem
  have heq : ∏ i ∈ Finset.univ.erase i₀, (Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹) = d := by
    funext k
    rw [Finset.prod_apply]
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hk : k = i₀
    · subst hk
      have h1 : ∀ i ∈ Finset.univ.erase k,
          ((if k = i then d i else 1) * if k = k then (d i)⁻¹ else 1) = (d i)⁻¹ := by
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi).symm, if_pos rfl, one_mul]
      rw [Finset.prod_congr rfl h1, Finset.prod_inv_distrib]
      have h2 := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k)
      rw [hd] at h2
      rw [eq_comm, ← mul_eq_one_iff_eq_inv]
      exact h2
    · have h1 : ∀ i ∈ Finset.univ.erase i₀,
          ((if k = i then d i else 1) * if k = i₀ then (d i)⁻¹ else 1) =
            if k = i then d i else 1 := by
        intro i _
        rw [if_neg hk, mul_one]
      rw [Finset.prod_congr rfl h1, Finset.prod_ite_eq]
      rw [if_pos (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)]
  rw [heq] at hprod
  exact hprod

end CommRing

section Field

variable {F : Type*} [Field F]

theorem mem_elementarySubgroup_of_det_eq_one {g : GL n F}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : g ∈ elementarySubgroup n F := by
  classical
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix n n F)
  have hdet : ∏ k, D k = 1 := by
    have h1 : (g : Matrix n n F).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]
    rw [hM, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, det_diagonal, one_mul, mul_one] at h1
    exact h1
  have hD : ∀ k, D k ≠ 0 := fun k h0 => by
    have := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hdet] at this
    exact one_ne_zero this
  let d : n → Fˣ := fun k => Units.mk0 (D k) (hD k)
  have hd : ∏ k, d k = 1 := by
    ext
    simp [d, Units.coe_prod, hdet]
  have hg' : g = (L.map (transvectionGL n F)).prod * diagonalGL d *
      (L'.map (transvectionGL n F)).prod := by
    ext1
    simp only [Units.val_mul, coe_list_prod_transvectionGL, coe_diagonalGL]
    rw [hM]
    rfl
  rw [hg']
  exact mul_mem (mul_mem (list_prod_transvectionGL_mem L) (diagonalGL_mem_elementarySubgroup hd))
    (list_prod_transvectionGL_mem L')

end Field

end GroundTheory.Automorphic
end

section

open Matrix

namespace GroundTheory.Automorphic

namespace Reduction

section Block

variable {R : Type*} [CommRing R] {m : ℕ}

def blockOne (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i

@[simp] theorem blockOne_last_last (M : Matrix (Fin m) (Fin m) R) :
    blockOne M (Fin.last m) (Fin.last m) = 1 := by
  simp [blockOne]

@[simp] theorem blockOne_last_castSucc (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    blockOne M (Fin.last m) (Fin.castSucc j) = 0 := by
  simp [blockOne]

@[simp] theorem blockOne_castSucc_last (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.last m) = 0 := by
  simp [blockOne]

@[simp] theorem blockOne_castSucc_castSucc (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.castSucc j) = M i j := by
  simp [blockOne]

theorem blockOne_mul (M N : Matrix (Fin m) (Fin m) R) :
    blockOne (M * N) = blockOne M * blockOne N := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem blockOne_one : blockOne (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem blockOne_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin m) (Fin m) R) :
    (blockOne M).map f = blockOne (M.map f) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp

def blockOneMonoidHom : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun := blockOne
  map_one' := blockOne_one
  map_mul' := blockOne_mul

def blockOneHom : GL (Fin m) R →* GL (Fin (m + 1)) R :=
  Units.map blockOneMonoidHom

@[simp] theorem coe_blockOneHom (γ : GL (Fin m) R) :
    ((blockOneHom γ : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      blockOne (γ : Matrix (Fin m) (Fin m) R) := rfl

theorem single_last_vecMul_blockOne (M : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* blockOne M = Pi.single (Fin.last m) 1 := by
  ext j
  induction j using Fin.lastCases <;>
    simp [vecMul, dotProduct, Pi.single_apply, Fin.castSucc_ne_last]

theorem vecMul_blockOne_castSucc (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    (y ᵥ* blockOne M) (Fin.castSucc j) = (Fin.init y ᵥ* M) j := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem vecMul_blockOne_last (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) :
    (y ᵥ* blockOne M) (Fin.last m) = y (Fin.last m) := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc]

end Block

section Row

variable {F : Type*} [Field F] {m : ℕ}

def rowMatrix (x : Fin (m + 1) → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => if i = Fin.last m then x j else if i = j then 1 else 0

theorem det_rowMatrix (x : Fin (m + 1) → F) : (rowMatrix x).det = x (Fin.last m) := by
  rw [det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [rowMatrix, Fin.castSucc_ne_last]
  · intro i j hij
    simp only [rowMatrix, of_apply]
    have hij' : i < j := hij
    have hi : i ≠ Fin.last m := fun h => by
      rw [h] at hij'
      exact absurd hij' (not_lt.2 (Fin.le_last j))
    rw [if_neg hi, if_neg hij'.ne]

theorem single_last_vecMul_rowMatrix (x : Fin (m + 1) → F) :
    Pi.single (Fin.last m) 1 ᵥ* rowMatrix x = x := by
  ext j
  rw [vecMul, dotProduct, Finset.sum_eq_single (Fin.last m)]
  · simp [rowMatrix]
  · intro b _ hb
    simp [hb]
  · simp

theorem exists_lastRow_eq {x : Fin (m + 1) → F} (hx : x ≠ 0) :
    ∃ γ : GL (Fin (m + 1)) F,
      Pi.single (Fin.last m) 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = x := by
  classical

  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun j => not_not.1 fun hj => h ⟨j, hj⟩)
  by_cases hl : x (Fin.last m) ≠ 0
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x) (by rw [det_rowMatrix]; exact hl), ?_⟩
    exact single_last_vecMul_rowMatrix x
  · rw [not_not] at hl
    have hjl : j ≠ Fin.last m := fun h => hj (h ▸ hl)
    set τ := transvection j (Fin.last m) (1 : F) with hτ
    have hτdet : τ.det = 1 := det_transvection_of_ne j (Fin.last m) hjl 1
    set x' := x ᵥ* τ with hx'
    have hx'l : x' (Fin.last m) = x j := by
      simp [hx', hτ, transvection, vecMul_add, hl, Matrix.vecMul, dotProduct,
        Matrix.single_apply]
    have hx'l0 : x' (Fin.last m) ≠ 0 := by rw [hx'l]; exact hj
    set τu : GL (Fin (m + 1)) F :=
      GeneralLinearGroup.mkOfDetNeZero τ (by rw [hτdet]; exact one_ne_zero) with hτu
    refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x') (by rw [det_rowMatrix]; exact hx'l0) *
      τu⁻¹, ?_⟩
    rw [Units.val_mul, ← vecMul_vecMul]
    change (Pi.single (Fin.last m) 1 ᵥ* rowMatrix x') ᵥ* _ = x
    have hτu' : (τu : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = τ := rfl
    rw [single_last_vecMul_rowMatrix, hx', ← hτu', vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, vecMul_one]

end Row

end Reduction

end GroundTheory.Automorphic
end

section

namespace GroundTheory.Automorphic.L2Kernel

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

section SlopeTestRemainingChoices

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    (g : α → E) : eLpNorm' g 2 μ ^ 2 = ∫⁻ a, ‖g a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_two]

theorem lt_top_of_sq_lt_top {a : ℝ≥0∞} (h : a ^ 2 < ∞) : a < ∞ := by
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_pow two_ne_zero] at h
  exact lt_irrefl _ h

end SlopeTestRemainingChoices

variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]

section Kernel

variable (k : Lp 𝕜 2 (μ.prod ν))

end Kernel

end

end GroundTheory.Automorphic.L2Kernel
end

section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)

section Coordinates

variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]

noncomputable def matrixCoords : Matrix ι ι (R ⊗[F] E) ≃ (ι × ι × κ → R) where
  toFun g p := (Algebra.TensorProduct.basis R b).repr (g p.1 p.2.1) p.2.2
  invFun x i j := (Algebra.TensorProduct.basis R b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k => x (i, j, k))
  left_inv g := by
    ext i j
    simp
  right_inv x := by
    funext ⟨i, j, k⟩
    simp

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem matrixCoords_apply (g : Matrix ι ι (R ⊗[F] E)) (i j : ι) (k : κ) :
    matrixCoords b R g (i, j, k) = (Algebra.TensorProduct.basis R b).repr (g i j) k := rfl


variable {R}


omit [Algebra.IsQuadraticExtension F E] [Fintype κ] in
theorem repr_tensorMap (f : R →ₐ[F] S) (z : R ⊗[F] E) (k : κ) :
    (Algebra.TensorProduct.basis S b).repr
        (TensorProduct.map f.toLinearMap (LinearMap.id : E →ₗ[F] E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]


omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem matrixCoords_map (f : R →ₐ[F] S) (g : Matrix ι ι (R ⊗[F] E)) :
    matrixCoords b S (g.map (TensorProduct.map f.toLinearMap
      (LinearMap.id : E →ₗ[F] E))) =
      f ∘ matrixCoords b R g := by
  funext ⟨i, j, k⟩
  rw [Function.comp_apply, matrixCoords_apply, matrixCoords_apply, Matrix.map_apply, repr_tensorMap]

end Coordinates

end GroundTheory.Automorphic
end
