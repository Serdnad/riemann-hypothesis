module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {n : ℕ} : blk4 (1 : Matrix (Fin n) (Fin n) K) 0 0 1 = 1 := by
  simp [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem neg_block_matrix {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_neg]
  rfl

theorem exists_blockMatrixTwoByTwoFin_eq {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    ∃ A B C D : Matrix (Fin n) (Fin n) K, g = blk4 A B C D := by
  refine ⟨(g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem is_siegel_parabolic_block_iff {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 a b c d) ↔ c = 0 := by
  constructor
  · intro h
    ext i j
    have h' := h i j
    simpa only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply] using h'
  · rintro rfl i j
    simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]

theorem det_block_lower_zero {n : ℕ} (a b d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b 0 d).det = a.det * d.det := by
  simp only [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

section cT
variable (σ : K →+* K)

theorem cT_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  unfold cT; simp

theorem cT_zero {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  unfold cT; simp

theorem cT_neg {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_sub {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  simp [cT]

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (cT σ x) = x := by
  ext i j
  simp [cT, hσ]

theorem det_cT {a : ℕ} (x : Matrix (Fin a) (Fin a) K) : (cT σ x).det = σ x.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem isUnit_det_cT {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : IsUnit (cT σ x).det := by
  rw [det_cT]; exact hx.map σ

theorem cT_inv {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : cT σ x⁻¹ = (cT σ x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← cT_mul, Matrix.mul_nonsing_inv _ hx, cT_one]

theorem cT_blk4 {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end cT

theorem Jm_mul_Jm (n : ℕ) : Jm K n * Jm K n = -1 := by
  rw [Jm, submatrix_fromBlocks_mul, ← block_matrix_one (K := K), neg_block_matrix]
  congr 1 <;> simp

theorem unitary_left_inv (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : (-(Jm K n * cT σ g * Jm K n)) * g = 1 := by
  unfold IsUnitary at hg
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g), hg, Jm_mul_Jm, neg_neg]

theorem isUnit_det_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (unitary_left_inv σ hg)

theorem inv_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : g⁻¹ = -(Jm K n * cT σ g * Jm K n) :=
  Matrix.inv_eq_left_inv (unitary_left_inv σ hg)

theorem unitary_mul (σ : K →+* K) {N : ℕ} {J g h : Matrix (Fin N) (Fin N) K}
    (hg : IsUnitary σ J g) (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul, show cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h by
    simp only [Matrix.mul_assoc], hg, hh]

section eId

theorem eId_mul_eId (n r : ℕ) : eId K n r * eId K n r = eId K n r := by
  rw [eId, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

theorem cT_eId (σ : K →+* K) (n r : ℕ) : cT σ (eId K n r) = eId K n r := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, eId, Matrix.diagonal_apply, apply_ite σ]
  · simp [cT, eId, Matrix.diagonal_apply, h, Ne.symm h]

theorem eId_mul_extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : eId K n r * extB b = extB b := by
  ext i j
  simp only [eId, Matrix.diagonal_mul, extB]
  split_ifs <;> simp_all

theorem extB_mul_eId {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : extB b * eId K n r = extB b := by
  ext i j
  simp only [eId, Matrix.mul_diagonal, extB]
  split_ifs <;> simp_all

theorem cT_extB (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    cT σ (extB (n := n) b) = extB (cT σ b) := by
  ext i j
  simp only [cT, extB, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp_all

theorem extB_injective {n r : ℕ} (hr : r ≤ n) {b b' : Matrix (Fin r) (Fin r) K}
    (h : extB (n := n) b = extB b') : b = b' := by
  ext i j
  have h' := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  simpa [extB] using h'

end eId

theorem repMat_eq (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    repMat σ b a = blk4 ((1 - eId K n r) * a) (eId K n r * (cT σ a)⁻¹) (-(eId K n r * a))
      ((1 - eId K n r - extB b) * (cT σ a)⁻¹) := by
  rw [repMat, wr, nB, mA, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  congr 1 <;> simp [sub_mul, mul_sub, add_mul, eId_mul_extB] <;> abel

end GlobalTheory.CompanionTheory.BruhatCell
end
end

section

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem span_range_mul_le {n : ℕ} (q M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (q * M)) ≤ Submodule.span K (Set.range M) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : (q * M) i = ∑ k, q i k • M k := by
    funext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_range_mul_of_isUnit {n : ℕ} {p : Matrix (Fin n) (Fin n) K} (hp : IsUnit p.det)
    (M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (p * M)) = Submodule.span K (Set.range M) := by
  refine le_antisymm (span_range_mul_le p M) ?_
  have h := span_range_mul_le p⁻¹ (p * M)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul] at h

theorem span_range_eId_mul {n r : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) :
    Submodule.span K (Set.range (eId K n r * a)) = Submodule.span K (Set.range c) := by
  have row : ∀ i : Fin n, (eId K n r * a) i = if (i : ℕ) < r then a i else 0 := by
    intro i
    funext j
    by_cases hi : (i : ℕ) < r <;> simp [eId, Matrix.diagonal_mul, hi]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (eId K n r * a) i ∈ _
    rw [row i]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, h.2 i hi]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [if_neg hi]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨j, j.2.trans_le hr⟩, ?_⟩
    change (eId K n r * a) ⟨j, j.2.trans_le hr⟩ = c j
    rw [row, if_pos j.2, h.2 ⟨j, j.2.trans_le hr⟩ j.2]

theorem span_range_lowerLeft : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n →
    ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det →
      Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  intro K _ n r hr c a p h hp
  have hneg : p * -(eId K n r * a) = (-p) * (eId K n r * a) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  have hdet : IsUnit (-p).det := by
    rw [Matrix.det_neg]
    exact ((IsUnit.neg isUnit_one).pow _).mul hp
  rw [hneg, span_range_mul_of_isUnit hdet, span_range_eId_mul hr h]

end GlobalTheory.CompanionTheory.BruhatCell
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatPtsUnn

def blkD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr k))

def blkA' {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl k))

theorem det_eq_of_lowerLeft_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (h : ∀ i j : Fin n, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    M.det = (blkA' M).det * (blkD M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; exact h i j
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  rfl

theorem mem_upperHalf {D : D7} {n : ℕ} (x : Fin (n + n) → AE D) :
    x ∈ upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i)) = 0 := by
  unfold upperHalf
  rw [LinearMap.mem_ker]
  exact funext_iff

end GlobalTheory.CompanionTheory.RatPtsUnn

namespace GlobalTheory.CompanionTheory.RatPtsUnn

theorem mulVec_inr {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (x : Fin (n + n) → R) (i : Fin n) :
    (M *ᵥ x) (finSumFinEquiv (Sum.inr i)) =
      (∑ j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) +
        (blkD M *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  rfl

variable {D : D7} {n : ℕ}

theorem exists_ratEmb_of_mem {γ : G D n} (hγ : γ ∈ GF D n) :
    ∃ g0 : GRat D.sp.cm.sig (Jst D n), ratEmb _ _ g0 = γ := by
  have h : γ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := by rw [range_ratEmb]; exact hγ
  exact h

theorem mat_ratEmb (g0 : GRat D.sp.cm.sig (Jst D n)) :
    mat (ratEmb _ _ g0) = (g0.1 : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E).map (incA D) := rfl

theorem clause1 : ∀ γ ∈ GF D n, ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det ∧
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g ∧ mat γ = g.map (incA D) := by
  intro γ hγ
  obtain ⟨g0, rfl⟩ := exists_ratEmb_of_mem hγ
  exact ⟨g0.1.1, (Matrix.isUnit_iff_isUnit_det _).1 g0.1.isUnit, g0.2, mat_ratEmb g0⟩

theorem clause2 : ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det →
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g → ∃ γ ∈ GF D n, mat γ = g.map (incA D) := by
  intro g hg hu
  let u : GL (Fin (n + n)) D.host.E := ((Matrix.isUnit_iff_isUnit_det g).2 hg).unit
  have hu' : u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := hu
  refine ⟨ratEmb _ _ ⟨u, hu'⟩, ?_, rfl⟩
  have h : ratEmb D.sp.cm.sig (Jst D n) ⟨u, hu'⟩ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := ⟨_, rfl⟩
  rw [range_ratEmb] at h
  exact h

theorem mem_P_iff (γ : G D n) :
    γ ∈ P D n ↔ ∀ x : Fin (n + n) → AE D, x ∈ upperHalf D n ↔ mat γ *ᵥ x ∈ upperHalf D n := by
  unfold P
  rw [Subgroup.mem_comap]
  exact Iff.rfl

theorem clause3 : ∀ γ ∈ GF D n, ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = g.map (incA D) →
      (γ ∈ P D n ↔ IsSiegelP g) := by
  intro γ _ g hg
  rw [mem_P_iff, hg]
  constructor
  · intro h i j
    have hx : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
      rw [mem_upperHalf]
      intro k
      exact Pi.single_eq_of_ne (fun e => Sum.inr_ne_inl (finSumFinEquiv.injective e)) _
    have h2 := (mem_upperHalf _).1 ((h _).1 hx) i
    rw [Matrix.mulVec_single_one] at h2
    change incA D (g _ _) = 0 at h2
    exact incA_injective (h2.trans (map_zero _).symm)
  · intro hS
    have hM : ∀ i j : Fin n, g.map (incA D) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
      intro i j; rw [Matrix.map_apply, hS i j, map_zero]
    have hdet : IsUnit (blkD (g.map (incA D))).det := by
      have h1 : IsUnit (mat γ).det := by
        unfold mat
        exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
      rw [hg] at h1
      rw [det_eq_of_lowerLeft_zero _ hM] at h1
      exact isUnit_of_mul_isUnit_right h1
    have hinj : ∀ y : Fin n → AE D, blkD (g.map (incA D)) *ᵥ y = 0 → y = 0 := by
      intro y hy
      rw [← Matrix.one_mulVec y, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    have hsum : ∀ (x : Fin (n + n) → AE D) (i : Fin n), (∑ j, g.map (incA D) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) = 0 := fun x i =>
      Finset.sum_eq_zero fun j _ => by rw [hM i j, zero_mul]
    intro x
    rw [mem_upperHalf, mem_upperHalf]
    constructor
    · intro hx i
      rw [mulVec_inr]
      have h0 : (fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := funext hx
      rw [hsum, h0, Matrix.mulVec_zero, zero_add]
      rfl
    · intro hx
      have h0 : (blkD (g.map (incA D)) *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := by
        funext i
        have := hx i
        rw [mulVec_inr, hsum, zero_add] at this
        exact this
      have h1 := hinj _ h0
      exact fun i => congrFun h1 i

theorem ratPtsUnn : RatPts := fun _ _ => ⟨clause1, clause2, clause3⟩

end GlobalTheory.CompanionTheory.RatPtsUnn
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

def CovAt {D : D7} {n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {θ : InfFam D}
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (γ : G D n) : Prop :=
  ∀ (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n), Ψ.1 = EC.Heisenberg₂ ψ V v Φ.1 →
    (ω γ Ψ).1 = EC.Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1

def FieldGen (K : Type) [Field K] (σ : K →+* K) (n : ℕ) : Prop :=
  ∀ T : Matrix (Fin (n + n)) (Fin (n + n)) K → Prop, (∀ g h, T g → T h → T (g * h)) →
    (∀ a : Matrix (Fin n) (Fin n) K, IsUnit a.det → T (mA σ a)) →
    (∀ b : Matrix (Fin n) (Fin n) K, cT σ b = b → T (nB b)) → T (Jm K n) →
    ∀ g, IsUnit g.det → IsUnitary σ (Jm K n) g → T g

variable {D : D7} {n : ℕ}

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := by
  unfold mat; rw [map_mul]; rfl

theorem mat_one' : mat (1 : G D n) = 1 := by
  unfold mat; rw [map_one]; rfl

theorem mat_inv_mul' (g : G D n) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem mat_mul_inv' (g : G D n) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, mat_one']

theorem mat_injective' : Function.Injective (mat : G D n → Mx D (n + n) (n + n)) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem x_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    xPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) A + HMul.hMul (yPart v) C := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]

theorem y_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    yPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) B + HMul.hMul (yPart v) E := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' = blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem covAt_mul {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {θ : InfFam D}
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {γ₁ γ₂ : G D n}
    (h₁ : CovAt ψ V ω γ₁) (h₂ : CovAt ψ V ω γ₂) : CovAt ψ V ω (γ₁ * γ₂) := by
  intro v Φ Ψ hΨ
  have e1 := h₁ _ (ω γ₂ Φ) (ω γ₂ Ψ) (h₂ v Φ Ψ hΨ)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, mul_inv_rev, mat_mul', Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.EisCovar
end
end
