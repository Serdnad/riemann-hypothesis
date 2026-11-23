module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.IsPhysSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem cpV_eq_sum (v : Fin n × Fin n → ℂ) : cpV v = ∑ x, v x • cpFock (n := n) x.1 x.2 := by
  refine LinearMap.ext fun y => ?_
  have hv : v = ∑ x, v x • Pi.single x (1 : ℂ) := by
    funext z
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [cpV, cpFock, LinearMap.sum_apply, Finset.sum_mul]

theorem cmV_eq_sum (v : Fin n × Fin n → ℂ) : cmV v = ∑ x, star (v x) • cmFock (n := n) x.1 x.2 := by

  rw [cmV, dualV, map_sum]
  simp only [map_smul]
  rfl

theorem toMatrix_cmV (v : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmV v) =
      (LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV v))ᴴ := by

  rw [cmV_eq_sum, cpV_eq_sum, map_sum, map_sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, map_smul, Matrix.conjTranspose_smul, lf_toMatrix_cm, lf_toMatrix_cp, fockMatrix_conjTranspose_eq_transpose]

theorem adPhys_kkH {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    adPhys ε k (adPhys ε kᴴ w) = w := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [← LinearMap.comp_apply, ← adPhys_mul hk (kset_conjTranspose hk), hkk]
  simp [adPhys, adMat_one]

theorem ffMat_H_cp {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV (adPhys ε kᴴ w)) * (ffMat ε k)ᴴ =
      (ffMat ε k)ᴴ * LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV w) := by
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n)) (ff_cmV hk (adPhys ε kᴴ w))
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, adPhys_kkH hk, toMatrix_cmV, toMatrix_cmV] at h
  have h2 := congrArg Matrix.conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  exact h2

theorem nH_cpV {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) (z : Fock n) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (cpV w z) =
      cpV (adPhys ε kᴴ w) (Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ z) := by
  have h := congrArg (Matrix.toLin (fockBasis n) (fockBasis n)) (ffMat_H_cp hk w)
  rw [Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_toMatrix, Matrix.toLin_toMatrix] at h
  have h3 := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply] at h3
  exact h3.symm

theorem algebraMapInv_ff (k : Matrix (Fin n) (Fin n) ℂ) (x : Fock n) :
    ExteriorAlgebra.algebraMapInv (ff ε k x) = ExteriorAlgebra.algebraMapInv x := by
  have : (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).comp (ff ε k) =
      ExteriorAlgebra.algebraMapInv := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun m => ?_
    simp [ff, ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun this x

theorem ιMulti_card_zero (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : p = 0) :
    ExteriorAlgebra.ιMulti ℂ p v = 1 := by
  subst hp
  exact ExteriorAlgebra.ιMulti_zero_apply v

theorem algebraMapInv_ιMulti_pos (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : 0 < p) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ιMulti ℂ p v) = 0 := by
  cases p with
  | zero => omega
  | succ p =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [ExteriorAlgebra.algebraMapInv]

theorem repr_empty (x : Fock n) : (fockBasis n).repr x ∅ = ExteriorAlgebra.algebraMapInv x := by
  have : Finsupp.lapply ∅ ∘ₗ (fockBasis n).repr.toLinearMap =
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).toLinearMap := by
    refine (fockBasis n).ext fun T => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      AlgHom.toLinearMap_apply]
    rw [fockBasis_eq]
    rcases Nat.eq_zero_or_pos T.card with h | h
    · have hT : T = ∅ := Finset.card_eq_zero.mp h
      rw [ιMulti_card_zero _ _ h, map_one, hT, Finsupp.single_eq_same]
    · have hT : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)
      rw [algebraMapInv_ιMulti_pos _ _ h]
      simp [hT]
  exact LinearMap.congr_fun this x

theorem ffMat_empty_row (k : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin (n * n))) :
    ffMat ε k ∅ T = if T = ∅ then 1 else 0 := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, repr_empty, algebraMapInv_ff, ← repr_empty,
    Module.Basis.repr_self, Finsupp.single_apply]

theorem nH_one (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ 1 = 1 := by
  have h1 : (1 : Fock n) = fockBasis n ∅ := by
    rw [fockBasis_eq, ιMulti_card_zero _ _ Finset.card_empty]
  rw [h1, Matrix.toLin_self, Finset.sum_eq_single ∅]
  · simp [conjTranspose_apply, ffMat_empty_row]
  · intro T _ hT
    simp [conjTranspose_apply, ffMat_empty_row, hT]
  · simp

theorem nH_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : Fock n) :
    ∀ y : Fock n, Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (x * y) =
      ff ε kᴴ x * Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    intro y
    simp [Algebra.algebraMap_eq_smul_one]
  | add x x' hx hx' =>
    intro y
    rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]
  | ι_mul x m hx =>
    intro y
    have h := nH_cpV hk m (x * y)
    simp only [cpV, LinearMap.mulLeft_apply] at h
    rw [mul_assoc, h, hx, map_mul, ff, ExteriorAlgebra.map_apply_ι, mul_assoc]

theorem nH_eq {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ = (ff ε kᴴ).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have h := nH_mul hk x 1
  rw [mul_one, nH_one, mul_one] at h
  exact h

theorem ffMat_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    ffMat ε k ∈ Matrix.unitaryGroup (Finset (Fin (n * n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h1 : (ffMat ε k)ᴴ = LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε kᴴ).toLinearMap := by
    rw [← nH_eq hk, LinearMap.toMatrix_toLin]
  have hkk : kᴴ * k = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this
    exact this
  have h2 : (ff ε kᴴ).toLinearMap * (ff ε k).toLinearMap = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply,
      ← ff_mul (kset_conjTranspose hk) hk, hkk, ff_one]
    rfl
  rw [h1, ffMat, ← LinearMap.toMatrix_mul, h2, LinearMap.toMatrix_one]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem det_one_sub_eq_sum_minors {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (1 - A).det =
      ∑ s : Finset ι, (-1 : ℂ) ^ s.card * (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have e : Matrix.det (1 - A) =
      Matrix.detRowAlternating ((fun i => (-A) i) + (fun i => (1 : Matrix ι ι ℂ) i)) := by
    refine congrArg Matrix.detRowAlternating ?_
    funext i j
    simp [sub_eq_neg_add]
  rw [e, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine (Matrix.det_piecewise_one_eq_submatrix_det (-A) s).trans ?_
  have hn : (-A).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      -(A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) := by
    ext i j
    simp
  rw [hn, Matrix.det_neg, Fintype.card_coe]

theorem fock_repr_ιMulti (S : Finset (Fin (n * n))) (v : Fin S.card → (Fin n × Fin n → ℂ)) :
    (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (Matrix.of fun i j => v i (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  have h1 : (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).exteriorPower S.card).repr
        (exteriorPower.ιMulti ℂ S.card v) (Set.powersetCard.ofCard (rfl : S.card = S.card)) := by
    rw [fockBasis, Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply,
      Set.powersetCard.prodEquiv_symm_apply]
    exact DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ (exteriorPower.ιMulti ℂ S.card v).2
  rw [h1, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

theorem ffMat_diag_det (k : Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin (n * n))) :
    ffMat ε k S S = (Matrix.of fun i j : Fin S.card =>
      adMat ε k (finProdFinEquiv.symm (S.orderEmbOfFin rfl i))
        (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti, fock_repr_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]

def physEmb (ε : Fin n → Bool) : {x : Fin n × Fin n // IsPhys ε x} ↪ Fin (n * n) :=
  ⟨fun x => finProdFinEquiv x.1, fun _ _ h => Subtype.ext (finProdFinEquiv.injective h)⟩

theorem ffMat_map_physEmb (k : Matrix (Fin n) (Fin n) ℂ) (s : Finset {x : Fin n × Fin n // IsPhys ε x}) :
    ffMat ε k (s.map (physEmb ε)) (s.map (physEmb ε)) =
      ((Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix
        (Subtype.val : s → _) Subtype.val).det := by
  classical
  set S := s.map (physEmb ε) with hS
  rw [ffMat_diag_det]
  have hmem : ∀ i, ∃ x ∈ s, physEmb ε x = S.orderEmbOfFin rfl i :=
    fun i => Finset.mem_map.1 (S.orderEmbOfFin_mem rfl i)
  let e : Fin S.card → s := fun i => ⟨(hmem i).choose, (hmem i).choose_spec.1⟩
  have he : ∀ i, (((e i : {x : Fin n × Fin n // IsPhys ε x}) : Fin n × Fin n)) =
      finProdFinEquiv.symm (S.orderEmbOfFin rfl i) := by
    intro i
    rw [← (hmem i).choose_spec.2]
    exact (finProdFinEquiv.symm_apply_apply _).symm
  have hp : ∀ i, IsPhys ε (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) :=
    fun i => he i ▸ (e i : {x : Fin n × Fin n // IsPhys ε x}).2
  have hinj : Function.Injective e := by
    intro i j hij
    have h1 := he i
    rw [hij, he j] at h1
    exact (S.orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h1.symm)
  have hcard : Fintype.card (Fin S.card) = Fintype.card s := by simp [S]
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).2 ⟨hinj, hcard⟩))]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.ofBijective_apply]
  rw [he i, he j]
  simp only [adMat, if_pos (hp i), if_pos (hp j)]

theorem strPhys_eq_physDet (k : Matrix (Fin n) (Fin n) ℂ) : strPhys ε k = physDet ε k := by
  classical
  have h1 : physDet ε k = (1 - Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
      k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).det := by
    rw [physDet]
    congr 1
  rw [h1, det_one_sub_eq_sum_minors, strPhys]
  symm
  refine Finset.sum_bij (fun s _ => s.map (physEmb ε)) ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsPhysSet]
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hm
    show IsPhys ε (finProdFinEquiv.symm (finProdFinEquiv x.1))
    rw [Equiv.symm_apply_apply]
    exact x.2
  · intro s _ t _ h
    exact Finset.map_injective _ h
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    refine ⟨Finset.univ.filter (fun x => physEmb ε x ∈ S), Finset.mem_univ _, ?_⟩
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hm
      refine ⟨⟨finProdFinEquiv.symm m, hS m hm⟩, ?_, finProdFinEquiv.apply_symm_apply m⟩
      show finProdFinEquiv (finProdFinEquiv.symm m) ∈ S
      rw [Equiv.apply_symm_apply]
      exact hm
  · intro s _
    rw [ffMat_map_physEmb, Finset.card_map]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
