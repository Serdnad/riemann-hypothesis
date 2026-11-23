module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

@[expose] public section

section

open Matrix Module
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem norm_orthonormalBasis_det_le (b : OrthonormalBasis ι 𝕜 E) (x : ι → E) :
    ‖b.toBasis.det x‖ ≤ ∏ k, ‖x k‖ := by
  classical
  haveI : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : LocallyFiniteOrderBot ι :=
    LocallyFiniteOrderBot.ofIic ι (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  have h : finrank 𝕜 E = Fintype.card ι := finrank_eq_card_basis b.toBasis
  set c := InnerProductSpace.gramSchmidtOrthonormalBasis h x with hc
  have h1 : b.toBasis.det x = b.toBasis.det c * c.toBasis.det x := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det c.toBasis]
    simp
  have h2 : c.toBasis.det x = ∏ i, ⟪c i, x i⟫_𝕜 := by
    convert InnerProductSpace.gramSchmidtOrthonormalBasis_det h x
  rw [h1, norm_mul, b.det_to_matrix_orthonormalBasis c, one_mul, h2, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  simpa [c.orthonormal.1 i] using norm_inner_le_norm (𝕜 := 𝕜) (c i) (x i)

theorem norm_det_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2) := by
  have h := norm_orthonormalBasis_det_le (EuclideanSpace.basisFun ι 𝕜)
    (fun j => (WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 ι))
  simp only [EuclideanSpace.norm_eq] at h
  convert h using 2
  rw [Basis.det_apply]
  congr 1

theorem norm_det_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ i, √(∑ j, ‖A i j‖ ^ 2) := by
  rw [← det_transpose]
  exact norm_det_le_prod_col Aᵀ

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_prod_col A) 2).trans_eq ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (by positivity)

theorem norm_det_sq_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [← det_transpose]
  exact norm_det_sq_le_prod_col Aᵀ

theorem det_gram_nonneg (x : ι → E) : 0 ≤ (gram 𝕜 x).det :=
  (posSemidef_gram 𝕜 x).det_nonneg

theorem re_det_gram_nonneg (x : ι → E) : 0 ≤ RCLike.re (gram 𝕜 x).det :=
  (RCLike.nonneg_iff.mp (det_gram_nonneg x)).1


omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem gram_sum_smul [Fintype κ] (e : ι → E) (m : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, m i j • e i) = mᴴ * gram 𝕜 e * m := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem re_det_gram_sum_smul (e : ι → E) (m : Matrix ι ι 𝕜) :
    RCLike.re (gram 𝕜 (fun j => ∑ i, m i j • e i)).det
      = ‖m.det‖ ^ 2 * RCLike.re (gram 𝕜 e).det := by
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul]
  norm_cast
  rw [RCLike.re_ofReal_mul]

theorem exists_orthonormal_of_linearIndependent {x : ι → E} (hx : LinearIndependent 𝕜 x) :
    ∃ (e : ι → E) (m : Matrix ι ι 𝕜), Orthonormal 𝕜 e ∧ ∀ j, x j = ∑ i, m i j • e i := by
  set S := Submodule.span 𝕜 (Set.range x)
  haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have h : finrank 𝕜 S = Fintype.card ι := finrank_span_eq_card hx
  let b : OrthonormalBasis ι 𝕜 S :=
    (stdOrthonormalBasis 𝕜 S).reindex (Fintype.equivFinOfCardEq h.symm).symm
  let y : ι → S := fun j => ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨fun i => (b i : E), of fun i j => b.repr (y j) i,
    b.orthonormal.comp_linearIsometry S.subtypeₗᵢ, fun j => ?_⟩
  have := congrArg (fun s : S => (s : E)) (b.sum_repr (y j))
  simpa using this.symm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem norm_sum_smul_sq {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := he.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.conj_mul] at h
  exact_mod_cast h

theorem re_det_gram_le_prod (x : ι → E) : RCLike.re (gram 𝕜 x).det ≤ ∏ k, ‖x k‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he]
    simp only [det_one, RCLike.one_re, mul_one, norm_sum_smul_sq he]
    exact norm_det_sq_le_prod_col m
  · rw [← det_gram_ne_zero_iff_linearIndependent, not_not] at hx
    rw [hx, map_zero]
    positivity


omit [DecidableEq ι] in
theorem det_gram_comp_equiv [DecidableEq ι] (x : ι → E) (σ : κ ≃ ι) :
    (gram 𝕜 (x ∘ σ)).det = (gram 𝕜 x).det :=
  det_submatrix_equiv_self σ (gram 𝕜 x)


omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem sum_norm_apply_sq_le {e : ι → E} (he : Orthonormal 𝕜 e) (φ : E →L[𝕜] 𝕜) :
    ∑ i, ‖φ (e i)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  set s := ∑ i, ‖φ (e i)‖ ^ 2 with hs
  set v := ∑ i, (starRingEnd 𝕜) (φ (e i)) • e i with hv
  have hs0 : 0 ≤ s := by positivity
  have h1 : ‖v‖ ^ 2 = s := by simp [hv, norm_sum_smul_sq he, hs]
  have h2 : φ v = (s : 𝕜) := by
    simp [hv, hs, RCLike.conj_mul]
  have h3 : s ≤ ‖φ‖ * ‖v‖ := by
    have := φ.le_opNorm v
    rwa [h2, RCLike.norm_ofReal, abs_of_nonneg hs0] at this
  nlinarith [sq_nonneg (‖φ‖ - ‖v‖)]

theorem norm_det_apply_sq_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ^ 2 ≤ RCLike.re (gram 𝕜 x).det * ∏ j, ‖φ j‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    have h : (of fun j k => φ j (x k)) = (of fun j i => φ j (e i)) * m := by
      ext j k
      simp [hm, Matrix.mul_apply, mul_comm]
    rw [h]
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he, det_mul, norm_mul, mul_pow,
      det_one, RCLike.one_re, mul_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_det_sq_le_prod_row _).trans ?_) (by positivity)
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j _ => sum_norm_apply_sq_le he (φ j)
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hx
    have h0 : (of fun j k => φ j (x k)).det = 0 := by
      refine exists_mulVec_eq_zero_iff.mp ⟨g, fun h => hi (congrFun h i), ?_⟩
      funext j
      have := congrArg (φ j) hg
      simpa [mulVec, dotProduct, mul_comm] using this
    rw [h0, norm_zero]
    exact (by norm_num : (0 : ℝ) ^ 2 ≤ 0).trans
      (mul_nonneg (re_det_gram_nonneg x) (by positivity))

theorem norm_det_apply_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ≤ (∏ k, ‖x k‖) * ∏ j, ‖φ j‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  exact (norm_det_apply_sq_le φ x).trans
    (mul_le_mul_of_nonneg_right (re_det_gram_le_prod x) (by positivity))

end GlobalTheory.Hadamard
end

section

open scoped ComplexOrder

namespace GlobalTheory.OneLeDetOneAdd

theorem one_le_det_one_add {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {D : Matrix n n 𝕜} (hD : D.PosSemidef) : (1 : 𝕜) ≤ (1 + D).det := by
  have hA : (1 + D).IsHermitian := Matrix.isHermitian_one.add hD.1
  have hμ : ∀ i, 1 ≤ hA.eigenvalues i := by
    intro i
    have hv1 : RCLike.re (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm]
      simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hA.eigenvectorBasis.orthonormal.1 i, algebraMap.coe_one, one_pow, RCLike.one_re]
    have h := hA.eigenvalues_eq i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, map_add (f := _), hv1] at h
    have h0 := hD.re_dotProduct_nonneg ⇑(hA.eigenvectorBasis i)
    linarith
  have hprod : (1 : ℝ) ≤ ∏ i, hA.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hA.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hμ i)
  rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  calc (1 : 𝕜) = ((1 : ℝ) : 𝕜) := by simp
    _ ≤ _ := RCLike.ofReal_le_ofReal.mpr hprod

end GlobalTheory.OneLeDetOneAdd
end

section

open Matrix

namespace GlobalTheory

section Ring

variable {R : Type*} [CommRing R]

abbrev subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) : Fin i → n :=
  S.1.orderEmbOfFin S.2

theorem range_subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) :=
  Finset.range_orderEmbOfFin _ _

theorem subsetEnum_injective {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Function.Injective (subsetEnum S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem alternatingMap_apply_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (f : (n → R) [⋀^Fin i]→ₗ[R] M)
    (A : Fin i → n → R) :
    f A = ∑ S : Set.powersetCard n i,
      ((Matrix.of A).submatrix id (subsetEnum S)).det • f (fun a => Pi.single (subsetEnum S a) 1) := by
  classical
  let b := Pi.basisFun R n
  have h := (b.exteriorPower i).sum_repr (exteriorPower.ιMulti R i A)

  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f A, ← h, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_smul, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  congr 2
  ext a
  simp [b, subsetEnum, Set.powersetCard.ofFinEmbEquiv_symm_apply, Pi.basisFun_apply]

theorem det_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by
  classical
  have h := alternatingMap_apply_eq_sum_minors
    ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A
  have h0 : (A * B).det =
      ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A := rfl
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [AlternatingMap.compLinearMap_apply]
  change Matrix.det _ = _
  congr 1
  ext a c
  simp [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]

theorem det_mul_det_eq_of_range_eq {m k n : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix m n R) (B : Matrix n m R) (φ : k ≃ m) (e : m → n) (g : k → n)
    (hg : Function.Injective g) (h : Set.range e = Set.range g) :
    (A.submatrix id e).det * (B.submatrix e id).det =
      (A.submatrix φ g).det * (B.submatrix g φ).det := by
  have h1 : ∀ a : k, ∃ c : m, e c = g a := fun a => by
    have : g a ∈ Set.range e := h ▸ Set.mem_range_self a
    exact this
  choose s hs using h1
  have hinj : Function.Injective (φ.symm ∘ s) := by
    intro a a' haa
    have : s a = s a' := φ.symm.injective haa
    exact hg (by rw [← hs a, ← hs a', this])
  let σ : Equiv.Perm k := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ a, e (φ (σ a)) = g a := fun a => by simp [σ, hs]
  have hA : A.submatrix φ g = ((A.submatrix id e).submatrix φ φ).submatrix id σ := by
    ext a c; simp [hσ]
  have hB : B.submatrix g φ = ((B.submatrix e id).submatrix φ φ).submatrix σ id := by
    ext a c; simp [hσ]
  rw [hA, hB, det_permute, det_permute', det_submatrix_equiv_self, det_submatrix_equiv_self]
  have : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  linear_combination (-(A.submatrix id e).det * (B.submatrix e id).det) * this

theorem det_mul_eq_sum_minors_of_enum {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (e : Set.powersetCard n (Fintype.card m) → m → n)
    (he : ∀ S, Set.range (e S) = (S.1 : Set n)) (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ S : Set.powersetCard n (Fintype.card m),
      (A.submatrix id (e S)).det * (B.submatrix (e S) id).det := by
  classical
  letI : LinearOrder n := linearOrderOfSTO WellOrderingRel
  let φ : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  rw [← det_submatrix_equiv_self φ (A * B), submatrix_mul A B φ id φ Function.bijective_id,
    det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [det_mul_det_eq_of_range_eq A B φ (e S) (subsetEnum S) (subsetEnum_injective S)
    ((he S).trans (range_subsetEnum S).symm)]
  rfl

theorem det_submatrix_mul_eq_sum_minors {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [submatrix_mul A B r id c Function.bijective_id, det_mul_eq_sum_minors]
  rfl

theorem det_mul_diagonal_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (d : n → R) (B : Matrix n (Fin i) R) :
    (A * diagonal d * B).det = ∑ S : Set.powersetCard n i,
      (∏ s ∈ S.1, d s) *
        ((A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det) := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (A * diagonal d).submatrix id (subsetEnum S) =
      A.submatrix id (subsetEnum S) * diagonal (d ∘ subsetEnum S) := by
    ext a c; simp
  have h2 : ∏ a, d (subsetEnum S a) = ∏ s ∈ S.1, d s := by
    refine Finset.prod_bij (fun a _ => subsetEnum S a) (fun a _ => Finset.orderEmbOfFin_mem _ _ _)
      (fun a _ b _ h => subsetEnum_injective S h) (fun s hs => ?_) (fun _ _ => rfl)
    have : s ∈ Set.range (subsetEnum S) := by rw [range_subsetEnum]; exact hs
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_univ _, ha⟩
  rw [h1, det_mul, det_diagonal, ← h2]
  simp only [Function.comp_apply]
  ring

end Ring

section Normed

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}

theorem det_mul_conjTranspose_eq_sum_norm_sq (A : Matrix (Fin i) n 𝕜) :
    (A * Aᴴ).det =
      ((∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_minors]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]

theorem sum_norm_sq_minors_eq_one (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq A
  rw [hA, det_one] at h
  exact_mod_cast h.symm

theorem two_rpow_neg_half_le_choose_rpow {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < N.choose i := by exact_mod_cast Nat.choose_pos hi
  have hle : (N.choose i : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.choose_le_two_pow N i).trans (Nat.pow_le_pow_right two_pos hr)
  calc (2 : ℝ) ^ (-(r : ℝ) / 2) = ((2 : ℝ) ^ (r : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)

theorem exists_choose_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by
  have h := sum_norm_sq_minors_eq_one A hA
  have hne : (Finset.univ : Finset (Set.powersetCard n i)).Nonempty := by
    rcases (Finset.univ : Finset (Set.powersetCard n i)).eq_empty_or_nonempty with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hi : i ≤ Fintype.card n := by
    obtain ⟨S, -⟩ := hne
    exact S.2 ▸ Finset.card_le_univ S.1
  have hcard : Fintype.card (Set.powersetCard n i) = (Fintype.card n).choose i := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hpos : (0 : ℝ) < (Fintype.card n).choose i := by exact_mod_cast Nat.choose_pos hi
  refine ⟨hi, ?_⟩
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (((Fintype.card n).choose i : ℝ))⁻¹)
    (g := fun S => ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2) (by
      rw [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])
  refine ⟨S, (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_⟩
  refine le_of_eq_of_le ?_ hS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
  norm_num

theorem exists_two_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by
  obtain ⟨hi, S, hS⟩ := exists_choose_rpow_le_norm_minor A hA
  exact ⟨S, (two_rpow_neg_half_le_choose_rpow hi hr).trans hS⟩

end Normed

end GlobalTheory
end
