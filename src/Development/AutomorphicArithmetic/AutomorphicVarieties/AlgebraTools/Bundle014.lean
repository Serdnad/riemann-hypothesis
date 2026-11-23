module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Idempotents
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle008
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle010
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.aeval_mulVec_eigen {k ι : Type} [CommRing k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (t : k) (v : ι → k) (hv : M *ᵥ v = t • v) (q : k[X]) :
    (aeval M q) *ᵥ v = q.eval t • v := by
  induction q using Polynomial.induction_on with
  | C c => simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  | add p q hp hq => rw [map_add (f := _), Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n c h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, h,
      eval_mul (q := X), eval_X, smul_smul, mul_comm]

private theorem UpperTheory.V.AlgebraTools.lag_ne_zero_field {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι]
    (a : ι → k) (P : Matrix ι ι k) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hP : P.charpoly = ∏ i, (X - C (a i))) (i : ι) : lag a P i ≠ 0 := by
  intro h0
  have h1 := (eq_lag_iff a P i (fun j hj => hu i j hj.symm) (lag a P i)).1 rfl
  rw [h0, smul_zero] at h1
  have hroot : P.charpoly.eval (a i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hv' : P *ᵥ v = a i • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  have h2 := UpperTheory.V.AlgebraTools.aeval_mulVec_eigen P (a i) v hv' (∏ j ∈ Finset.univ.erase i, (X - C (a j)))
  rw [← h1, Matrix.zero_mulVec, eval_prod] at h2
  rcases smul_eq_zero.1 h2.symm with h | h
  · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.1 h
    have := (hu i j (Finset.ne_of_mem_erase hj).symm).ne_zero
    apply this
    simpa using hj0
  · exact hv0 h

theorem UpperTheory.V.AlgebraTools.lag_ne_zero :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → R) (P : Matrix ι ι R), (∀ i j, i ≠ j → IsUnit (a i - a j)) → P.charpoly.map (residue R) = ∏ i, (X - C (residue R (a i))) → ∀ i, lag a P i ≠ 0 := by
  intro R _ _ ι _ _ a P hu hP i h0
  have h := lag_map (residue R) (residue R).mapMatrix a P
    (fun c => by
      ext x y
      by_cases hxy : x = y <;> simp [Matrix.algebraMap_matrix_apply, hxy]) hu i
  rw [h0, map_zero] at h
  refine UpperTheory.V.AlgebraTools.lag_ne_zero_field (fun j => residue R (a j)) ((residue R).mapMatrix P)
    (fun i j hij => by simpa only [map_sub] using (hu i j hij).map (residue R)) ?_ i h.symm
  rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, hP]
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem left_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ f * x = u • f) :
    ∃ u : R, IsUnit u ∧ f * L.prod = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨u * v, hu.mul hv, by
      rw [List.prod_cons, ← mul_assoc, e, smul_mul_assoc, e', smul_smul]⟩

private theorem right_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ x * f = u • f) :
    ∃ u : R, IsUnit u ∧ L.prod * f = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨v * u, hv.mul hu, by
      rw [List.prod_cons, mul_assoc, e', mul_smul_comm, e, smul_smul]⟩

private theorem mid_zero {R E : Type} [CommRing R] [Ring E] [Algebra R E] {n : ℕ} (f g : E)
    (F : Fin n → E) (i : Fin n)
    (hf : ∀ j, j < i → ∃ u : R, IsUnit u ∧ f * F j = u • f)
    (hg : ∀ j, i < j → ∃ u : R, IsUnit u ∧ F j * g = u • g)
    (h0 : (List.ofFn F).prod = 0) : f * F i * g = 0 := by
  have hlen : (List.ofFn F).length = n := List.length_ofFn
  have hsplit : List.ofFn F = (List.ofFn F).take i ++ F i :: (List.ofFn F).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn F)]
    congr 1
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact i.2)]
    simp
  have hT : ∀ x ∈ (List.ofFn F).take i, ∃ u : R, IsUnit u ∧ f * x = u • f := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, hlen] at hk
    rw [List.getElem_take, List.getElem_ofFn]
    exact hf ⟨k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  have hD : ∀ x ∈ (List.ofFn F).drop (i + 1), ∃ u : R, IsUnit u ∧ x * g = u • g := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_drop, hlen] at hk
    rw [List.getElem_drop, List.getElem_ofFn]
    exact hg ⟨i + 1 + k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  obtain ⟨u, hu, hA⟩ := left_unit (R := R) f _ hT
  obtain ⟨v, hv, hB⟩ := right_unit (R := R) g _ hD
  have key : f * (List.ofFn F).prod * g = (u * v) • (f * F i * g) := by
    rw [hsplit, List.prod_append, List.prod_cons]
    calc f * (((List.ofFn F).take i).prod * (F i * ((List.ofFn F).drop (i + 1)).prod)) * g
        = (f * ((List.ofFn F).take i).prod) * F i * (((List.ofFn F).drop (i + 1)).prod * g) := by
          simp only [mul_assoc]
      _ = (u • f) * F i * (v • g) := by rw [hA, hB]
      _ = (u * v) • (f * F i * g) := by
          rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h0, mul_zero, zero_mul] at key
  exact ((hu.mul hv).smul_eq_zero).1 key.symm

theorem UpperTheory.V.AlgebraTools.lag_triangular :
    ∀ {R Λ E : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Ring E] [Algebra R E] {n : ℕ} (ρ : Λ →ₐ[R] E) (χ : Fin n → Λ →ₐ[R] R) (z : Λ), (∀ y : Fin n → Λ, (List.ofFn fun i => ρ (y i) - algebraMap R E (χ i (y i))).prod = 0) → (∀ i j, i ≠ j → IsUnit (χ i z - χ j z)) → CompleteOrthogonalIdempotents (lag (fun i => χ i z) (ρ z)) ∧ (∀ (y : Λ) (a b : Fin n), b < a → lag (fun i => χ i z) (ρ z) a * ρ y * lag (fun i => χ i z) (ρ z) b = 0) ∧ ∀ (y : Λ) (i : Fin n), lag (fun i => χ i z) (ρ z) i * ρ y * lag (fun i => χ i z) (ρ z) i = χ i y • lag (fun i => χ i z) (ρ z) i := by
  intro R Λ E _ _ _ _ _ n ρ χ z hprod hu
  have hzero : aeval (ρ z) (∏ i, (X - C ((fun i => χ i z) i))) = 0 := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simpa [Function.comp_def] using hprod (fun _ => z)
  obtain ⟨hcoi, hP, -, hcomm⟩ := lag_coi (fun i => χ i z) (ρ z) hu hzero
  have hl : ∀ c j, lag (fun i => χ i z) (ρ z) c * (ρ z - algebraMap R E (χ j z)) =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [mul_sub, ← (hcomm (ρ z) c (Commute.refl _)).eq, hP, ← Algebra.commutes,
      ← Algebra.smul_def, sub_smul]
  have hr : ∀ c j, (ρ z - algebraMap R E (χ j z)) * lag (fun i => χ i z) (ρ z) c =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [sub_mul, hP, ← Algebra.smul_def, sub_smul]
  have key : ∀ (y : Λ) (c d i : Fin n), (∀ j, j < i → j ≠ c) → (∀ j, i < j → j ≠ d) →
      lag (fun i => χ i z) (ρ z) c * (ρ y - algebraMap R E (χ i y)) *
        lag (fun i => χ i z) (ρ z) d = 0 := by
    intro y c d i h1 h2
    have h := mid_zero (R := R) (lag (fun i => χ i z) (ρ z) c) (lag (fun i => χ i z) (ρ z) d)
      (fun j => ρ (Function.update (fun _ => z) i y j) -
        algebraMap R E (χ j (Function.update (fun _ => z) i y j))) i ?_ ?_ (hprod _)
    · simpa using h
    · intro j hj
      refine ⟨_, hu c j (h1 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_lt hj)]
      exact hl c j
    · intro j hj
      refine ⟨_, hu d j (h2 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_gt hj)]
      exact hr d j
  have hmid : ∀ (r : R) (c d : Fin n), lag (fun i => χ i z) (ρ z) c * algebraMap R E r *
      lag (fun i => χ i z) (ρ z) d =
        r • (lag (fun i => χ i z) (ρ z) c * lag (fun i => χ i z) (ρ z) d) := by
    intro r c d
    rw [← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc]
  refine ⟨hcoi, ?_, ?_⟩
  · intro y a b hba
    have h := key y a b a (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt (hba.trans hj))
    rw [mul_sub, sub_mul, hmid, hcoi.ortho (ne_of_gt hba), smul_zero, sub_zero] at h
    exact h
  · intro y i
    have h := key y i i i (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt hj)
    rw [mul_sub, sub_mul, hmid, (hcoi.idem i).eq, sub_eq_zero] at h
    exact h
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem dual_symm {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) : IsDual b a := by
  intro w
  have h2 := congrArg (rename ⇑w) (h w⁻¹)

  simp only [map_sum, map_mul, rename_rename] at h2
  have hc : (⇑w ∘ ⇑w⁻¹ : Fin n → Fin n) = id := by
    funext k
    simp
  simp only [hc, rename_id, AlgHom.id_apply] at h2
  simp_rw [mul_comm (b _)]
  rw [h2]
  by_cases hw : w = 1
  · subst hw
    simp
  · have hw' : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
    simp [hw, hw']

private theorem dual_exp {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) (x : MvPolynomial (Fin n) R) :
    ∑ i, a i * dd (b i * x) = x := by
  obtain ⟨hD, -, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  apply mul_left_cancel₀ hD
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (De R n), UpperTheory.V.AlgebraTools.hkDdSpec, alt, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  have key : ∀ y : Perm (Fin n), ∑ i, a i * Perm.sign y • ((rename ⇑y) (b i) * (rename ⇑y) x) =
      Perm.sign y • ((if y = 1 then De R n else 0) * (rename ⇑y) x) := by
    intro y
    rw [← h y, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, mul_assoc]
  rw [Finset.sum_congr rfl fun y _ => key y]
  simp

theorem UpperTheory.V.AlgebraTools.hkDualExp :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) R), IsDual a b →
      ∀ x, ∑ i, a i * dd (b i * x) = x ∧ ∑ i, b i * dd (a i * x) = x := by
  intro R _ _ n ι _ a b h x
  exact ⟨dual_exp h x, dual_exp (dual_symm h) x⟩
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem rename_alt {R : Type} [CommRing R] {n : ℕ} (u : Perm (Fin n)) (x : MvPolynomial (Fin n) R) :
    rename u (alt x) = Perm.sign u • alt x := by
  unfold alt

  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun w => ?_
  simp only [Equiv.coe_mulLeft]
  rw [Units.smul_def, map_zsmul, rename_rename, ← Perm.coe_mul, Perm.sign_mul, mul_smul, smul_smul,
    Int.units_mul_self, one_smul, Units.smul_def]

private theorem antisymmetrizer_add {R : Type} [CommRing R] {n : ℕ} (x y : MvPolynomial (Fin n) R) :
    alt (x + y) = alt x + alt y := by
  simp only [alt, map_add (f := _), smul_add, Finset.sum_add_distrib]

private theorem antisymmetrizer_symmetric_mul {R : Type} [CommRing R] {n : ℕ} (z x : MvPolynomial (Fin n) R)
    (hz : z.IsSymmetric) : alt (z * x) = z * alt x := by
  simp only [alt, map_mul, hz _, Finset.mul_sum, mul_smul_comm]

private theorem eq_of_De_mul_eq_De_mul {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p q : MvPolynomial (Fin n) R) (h : De R n * p = De R n * q) : p = q :=
  by
    have hd : De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
      rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp
    apply mul_left_cancel₀ ?_ h
    rw [hd, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective

theorem UpperTheory.V.AlgebraTools.hkDdProps :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), (∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y) ∧ (∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x) ∧
      (∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric) ∧
      ∃ D : MvPolynomial (Fin n) R →ₗ[symmetricSubalgebra (Fin n) R] symmetricSubalgebra (Fin n) R, ∀ x, (D x : MvPolynomial (Fin n) R) = dd x := by
  intro R _ _ n
  have hadd : ∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y := by
    intro x y
    apply eq_of_De_mul_eq_De_mul
    rw [mul_add, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_add]
  have hmul : ∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x := by
    intro z x hz
    apply eq_of_De_mul_eq_De_mul
    rw [UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_symmetric_mul z x hz, mul_left_comm, UpperTheory.V.AlgebraTools.hkDdSpec]
  have hsym : ∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric := by
    intro x w
    apply eq_of_De_mul_eq_De_mul
    have hd : De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
      rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp
    have hw : rename w (De R n) = Perm.sign w • De R n := by
      rw [hd, AlgHom.map_det]
      have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
          (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
          (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
        ext i j
        simp [Matrix.vandermonde_apply]
      rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
    have e1 := congrArg (rename ⇑w) (UpperTheory.V.AlgebraTools.hkDdSpec R n x)
    rw [map_mul, hw, rename_alt, ← UpperTheory.V.AlgebraTools.hkDdSpec R n x,
      smul_mul_assoc] at e1
    exact (smul_left_cancel_iff _).mp e1
  refine ⟨hadd, hmul, hsym, ?_⟩
  refine ⟨{ toFun := fun x => ⟨dd x, (mem_symmetricSubalgebra _).mpr (hsym x)⟩
            map_add' := fun x y => Subtype.ext (hadd x y)
            map_smul' := fun c x => Subtype.ext ?_ }, fun x => rfl⟩
  simp only [RingHom.id_apply, Subalgebra.smul_def, SetLike.val_smul]
  exact hmul _ _ ((mem_symmetricSubalgebra _).mp c.2)
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.isCO :
    ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (p₀ : Ideal R₀) (p : Ideal R)
      (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] [Algebra R₀ O] [Algebra R B]
      [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ R B] [IsScalarTower R₀ O B],
      IsCplAt R₀ p₀ O → IsCplAt R p B → p.comap (algebraMap R₀ R) = p₀ →
      (∀ x : R, ∃ a : R₀, x - algebraMap R₀ R a ∈ p) → UpperTheory.V.Alg.IsCO O B := by
  intro R₀ R _ _ _ p₀ p O B _ _ _ _ _ _ _ _ _ _ hO hB hp hsurj
  have hRB : ∀ r : R, algebraMap R B r ∈ maximalIdeal B ↔ r ∈ p := by
    intro r
    rw [← hB.comap_eq, Ideal.mem_comap]
  have h0B : ∀ c : R₀, algebraMap R₀ B c ∈ maximalIdeal B ↔ c ∈ p₀ := by
    intro c
    rw [IsScalarTower.algebraMap_apply R₀ R B, hRB, ← hp, Ideal.mem_comap]
  have hmO : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ maximalIdeal B := by
    have hm := IsCplAt.map_pow_eq R₀ p₀ O hO 1
    rw [pow_one, pow_one] at hm
    rw [← hm, Ideal.map_map, ← IsScalarTower.algebraMap_eq R₀ O B, Ideal.map_le_iff_le_comap]
    intro c hc
    exact (h0B c).2 hc
  have hloc : IsLocalHom (algebraMap O B) := by
    refine ⟨fun o ho => ?_⟩
    by_contra hn
    exact (IsLocalRing.mem_maximalIdeal _).1
      (hmO (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hn))) ho
  have e : ∀ c : R₀, algebraMap O B (algebraMap R₀ O c) = algebraMap R B (algebraMap R₀ R c) := by
    intro c
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hres : ∀ x : B, ∃ o : O, x - algebraMap O B o ∈ maximalIdeal B := by
    intro x
    obtain ⟨a, s, hs, hx⟩ := hB.dense 1 x
    rw [pow_one] at hx
    obtain ⟨s₀, hs₀⟩ := hsurj s
    obtain ⟨a₀, ha₀⟩ := hsurj a
    have h1 : algebraMap R B s - algebraMap O B (algebraMap R₀ O s₀) ∈ maximalIdeal B := by
      rw [e, ← map_sub]
      exact (hRB _).2 hs₀
    have h2 : algebraMap R B a - algebraMap O B (algebraMap R₀ O a₀) ∈ maximalIdeal B := by
      rw [e, ← map_sub]
      exact (hRB _).2 ha₀
    have hsu : IsUnit (algebraMap O B (algebraMap R₀ O s₀)) := by
      by_contra hn
      have hm : algebraMap O B (algebraMap R₀ O s₀) ∈ maximalIdeal B :=
        (IsLocalRing.mem_maximalIdeal _).2 hn
      have hsum := Ideal.add_mem _ h1 hm
      rw [sub_add_cancel] at hsum
      exact hs ((hRB s).1 hsum)
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hsu
    refine ⟨↑u⁻¹ * algebraMap R₀ O a₀, ?_⟩
    have key : algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀)
        ∈ maximalIdeal B := by
      have hid : algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀) =
          (algebraMap R B s * x - algebraMap R B a)
            - (algebraMap R B s - algebraMap O B (algebraMap R₀ O s₀)) * x
            + (algebraMap R B a - algebraMap O B (algebraMap R₀ O a₀)) := by ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ hx (Ideal.mul_mem_right _ _ h1)) h2
    have hinv : algebraMap O B ↑u⁻¹ * algebraMap O B ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hid2 : x - algebraMap O B (↑u⁻¹ * algebraMap R₀ O a₀) = algebraMap O B ↑u⁻¹ *
        (algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀)) := by
      rw [← hu, map_mul]
      linear_combination (-x) * hinv
    rw [hid2]
    exact Ideal.mul_mem_left _ _ key
  haveI := hB.noeth
  exact UpperTheory.V.Alg.IsCO.mk hB.complete hloc hres
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  have : Module.Finite R S := by
    have : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  have : IsMulCommutative S := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hT i j)
  let _ : CommRing S := by
    open scoped IsMulCommutative in
    exact inferInstance
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
end
