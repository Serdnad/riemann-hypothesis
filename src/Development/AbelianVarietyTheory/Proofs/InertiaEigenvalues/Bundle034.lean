module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.MeasureTheory.Group.Measure
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open Matrix
namespace GlobalTheory
private lemma rank_fromBlocks_one_zero_lemma {F G : Type} [Field F] [Field G] (r s : ℕ) :
    (fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (0 : Matrix (Fin s) (Fin s) F)).rank =
      (fromBlocks (1 : Matrix (Fin r) (Fin r) G) 0 0 (0 : Matrix (Fin s) (Fin s) G)).rank := by
  classical
  rw [← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal,
    ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by cases i <;> simp)
theorem matrix_rank_map_field {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := exists_rank_normal_form M
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det _).1 hV
  have hUd : IsUnit U.det := (isUnit_iff_isUnit_det _).1 hU
  have hV' : IsUnit (V.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hVd.map φ
  have hU' : IsUnit (U.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hUd.map φ
  have hmap : V.map φ * M.map φ * U.map φ =
      (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0 0).submatrix e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h, ← submatrix_map, fromBlocks_map]
    simp
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hU', rank_mul_eq_right_of_isUnit_det _ _ hV']
    _ = (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0 0).rank := by
        rw [hmap, rank_submatrix]
        exact rank_fromBlocks_one_zero_lemma _ _
    _ = (V * M * U).rank := by rw [h, rank_submatrix]
    _ = M.rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]
end GlobalTheory
end

section

open Polynomial
namespace GlobalTheory
theorem finrank_le_of_first_order_kernel (k V U : Type) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup U] [Module k U] [Module.Finite k U] (e : ℕ) (t u : V →ₗ[k] U)
    (h : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) :
    Module.finrank k V ≤ Module.finrank k U + e := by
  classical
  set q : LinearMap.ker t →ₗ[k] U ⧸ LinearMap.range t :=
    (LinearMap.range t).mkQ ∘ₗ u ∘ₗ (LinearMap.ker t).subtype

  have hq : Module.finrank k (LinearMap.ker q) ≤ e := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k) (M := LinearMap.ker q)
      (n := e + 1) hlt
    have hmem : ∀ j, u ((f j : LinearMap.ker t) : V) ∈ LinearMap.range t := by
      intro j
      have hj : (LinearMap.range t).mkQ (u ((f j : LinearMap.ker t) : V)) = 0 :=
        LinearMap.mem_ker.mp (f j).2
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hj
      exact hj
    choose y hy using fun j => LinearMap.mem_range.mp (hmem j)
    have hli : LinearIndependent k (fun j => ((f j : LinearMap.ker t) : V)) :=
      (hf.map' _ (Submodule.ker_subtype _)).map' _ (Submodule.ker_subtype _)
    exact h (fun j => ((f j : LinearMap.ker t) : V)) y
      (fun j => ⟨LinearMap.mem_ker.mp (f j : LinearMap.ker t).2, hy j⟩) hli
  have h1 := LinearMap.finrank_range_add_finrank_ker t
  have h2 := LinearMap.finrank_range_add_finrank_ker q
  have h3 := Submodule.finrank_le (LinearMap.range q)
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.range t)
  omega

theorem rank_le_rank_map_algebraMap (k K : Type) [Field k] [Field K] [Algebra k K] (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) k) : Φ.rank ≤ (Φ.map (algebraMap k K)).rank := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k)
    (M := LinearMap.range Φ.mulVecLin) (n := Φ.rank) (Matrix.finrank_range_mulVecLin Φ).ge
  have hv : LinearIndependent k (fun i => ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    hf.map' _ (Submodule.ker_subtype _)

  have hw : LinearIndependent K
      (fun i => algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hmem : ∀ i, algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k) ∈
      LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := by
    intro i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (f i).2
    refine ⟨algebraMap k K ∘ y, ?_⟩
    rw [← hy]
    funext j
    simp only [Matrix.mulVecLin_apply, Function.comp_apply]
    exact (RingHom.map_mulVec _ _ _ j).symm
  let g : Fin Φ.rank → LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := fun i => ⟨_, hmem i⟩
  have hg : LinearIndependent K g := LinearIndependent.of_comp (LinearMap.range _).subtype hw
  have hc := hg.fintype_card_le_finrank
  rw [Fintype.card_fin] at hc
  exact hc.trans_eq (Matrix.finrank_range_mulVecLin _)

theorem finrank_ker_map_le_of_first_order_kernel : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  intro k K _ _ _ a e Φ U _ _ _ t u h
  have h1 := finrank_le_of_first_order_kernel k (LinearMap.ker Φ.mulVecLin) U e t u h
  have h2 := rank_le_rank_map_algebraMap k K a Φ
  have hk := LinearMap.finrank_range_add_finrank_ker Φ.mulVecLin
  have hK := LinearMap.finrank_range_add_finrank_ker (Φ.map (algebraMap k K)).mulVecLin
  rw [Module.finrank_fin_fun] at hk hK
  rw [← Matrix.finrank_range_mulVecLin Φ, ← Matrix.finrank_range_mulVecLin (Φ.map (algebraMap k K))] at h2
  omega
end GlobalTheory
end

section

open TensorProduct Module

theorem GlobalTheory.tensorBasisCoords : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  intro F _ B _ _ V _ _ n _ _ b
  let e : V ⊗[F] B ≃ₗ[F] (n → B) :=
    (TensorProduct.comm F V B) ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl F B) b.equivFun) ≪≫ₗ
      TensorProduct.piScalarRight F F B n
  have h1 : ∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x := by
    intro v x i
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hadd : ∀ y z : V ⊗[F] B, e (y + z) = e y + e z := fun y z => map_add e y z
  refine ⟨e, h1, ?_, ?_⟩
  · intro y
    rw [LinearEquiv.symm_apply_eq]
    funext j

    rw [map_sum, Finset.sum_apply]
    simp only [h1, Basis.repr_self, Finsupp.single_apply]
    simp
  · intro r f y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      rw [show (fun _ : n => f ((0 : n → B) _)) = 0 from by funext i; simp, Matrix.mulVec_zero]
    | tmul v x =>
      funext i
      rw [TensorProduct.map_tmul, h1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix_apply, h1, map_smul]
      simp_rw [← Algebra.smul_def, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.sum_repr v]

      rw [map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    | add y z hy hz =>
      rw [map_add (f := _), hadd, hy, hz, hadd, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add (f := _)]
end

section

open Polynomial

namespace GlobalTheory

theorem isNilpotent_residue_toMatrix_mulLeft : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  intro R S _ _ _ _ _ n b t ht
  let φ : S →ₐ[R] Matrix (Fin n) (Fin n) R :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul R S)
  have hφ : ∀ s, φ s = LinearMap.toMatrix b b (LinearMap.mulLeft R s) := by
    intro s; ext i j
    simp [φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  set N := LinearMap.toMatrix b b (LinearMap.mulLeft R t) with hN
  set Nb := N.map (IsLocalRing.residue R) with hNb
  have hcp : Nb.charpoly ≠ 0 := (Matrix.charpoly_monic Nb).ne_zero
  obtain ⟨hb, hfac, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Nb.charpoly hcp 0
  have h0 : hb.eval 0 ≠ 0 := by
    intro h; apply hndvd; rw [dvd_iff_isRoot]; exact h
  obtain ⟨h, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R)
    IsLocalRing.residue_surjective hb
  have hu0 : IsUnit (h.coeff 0) := by
    by_contra hc
    apply h0
    rw [← coeff_zero_eq_eval_zero, coeff_map]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hc)
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := h)
  have hsplit : aeval t h = algebraMap R S (h.coeff 0) + t * aeval t q := by
    have : h = C (h.coeff 0) + X * q := by rw [← hq]; ring
    conv_lhs => rw [this]
    simp
  have hut : IsUnit (aeval t h) := by
    rw [hsplit]
    by_contra hc
    have h1 : algebraMap R S (h.coeff 0) + t * aeval t q ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).2 hc
    have h2 : t * aeval t q ∈ IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_right _ _ ht
    have h3 : algebraMap R S (h.coeff 0) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 (hu0.map (algebraMap R S))
  have huN : IsUnit (aeval N h) := by
    have := hut.map φ
    rwa [← Polynomial.aeval_algHom_apply, hφ] at this
  have hmap : (IsLocalRing.residue R).mapMatrix (aeval N h) = aeval Nb (h.map (IsLocalRing.residue R)) := by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    ext r i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp
  have huNb : IsUnit (aeval Nb (h.map (IsLocalRing.residue R))) := by
    rw [← hmap]; exact huN.map _
  have hCH := Matrix.aeval_self_charpoly Nb
  rw [hfac, C_0, sub_zero, map_mul, map_pow, aeval_X] at hCH
  exact ⟨_, (huNb.mul_left_eq_zero).1 hCH⟩

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem linearForm_matrix_eq_smul_trace_of_comm (k : Type) [Field k] (m : ℕ)
    (t : Matrix (Fin m) (Fin m) k →ₗ[k] k) (ht : ∀ x y, t (x * y) = t (y * x)) :
    ∃ c : k, ∀ x, t x = c * x.trace := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨0, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : k, t (single (⟨0, hm⟩ : Fin m) ⟨0, hm⟩ 1) = c := ⟨_, rfl⟩
    refine ⟨c, fun x => ?_⟩
    set o : Fin m := ⟨0, hm⟩
    have key : ∀ a b : Fin m, t (single a b 1) = if a = b then c else 0 := by
      intro a b
      split_ifs with hab
      · subst hab
        have h1 : single a a (1 : k) = single a o 1 * single o a 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single o o (1 : k) = single o a 1 * single a o 1 := by
          rw [single_mul_single_same, mul_one]
        rw [h1, ht, ← h2, hc]
      · have h1 : single a b (1 : k) = single a a 1 * single a b 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single a b (1 : k) * single a a 1 = 0 :=
          single_mul_single_of_ne (1 : k) a b a (Ne.symm hab) 1
        rw [h1, ht, h2, map_zero]
    have hx : x = ∑ a, ∑ b, x a b • single a b (1 : k) := by
      conv_lhs => rw [matrix_eq_sum_single x]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [hx]

    simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
    rw [trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]

theorem centralLinearForm_pi_matrix_eq_sum_trace :
    ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ)
      (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k),
      (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  intro k _ N n τ hτ
  have h : ∀ i, ∃ c : k, ∀ A, (τ ∘ₗ LinearMap.single k (fun i => Matrix (Fin (n i)) (Fin (n i)) k) i) A
      = c * A.trace := by
    intro i
    refine linearForm_matrix_eq_smul_trace_of_comm k (n i) _ fun A B => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Pi.single_mul, Pi.single_mul, hτ]
  choose c hc using h
  refine ⟨c, fun x => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hc i (x i)
  simpa using this

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

noncomputable def blockDiagMultAlgHom (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) :
    (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k]
      Matrix (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) k where
  toFun x := blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)
  map_one' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 1
    exact blockDiagonal'_one
  map_mul' x y := by
    simp only [Pi.mul_apply]
    exact blockDiagonal'_mul _ _
  map_zero' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (0 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 0
    exact blockDiagonal'_zero
  map_add' x y := by
    simp only [Pi.add_apply]
    exact (blockDiagonal'_add _ _)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    simp only [Pi.smul_apply, Pi.one_apply]
    rw [show (fun j : (Σ i, Fin (m i)) => r • (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k))
        = r • (fun j => 1) from rfl, blockDiagonal'_smul]
    congr 1
    exact blockDiagonal'_one

theorem blockDiagMultAlgHom_trace (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ)
    (x : Π i, Matrix (Fin (n i)) (Fin (n i)) k) :
    (blockDiagMultAlgHom k N n m x).trace = ∑ i, (m i : k) * (x i).trace := by
  show (blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)).trace = _
  rw [trace_blockDiagonal', Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ _y : Fin (m i), (x i).trace = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_algHom_trace_eq_sum_mult_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ),
    ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k,
      ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  intro k _ N n m d hd
  have hcard : Fintype.card (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) = d := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, ← hd]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨(reindexAlgEquiv k k e).toAlgHom.comp (blockDiagMultAlgHom k N n m), fun x => ?_⟩
  rw [← blockDiagMultAlgHom_trace]
  show (reindex e e (blockDiagMultAlgHom k N n m x)).trace = _
  simp only [reindex_apply, trace, diag, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => blockDiagMultAlgHom k N n m x i i)

end GlobalTheory
end

section

namespace GlobalTheory.TargetStatementAlt

open Polynomial

theorem main {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) :
    IsIntegral R (Matrix.trace M) := by
  let f : F →ₐ[R] AlgebraicClosure F := IsScalarTower.toAlgHom R F (AlgebraicClosure F)
  let φ : Matrix n n F →ₐ[R] Matrix n n (AlgebraicClosure F) := f.mapMatrix
  obtain ⟨p, hpm, hp⟩ := hM.map φ
  have key : ∀ μ ∈ (φ M).charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.mp hμ).2
    have hs : μ ∈ spectrum (AlgebraicClosure F) (φ M) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F)))
      ⟨μ, hs, rfl⟩
    have h2 : aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h2, spectrum.mem_iff, sub_zero] at h1
    refine ⟨p, hpm, ?_⟩
    by_contra hne
    apply h1
    have : eval μ (p.map (algebraMap R (AlgebraicClosure F))) ≠ 0 := by
      rwa [eval_map_algebraMap, aeval_def]
    exact (Ne.isUnit this).map _
  have ht : IsIntegral R (Matrix.trace (φ M)) := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum key
  have he : Matrix.trace (φ M) = f (Matrix.trace M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [φ, Matrix.trace, map_sum, AlgHom.mapMatrix_apply]
  rw [he] at ht
  exact (isIntegral_algHom_iff f f.toRingHom.injective).mp ht

theorem target : ∀ {R F : Type} [inst : CommRing R] [inst_1 : Field F] [inst_2 : Algebra R F] {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] (M : Matrix n n F), IsIntegral R M → IsIntegral R (Matrix.trace M) :=
  fun M h => main M h

end GlobalTheory.TargetStatementAlt
end

section

open MeasureTheory

namespace GlobalTheory

theorem map_pi_eq_of_map_addHaar_eq (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (φ : G →+ G) (hφ : Continuous φ)
    (h : ∀ ν : Measure G, ν.IsAddHaarMeasure → ν.map φ = ν) (m : ℕ)
    (μ : @Measure (Fin m → G) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Fin m → G) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x i => φ (x i)) μ = μ := by
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin m → G)) = borel _ := BorelSpace.measurable_eq
  revert μ hμ
  rw [← hb]
  intro μ hμ
  let ν : Measure G := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hp : MeasurePreserving φ ν ν := ⟨hφ.measurable, h ν hν⟩
  have hpi : MeasurePreserving (fun (x : Fin m → G) i => φ (x i)) (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_pi _ _ (fun _ => hp)
  have hH : (Measure.pi fun _ : Fin m => ν).IsAddHaarMeasure := inferInstance
  have he := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin m => ν)
  generalize Measure.addHaarScalarFactor μ (Measure.pi fun _ : Fin m => ν) = c at he
  subst he
  rw [Measure.map_smul c hpi.measurable.aemeasurable, hpi.map_eq]

end GlobalTheory
end
