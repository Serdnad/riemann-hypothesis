module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle004
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
public import Mathlib.LinearAlgebra.Lagrange
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
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAltPartitionExpansion.alt_partition_add_stair_eq {r : ℕ} (lam : Fin r → ℕ) :
    Comb.alt (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) =
      vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam := by
  unfold Comb.alt
  rw [← Matrix.det_transpose, mul_comm]
  exact Schur.det_pow_add_staircase_eq lam

theorem SchAltPartitionExpansion.strictAnti_partition_add_stair {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by
  unfold partitionsOf at hlam
  rw [Finset.mem_filter] at hlam
  intro i j hij
  have h1 := hlam.2 i j hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  simp only
  omega

theorem SchAltPartitionExpansion.proof (h1 : SchStrictAntiSplit.Statement) :
    SchAltPartitionExpansion.Statement := by
  intro r n P hP hhom
  set e : (Fin r → ℕ) → (Fin r →₀ ℕ) := fun lam =>
    Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)) with he
  have e_inj : Set.InjOn e (partitionsOf r n : Set (Fin r → ℕ)) := by
    intro a _ b _ hab
    funext i
    have := congrArg (fun f : Fin r →₀ ℕ => f i) hab
    simp only [he, Finsupp.coe_equivFunOnFinite_symm] at this
    omega

  have hR : ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (e lam)) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam) =
      ∑ d ∈ (partitionsOf r n).image e, AddMonoidAlgebra.coeff P d • Comb.alt (⇑d) := by
    rw [Finset.sum_image e_inj]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [C_mul', ← SchAltPartitionExpansion.alt_partition_add_stair_eq]
    simp [he]
  rw [hR]
  conv_lhs => rw [Comb.IsAlt.eq_sum_alt hP]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hsum : ∑ i, d i = r * (r - 1) / 2 + n := by
      have := hhom (mem_support_iff.mp hd.1)
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact this
    obtain ⟨hge, hmem⟩ := h1 r n (⇑d) hd.2 hsum
    refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
    ext i
    simp only [he, Finsupp.coe_equivFunOnFinite_symm]
    have := hge i
    omega
  · intro d hd hnot
    obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp hd
    have hz : AddMonoidAlgebra.coeff P (e lam) = 0 := by
      by_contra hne
      apply hnot
      rw [Finset.mem_filter]
      refine ⟨mem_support_iff.mpr hne, ?_⟩
      simpa [he] using SchAltPartitionExpansion.strictAnti_partition_add_stair hlam
    rw [hz, zero_smul]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def smallBlockPlaceEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv x := by
    cases c <;> rcases x with i | j <;>
      simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv p := by
    cases c
    · by_cases h : (p : ℕ) < a
      · simp [smallBlockPlace, smallBlockOf, zIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inl, yIndex]
        ext; simp; omega
    · by_cases h : (p : ℕ) < r
      · simp [smallBlockPlace, smallBlockOf, yIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inr, zIndex]
        ext; simp; omega

theorem smallBlockPlace_eq (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem SchAntisymmetrizePlace.proof : SchAntisymmetrizePlace.Statement := by
  intro r a c Q
  set e := smallBlockPlaceEquiv r a c with he
  unfold antisymmetrize antisym

  rw [map_sum]
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) _).trans e.symm.permCongr) _ _ ?_
  intro w
  simp only [Equiv.trans_apply, Equiv.funUnique_apply]
  rw [AlgHom.map_smul_of_tower, blockPermute, rename_rename, rename_rename]
  have hs : blockSign 1 (r + a) w = ((Equiv.Perm.sign (e.symm.permCongr (w 0)) : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_permCongr, blockSign, Fintype.prod_unique]
    rfl
  rw [hs]
  congr 3
  funext x
  simp [smallBlockPlace_eq, ← he]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace SchCompleteGenerating

theorem coeff_prod_geomSeries_eval {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by

  rw [PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Schur.geomSeries, PowerSeries.coeff_mk, map_prod]

theorem coe_prod_one_sub {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

theorem prod_one_sub_mul_prod_geomSeries {N : ℕ} (y : Fin N → ℂ) :
    (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      ∏ i : Fin N, Schur.geomSeries (y i) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm, Schur.geomSeries_mul]

theorem proof : Statement := by
  intro N y d
  have key := congrArg (PowerSeries.coeff d) (prod_one_sub_mul_prod_geomSeries y)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      PowerSeries.coeff b (∏ i : Fin N, Schur.geomSeries (y i))), PowerSeries.coeff_one] at key
  simp only [coeff_prod_geomSeries_eval, ← coe_prod_one_sub, Polynomial.coeff_coe] at key
  exact key

end SchCompleteGenerating

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternantZero.proof : SchConcatAlternantZero.Statement := by
  intro r a lam hanti hnot
  have hex : ∃ i, lam i < a := by
    by_contra h
    exact hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkv : (k : ℕ) = r - 1 := rfl
  have hik : i ≤ k := by
    rw [Fin.le_def, hkv]; omega
  have hka : lam k < a := lt_of_le_of_lt (hanti hik) hi
  let j : Fin a := ⟨a - 1 - lam k, by omega⟩
  have hjv : (j : ℕ) = a - 1 - lam k := rfl
  have hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ) := by
    rw [hkv, hjv]; omega
  unfold alternant
  apply Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr
  intro p
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hexp]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem psum_isHomogeneous_alt (N j : ℕ) : (psum (Fin N) ℚ j).IsHomogeneous j :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j

theorem SchPowerSumHomWeighted.proof : SchPowerSumHomWeighted.Statement := by
  intro N d S hS

  rw [S.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = d :=
    hS (mem_support_iff.mp he)
  rw [powerSumHom, aeval_monomial, Finsupp.prod, algebraMap_eq]
  have hprod : (∏ i ∈ e.support, psum (Fin N) ℚ ((i : ℕ) + 1) ^ e i).IsHomogeneous
      (∑ i ∈ e.support, ((i : ℕ) + 1) * e i) :=
    IsHomogeneous.prod _ _ _ fun i _ => (psum_isHomogeneous_alt N ((i : ℕ) + 1)).pow (e i)
  have hsum : ∑ i ∈ e.support, ((i : ℕ) + 1) * e i = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hsum] at hprod
  exact hprod.C_mul _

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem aeval_vandermondeOf_X {m : ℕ} (v : Fin m → ℂ) :
    aeval v (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) = vandermondeOf v := by
  simp [vandermondeOf, map_prod, map_sub, aeval_X]

theorem SchRootOfUnityBialternant.proof (h1 : SchSchurEvalMatrix.Statement) :
    SchRootOfUnityBialternant.Statement := by
  intro k nu hk
  have hw : ∀ j : Fin k, rootOfUnityPoint k k j = rootOfUnity k ^ (j : ℕ) := fun j => by
    simp [rootOfUnityPoint, j.isLt]
  have key := congrArg (aeval (rootOfUnityPoint k k)) (Schur.det_pow_add_staircase_eq nu)
  rw [map_mul, h1 k k k nu hk le_rfl, AlgHom.map_det, aeval_vandermondeOf_X] at key
  have hv : rootOfUnityPoint k k = fun i : Fin k => rootOfUnity k ^ (i : ℕ) := funext hw
  rw [hv] at key
  rw [← key]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, Matrix.map_apply, aeval_X, ← pow_mul]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSchurEvalMatrix.aeval_completeSymmetric (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by
  unfold completeSymmetric
  by_cases h0 : 0 ≤ d
  · rw [if_pos h0, h1 N k d.toNat hk hkN]
    have hdiv : (k ∣ d.toNat) ↔ ((k : ℤ) ∣ d) := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h0]
    by_cases hd : (k : ℤ) ∣ d
    · rw [if_pos (hdiv.mpr hd), if_pos ⟨h0, hd⟩]
    · rw [if_neg (fun h => hd (hdiv.mp h)), if_neg (fun h => hd h.2)]
  · rw [if_neg h0, map_zero, if_neg (fun h => h0 h.1)]

theorem SchSchurEvalMatrix.proof (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Complex

theorem rootOfUnity_pow_self (k : ℕ) (hk : k ≠ 0) : rootOfUnity k ^ k = 1 :=
  (Complex.isPrimitiveRoot_exp k hk).pow_eq_one

theorem rootOfUnity_pow_mod (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    rootOfUnity k ^ a = rootOfUnity k ^ (a % k) := by
  conv_lhs => rw [← Nat.mod_add_div a k, pow_add, pow_mul, rootOfUnity_pow_self k hk, one_pow,
    mul_one]

theorem SchRootOfUnityRowsEq.proof : SchRootOfUnityRowsEq.Statement := by
  intro k l i i' hne hmod
  have hk : k ≠ 0 := by
    rintro rfl
    exact i.elim0
  apply Matrix.det_zero_of_row_eq hne
  funext j
  simp only [Matrix.of_apply]
  rw [pow_mul', pow_mul', rootOfUnity_pow_mod k hk (l i), rootOfUnity_pow_mod k hk (l i'), hmod]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchRootOfUnityRowsPerm.proof : SchRootOfUnityRowsPerm.Statement := by
  intro k l π hk hl
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hζk : rootOfUnity k ^ k = 1 := by
    unfold rootOfUnity
    exact (Complex.isPrimitiveRoot_exp k hk0).pow_eq_one
  have hmod : ∀ j n : ℕ, rootOfUnity k ^ (j * n) = rootOfUnity k ^ (j * (n % k)) := by
    intro j n
    conv_lhs => rw [← Nat.mod_add_div n k]
    rw [mul_add, pow_add, mul_left_comm j k, pow_mul (rootOfUnity k) k, hζk, one_pow, mul_one]
  have hM : (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)) =
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).submatrix π id := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    rw [hmod, hl i]
  rw [hM, Matrix.det_permute]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Polynomial Finset

theorem SchProdOneSubRootsOfUnity.proof : SchProdOneSubRootsOfUnity.Statement := by
  intro k hk
  have hk0 : 0 < k := hk
  have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk0⟩
  have hζ : IsPrimitiveRoot (rootOfUnity k) k := by
    unfold rootOfUnity
    exact Complex.isPrimitiveRoot_exp k (Nat.pos_iff_ne_zero.mp hk0)
  set p : ℂ[X] := ∏ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X) with hp
  set q : ℂ[X] := 1 - X ^ k with hq
  have hpdeg : p.natDegree ≤ k := by
    have h1 : ∀ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X).natDegree ≤ 1 := fun i _ => by
      compute_degree
    refine (natDegree_prod_le _ _).trans ((sum_le_sum h1).trans ?_)
    simp
  have hqdeg : q.natDegree ≤ k := by
    rw [hq]; compute_degree
  have hdeg : (p - q).degree < #(insert (0 : ℂ) (nthRootsFinset k (1 : ℂ))) := by
    rw [card_insert_of_notMem (by simp [mem_nthRootsFinset hk0, zero_pow hk0.ne']),
      hζ.card_nthRootsFinset]
    refine (degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le hpdeg hqdeg))).trans_lt ?_
    exact_mod_cast Nat.lt_succ_self k
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ hdeg fun x hx => ?_
  rcases mem_insert.mp hx with rfl | hx
  · simp [hp, hq, eval_prod, zero_pow hk0.ne']
  · have hxk : x ^ k = 1 := (mem_nthRootsFinset hk0 _).mp hx
    have hinv : x⁻¹ ^ k = 1 := by rw [inv_pow, hxk, inv_one]
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hinv
    have hx0 : x ≠ 0 := by
      rintro rfl; simp [zero_pow hk0.ne'] at hxk
    have hzero : p.eval x = 0 := by
      rw [hp, eval_prod]
      refine prod_eq_zero (mem_range.mpr hi) ?_
      simp [hi', inv_mul_cancel₀ hx0]
    rw [hzero, hq]
    simp [hxk]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagPowerSumSymmetric.proof : FlagPowerSumSymmetric.Statement := by
  intro f N k τ w

  simp only [blockPowerSum, map_sum, map_pow, Flag.blockPermute_X]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : RootRing f N) ^ k)

end RestTerms

end GroundTheory.Heights₂.Heights
end
