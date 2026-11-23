module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle004
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchStrictAntiSplit.add_gap_le {r : ℕ} {d : Fin r → ℕ} (hd : StrictAnti d) :
    ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → d j + k ≤ d i :=
  _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd

theorem SchStrictAntiSplit.sum_staircase (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r,
    Finset.sum_range_id]

theorem SchStrictAntiSplit.proof : SchStrictAntiSplit.Statement := by
  intro r n d hd hsum
  have hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i := by
    intro i
    have hr : 0 < r := Fin.pos i
    have h := SchStrictAntiSplit.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩
      (by simp; omega)
    omega
  refine ⟨hlow, ?_⟩
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, ?_⟩
  · have hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) =
        ∑ i : Fin r, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)
    rw [SchStrictAntiSplit.sum_staircase] at hadd
    omega
  · intro i j hij
    have h := SchStrictAntiSplit.add_gap_le hd ((j : ℕ) - i) i j (by omega)
    have := hlow i
    have := hlow j
    have : (i : ℕ) ≤ j := hij
    have : (j : ℕ) < r := j.isLt
    show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))
    omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem antisymmetrize_C_mul (f N : ℕ) (k : ℚ) (H : RootRing f N) :
    antisymmetrize f N (C k * H) = C k * antisymmetrize f N H := by
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [blockPermute]

theorem blockVandermonde_ne_zero (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  unfold blockVandermonde vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
  intro h
  have h' := X_injective h
  simp only [Prod.mk.injEq, true_and] at h'
  exact (ne_of_lt (Finset.mem_Ioi.mp hj)) h'

theorem LemmaB.proof (h1 : SchAevalSignedRename.Statement) (h2 : SchAntisymmetrizePlace.Statement)
    (h3 : SchSmallBlockProduct.Statement) (h4 : SchConcatAlternant.Statement)
    (h5 : SchConcatAlternantZero.Statement) (h6 : SchBlockVandermondeOne.Statement)
    (h7 : SchSchurHomogeneous.Statement) : LemmaB.Statement := by
  intro r a c
  obtain ⟨s, hs, hconc⟩ := h4 r a c
  have hsgn : ∀ n : ℕ, c.sign ^ n = 1 ∨ c.sign ^ n = -1 := by
    intro n
    cases c <;> simp [SmallBlock.sign, neg_one_pow_eq_or]
  refine ⟨s * ((r.factorial : ℚ) * a.factorial) * c.sign ^ (r * (r - 1) / 2 + r * a), ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hsgn (r * (r - 1) / 2 + r * a) with h | h <;>
      rw [h] <;> first | (left; ring1) | (right; ring1)
  intro lam hlam
  have hV : algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
      (blockVandermonde 1 (r + a)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero 1 (r + a))
  unfold dividedDifference
  rw [h3, antisymmetrize_C_mul, h2, KAlt.antisym_rename_mul_rename, map_smul]
  split_ifs with hcont
  · rw [hconc lam hcont, div_eq_iff hV, ← map_mul]
    congr 1
    have hA := h1 (Fin (r + a)) (Fin 1 × Fin (r + a)) c.sign (fun i => ((0 : Fin 1), i))
      (∑ i, (lam i - a)) (schur (Fin (r + a)) (fun i : Fin r => lam i - a))
      (h7 (Fin (r + a)) r (fun i : Fin r => lam i - a))
    have hsum : ∑ i, lam i = ∑ i, (lam i - a) + r * a := by
      rw [show r * a = ∑ _i : Fin r, a by simp, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hcont i)).symm
    rw [hA, h6, map_mul, hsum, smul_eq_C_mul]
    simp only [map_mul, map_pow, map_natCast]
    ring
  · rw [h5 r a lam hlam hcont, map_zero, smul_zero, mul_zero, map_zero, zero_div]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def flagIntegralReal (f N : ℕ) : MvPolynomial (Fin f × Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun G := ∑ α ∈ (blockVandermonde f N).support,
    AddMonoidAlgebra.coeff G α * ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) * α.prod (fun _ e => (e.factorial : ℝ))
  map_add' G H := by simp only [MvPolynomial.coeff_add, add_mul, sum_add_distrib]
  map_smul' c G := by simp only [MvPolynomial.coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem flagIntegralReal_map (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by
  simp [flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]

namespace FlagEq

theorem flagIntegralReal_eq {f N : ℕ} (G : MvPolynomial (Fin f × Fin N) ℝ) :
    flagIntegralReal f N G =
      stairConst f N * ∑ w, ((permSign f N w : ℤ) : ℝ) * AddMonoidAlgebra.coeff G (stairExp f N w) := by
  classical
  have hsub : (blockVandermonde f N).support ⊆
      (blockVandermonde f N).support ∪ univ.image (stairExp f N) := subset_union_left
  show ∑ α ∈ _, _ = _
  rw [sum_subset hsub (fun α _ hα => by rw [notMem_support_iff.mp hα]; simp)]
  have hc : ∀ α : Fin f × Fin N →₀ ℕ, ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) =
      ∑ w, ((permSign f N w : ℤ) : ℝ) * if stairExp f N w = α then 1 else 0 := by
    intro α
    rw [coeff_blockVandermonde, Rat.cast_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hc, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [sum_ite_eq, if_pos (mem_union_right _ (mem_image_of_mem _ (mem_univ w))),
    prod_factorial_stairExp]
  ring

theorem ddConst_apply (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      AddMonoidAlgebra.coeff (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) (rho f (j + k)) := by
  simp [IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho,
    IndefiniteRowSideFullHecke.RestTerms.rhoMon, coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]

theorem ddConst_eq (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * AddMonoidAlgebra.coeff G (stairExp f (j + k) w) := by
  rw [ddConst_apply, coeff_rho_antisym]

theorem rename_psumAt (f j k m : ℕ) (τ : Fin f) (w : Fin f → Equiv.Perm (Fin (j + k))) :
    rename (Equiv.prodCongrRight w) (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by

  simp only [IndefiniteRowSideFullHecke.RestTerms.psumAt, map_sum, map_pow, rename_X, Equiv.prodCongrRight_apply]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) ^ m)

def antisym (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G

theorem antisym_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    antisym f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * antisym f j k G := by
  simp only [antisym, map_mul, rename_psumAt, mul_sum, mul_smul_comm]

theorem rename_antisym (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by
  have hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)),
      rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) =
        rename (Equiv.prodCongrRight (u * w)) G := by
    intro w
    rw [rename_rename]
    congr 1
  have hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1 := by
    exact_mod_cast permSign_mul_self u

  simp only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft, permSign_mul]
  push_cast
  rw [← mul_assoc, hs, one_mul]

theorem coeff_eq_zero_of_swap {f N : ℕ} (A : MvPolynomial (Fin f × Fin N) ℝ)
    (hA : ∀ u : Fin f → Equiv.Perm (Fin N),
      rename (Equiv.prodCongrRight u) A = ((permSign f N u : ℤ) : ℝ) • A)
    (β : Fin f × Fin N →₀ ℕ) (τ : Fin f) (i i' : Fin N) (hii : i ≠ i')
    (hβ : β (τ, i) = β (τ, i')) : AddMonoidAlgebra.coeff A β = 0 := by
  classical
  let u : Fin f → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap i i')
  have hu1 : u τ = Equiv.swap i i' := Pi.mulSingle_eq_same _ _
  have hu2 : ∀ τ', τ' ≠ τ → u τ' = 1 := fun τ' h => Pi.mulSingle_eq_of_ne h _
  have hs : permSign f N u = -1 := by
    rw [permSign, Fintype.prod_eq_single τ]
    · rw [hu1, Equiv.Perm.sign_swap hii]; rfl
    · intro τ' h; rw [hu2 τ' h]; simp
  have hfix : (Finsupp.equivFunOnFinite.symm fun v => β (Equiv.prodCongrRight u v)) = β := by
    ext ⟨τ', l⟩
    simp only [Finsupp.coe_equivFunOnFinite_symm, Equiv.prodCongrRight_apply]
    by_cases h : τ' = τ
    · subst h
      rw [hu1]
      rcases eq_or_ne l i with rfl | h1
      · rw [Equiv.swap_apply_left, hβ]
      · rcases eq_or_ne l i' with rfl | h2
        · rw [Equiv.swap_apply_right, hβ]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hu2 τ' h]; rfl
  have h := congrArg (AddMonoidAlgebra.coeff · β) (hA u)
  rw [coeff_rename_prodCongrRight, hfix, hs, MvPolynomial.coeff_smul, smul_eq_mul] at h
  push_cast at h
  linarith

theorem ddConst_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by
  classical
  rw [ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [Finsupp.single_le_iff] at h
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm] at h
    have hi : (i : ℕ) + m < j + k := by have := i.isLt; omega
    have hii : i ≠ ⟨(i : ℕ) + m, hi⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rfl

theorem ddConst_monomial_rho (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by
  rw [ddConst_eq, Fintype.sum_eq_single 1]
  · simp [stairExp_one, permSign_one]
  · intro w hw
    rw [coeff_monomial, if_neg (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]

end FlagEq


open FlagEq in
theorem flagIntegralReal_eq_mul_ddConst (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by
  rw [flagIntegralReal_eq, ddConst_eq]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchWeightedPreimage.proof (h1 : SchPowerSumHomWeighted.Statement) :
    SchWeightedPreimage.Statement := by
  classical
  intro N k P hsym hhom
  obtain ⟨S₀, hS₀⟩ := Flag.exists_powerSumHom_eq hsym
  let w : Fin N → ℕ := fun i => (i : ℕ) + 1
  refine ⟨weightedHomogeneousComponent w k S₀, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous k S₀⟩
  have hfin := weightedHomogeneousComponent_finsupp (w := w) S₀
  have hsum := sum_weightedHomogeneousComponent w S₀
  rw [finsum_eq_sum _ hfin] at hsum
  have hterm : ∀ m : ℕ, homogeneousComponent k (powerSumHom N (weightedHomogeneousComponent w m S₀))
      = if k = m then powerSumHom N (weightedHomogeneousComponent w m S₀) else 0 :=
    fun m => homogeneousComponent_of_mem
      (h1 N m _ (weightedHomogeneousComponent_isWeightedHomogeneous m S₀))
  have key : homogeneousComponent k (powerSumHom N S₀) =
      powerSumHom N (weightedHomogeneousComponent w k S₀) := by
    conv_lhs => rw [← hsum]

    rw [map_sum, map_sum]
    simp only [hterm, Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have hk0 : weightedHomogeneousComponent w k S₀ = 0 := by
        by_contra hne
        exact hk (Set.Finite.mem_toFinset (hs := hfin) |>.mpr hne)
      rw [hk0, map_zero]
  rw [← key, hS₀, homogeneousComponent_eq_self hhom]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  unfold rootOfUnity
  exact Complex.isPrimitiveRoot_exp k (by omega)

theorem SchRootOfUnityVandermondeNe.proof : SchRootOfUnityVandermondeNe.Statement := by
  intro k hk
  have hz := SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot hk
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro h
  have hij : (i : ℕ) = j := hz.pow_inj i.isLt j.isLt h
  have hlt : i < j := Finset.mem_Ioi.mp hj
  exact absurd (Fin.ext hij) (ne_of_lt hlt)

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  simpa [rootOfUnity] using Complex.isPrimitiveRoot_exp k (by omega)

theorem SchPowerSumAtRootsOfUnity.proof : SchPowerSumAtRootsOfUnity.Statement := by
  intro N k j hk hkN hj
  have hprim := SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot hk

  simp only [psum, map_sum, map_pow, aeval_X]
  have hsum : ∑ i : Fin N, rootOfUnityPoint N k i ^ j =
      ∑ i ∈ range k, (rootOfUnity k ^ j) ^ i := by
    unfold rootOfUnityPoint
    rw [Fin.sum_univ_eq_sum_range (fun i => (if i < k then rootOfUnity k ^ i else 0) ^ j) N,
      ← Finset.sum_range_add_sum_Ico _ hkN]
    rw [Finset.sum_eq_zero (s := Ico k N) (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp [show ¬ i < k by omega, zero_pow (show j ≠ 0 by omega)]), add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hi, ← pow_mul, mul_comm]
  rw [hsum]
  split_ifs with hd
  · have h1 : rootOfUnity k ^ j = 1 := (hprim.pow_eq_one_iff_dvd j).2 hd
    simp [h1]
  · have h1 : rootOfUnity k ^ j ≠ 1 := fun h => hd ((hprim.pow_eq_one_iff_dvd j).1 h)
    have h2 : (rootOfUnity k ^ j) ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagAltCoeffInjective.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagAltCoeffInjective.Statement := by
  classical
  intro f N P α hP hc τ i j hij
  simp only at hij
  by_contra hne
  let w : Fin f → Equiv.Perm (Fin N) := Function.update 1 τ (Equiv.swap i j)
  have hsign : blockSign f N w = -1 := by
    unfold blockSign
    rw [Finset.prod_eq_single τ]
    · simp [w, Equiv.Perm.sign_swap hne]
    · intro b _ hb
      simp [w, Function.update_of_ne hb]
    · simp
  have hα : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α := by
    ext ⟨σ, k⟩
    change α (σ, w σ k) = α (σ, k)
    by_cases hσ : σ = τ
    · subst hσ
      simp only [w, Function.update_self]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left]; exact hij.symm
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Equiv.swap_apply_right]; exact hij
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · simp [w, Function.update_of_ne hσ]
  have key := h1 f N w P α
  rw [hα, hP w, hsign, MvPolynomial.coeff_smul] at key
  have : AddMonoidAlgebra.coeff P α = 0 := by
    have h2 : (2 : ℚ) * AddMonoidAlgebra.coeff P α = 0 := by
      rw [smul_eq_mul] at key
      linarith
    simpa using h2
  exact hc this

end RestTerms

end GroundTheory.Heights₂.Heights
end
