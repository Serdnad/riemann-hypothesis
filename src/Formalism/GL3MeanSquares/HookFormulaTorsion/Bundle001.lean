module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

section

open Filter

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2





end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

section

namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

section A
open Finset

end A

section B
open Finset
open scoped ComplexOrder

end B

section C
open Finset MeasureTheory
open scoped ComplexOrder


end C

section D
open Finset
open scoped Nat

end D

section E
open Finset Matrix Unitary

end E

section F
open Finset

def bb (k rS : ℕ) (i : ℕ) : ℕ := if i < rS then i else if i < rS + (k + 1) then rS else i - k
def cc (k rS : ℕ) (j : ℕ) : ℕ := if j < rS then j else if j < rS + (k + 1) then rS else j

lemma inner (k rS j : ℕ) (hj : j < rS + (k + 1) + rS) :
    ((range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j)).card = cc k rS j := by
  have h : (range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j) = range (cc k rS j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    simp only [bb, cc]
    constructor
    · rintro ⟨h1, h2⟩
      split_ifs at h2 ⊢ <;> omega
    · intro h1
      refine ⟨by split_ifs at h1 <;> omega, ?_⟩
      split_ifs at h1 ⊢ <;> omega
  rw [h, card_range]

lemma total (k rS : ℕ) : ∑ j ∈ range (rS + (k + 1) + rS), cc k rS j = rS * (2 * k + 1 + 2 * rS) := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ range rS, cc k rS x = ∑ x ∈ range rS, x :=
    Finset.sum_congr rfl fun x hx => by simp [cc, mem_range.1 hx]
  have e2 : ∑ x ∈ range (k + 1), cc k rS (rS + x) = ∑ x ∈ range (k + 1), rS :=
    Finset.sum_congr rfl fun x hx => by
      have := mem_range.1 hx
      simp only [cc]
      split_ifs <;> omega
  have e3 : ∑ x ∈ range rS, cc k rS (rS + (k + 1) + x) = ∑ x ∈ range rS, (rS + (k + 1) + x) :=
    Finset.sum_congr rfl fun x _ => by
      simp only [cc]
      split_ifs <;> omega
  rw [e1, e2, e3, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, card_range, card_range,
    smul_eq_mul, smul_eq_mul]
  have hS := Finset.sum_range_id_mul_two rS
  rcases rS with _ | m
  · simp
  · simp only [Nat.add_sub_cancel] at hS
    nlinarith [hS]

lemma countFree (k rS r : ℕ) (hr : r = rS + (k + 1) + rS) :
    (univ.filter (fun ij : Fin r × Fin r => bb k rS ij.1.val < bb k rS ij.2.val)).card =
      rS * (2 * k + 1 + 2 * rS) := by
  subst hr
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin (rS + (k + 1) + rS),
      ∑ i : Fin (rS + (k + 1) + rS), (if bb k rS i.val < bb k rS j.val then 1 else 0) = cc k rS j.val := by
    intro j
    have h1 := inner k rS j.val j.isLt
    rw [Finset.card_filter] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => if bb k rS i < bb k rS j.val then 1 else 0), h1]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun j => cc k rS j), total]

end F

end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

namespace Formalism.HermitianLattices.CumulantEstimateDefs

end Formalism.HermitianLattices.CumulantEstimateDefs
end

section

namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums

open Module Finset Matrix

section IdxDet

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem lenQuotSpan (ϖ : R) (hϖ : Irreducible ϖ) (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = emultiplicity ϖ a := by
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : Ideal.span ({(w : R) * ϖ ^ k} : Set R) = IsLocalRing.maximalIdeal R ^ k := by
    rw [Ideal.span_singleton_mul_left_unit w.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [h1, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
    emultiplicity_eq_of_associated_right (associated_unit_mul_left (ϖ ^ k) (w : R) w.isUnit),
    emultiplicity_pow_self_of_prime hϖ.prime]

theorem mulVecLin_inj {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n R) (hu : u.det ≠ 0) :
    Function.Injective u.mulVecLin := by
  intro x y hxy
  simp only [Matrix.mulVecLin_apply] at hxy
  have h2 : u.adjugate *ᵥ (u *ᵥ x) = u.adjugate *ᵥ (u *ᵥ y) := by rw [hxy]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  exact smul_right_injective _ hu h2

theorem endo_inj {n : Type} [Fintype n] [DecidableEq n] (P : (n → R) →ₗ[R] (n → R))
    (hP : LinearMap.det P ≠ 0) : Function.Injective P := by
  have h := mulVecLin_inj (LinearMap.toMatrix' P) (by rwa [LinearMap.det_toMatrix'])
  rwa [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix'] at h

theorem index_det (ϖ : R) (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n]
    (u : Matrix n n R) (hu : u.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det := by
  set L := u.mulVecLin with hL
  have hinj : Function.Injective L := mulVecLin_inj u hu
  have h : Module.finrank R (LinearMap.range L) = Module.finrank R (n → R) :=
    LinearMap.finrank_range_of_inj hinj
  let b := Pi.basisFun R n
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range L) b h).length_eq,
    Module.length_pi_of_fintype]
  rw [Finset.sum_congr rfl (fun i _ => lenQuotSpan ϖ hϖ _ (Submodule.smithNormalFormCoeffs_ne_zero b h i)),
    ← Finset.emultiplicity_prod hϖ.prime]
  set a := Submodule.smithNormalFormCoeffs b h
  set b' := Submodule.smithNormalFormTopBasis b h
  set ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : n → R) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  let P : (n → R) →ₗ[R] (n → R) := b'.constr R (fun i => (ab i : n → R))
  have hPb : ∀ i, P (b' i) = a i • b' i := by
    intro i; simp only [P, Basis.constr_basis, hab]
  have hdetP : LinearMap.det P = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' P = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hPb, map_smul, b'.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.det_diagonal]
  have hPinj : Function.Injective P := endo_inj P (by
    rw [hdetP]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i))
  have hPL : ∀ x, P x ∈ LinearMap.range L := by
    intro x

    rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [map_smul, hPb, ← hab]
    exact Submodule.smul_mem _ _ (ab i).2
  have hLP : ∀ x, L x ∈ LinearMap.range P := by
    intro x
    let y : LinearMap.range L := ⟨L x, LinearMap.mem_range_self L x⟩
    refine ⟨∑ i, ab.repr y i • b' i, ?_⟩
    have e2 := congrArg Subtype.val (ab.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2

    rw [map_sum]
    calc ∑ i, P (ab.repr y i • b' i) = ∑ i, ab.repr y i • (ab i : n → R) :=
          Finset.sum_congr rfl (fun i _ => by rw [map_smul, hPb, hab])
      _ = L x := e2
  let g : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective P hPinj).symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range P) hLP
  let g' : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective L hinj).symm.toLinearMap ∘ₗ P.codRestrict (LinearMap.range L) hPL
  have hg : P ∘ₗ g = L := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective P hPinj).apply_symm_apply
      (L.codRestrict (LinearMap.range P) hLP x))
  have hg' : L ∘ₗ g' = P := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective L hinj).apply_symm_apply
      (P.codRestrict (LinearMap.range L) hPL x))
  have hdetL : LinearMap.det L = u.det := by
    rw [hL, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  have d1 : LinearMap.det P ∣ u.det := ⟨LinearMap.det g, by rw [← hdetL, ← hg, LinearMap.det_comp]⟩
  have d2 : u.det ∣ LinearMap.det P := ⟨LinearMap.det g', by rw [← hdetL, ← hg', LinearMap.det_comp]⟩
  rw [← hdetP]
  exact emultiplicity_eq_of_associated_right (associated_of_dvd_dvd d1 d2)

end IdxDet

section Count

variable {F : Type} [Field F] [Fintype F]

end Count

end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
end
