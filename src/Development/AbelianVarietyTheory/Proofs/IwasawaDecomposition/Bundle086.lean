module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleFinrankOne.IrrOfFinrankOne
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle079
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle078
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
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PrincipalCompletion

variable {R : Type} [CommRing R] (a : R)

theorem fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton a

theorem eval_eq_zero_iff (n : ℕ) (x : AdicCompletion (Ideal.span {a}) R) :
    AdicCompletion.eval (Ideal.span {a}) R n x = 0 ↔
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ n ∣ x := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (fg a),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
      (AdicCompletion (Ideal.span {a}) R) := by
  have h := AdicCompletion.isAdicComplete (M := R) (fg a)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {a}) R),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (x : AdicCompletion (Ideal.span {a}) R) (r : ℕ) :
    ∃ (s : R) (z : AdicCompletion (Ideal.span {a}) R),
      x = algebraMap R _ s + (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {a}) R r x)
  have : AdicCompletion.eval (Ideal.span {a}) R r (x - algebraMap R _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff a r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : R) (r : ℕ) :
    (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r ∣ algebraMap R _ s ↔ a ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {a}) R r (algebraMap R _ s) = Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem torsionFree (ha : ∀ s : R, a * s = 0 → s = 0) (x : AdicCompletion (Ideal.span {a}) R)
    (hx : algebraMap R (AdicCompletion (Ideal.span {a}) R) a * x = 0) : x = 0 := by
  refine AdicCompletion.ext fun n => ?_
  change AdicCompletion.eval (Ideal.span {a}) R n x = 0
  rw [eval_eq_zero_iff]
  obtain ⟨s, z, rfl⟩ := dense a x n
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [dvd_iff]
  have h1 : (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ (n + 1) ∣
      algebraMap R _ (a * s) := ⟨-z, by rw [map_mul]; linear_combination hx⟩
  obtain ⟨t, ht⟩ := (dvd_iff a _ _).1 h1
  exact ⟨t, sub_eq_zero.1 (ha _ (by linear_combination ht))⟩

theorem basic_of_equiv_pt (p : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (hp : ∀ s : R, (p : R) * s = 0 → s = 0)
    (e : A ≃+* AdicCompletion (Ideal.span {(p : R)}) R)
    (he : ∀ s, e (algebraMap R A s) = algebraMap R _ s) :
    IsAdicComplete (Ideal.span {(p : A)}) A ∧
    (∀ x : A, (p : A) * x = 0 → x = 0) ∧
    (∀ (x : A) (r : ℕ), ∃ (s : R) (z : A), x = algebraMap R A s + (p : A) ^ r * z) ∧
    ∀ (s : R) (r : ℕ), (p : A) ^ r ∣ algebraMap R A s ↔ (p : R) ^ r ∣ s := by
  have hpe : e (p : A) = algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) (p : R) := by
    rw [map_natCast, map_natCast]
  refine ⟨?_, fun x hx => ?_, fun x r => ?_, fun s r => ?_⟩
  · have h := complete (p : R)
    rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton, hpe]
    exact h
  · apply e.injective
    rw [map_zero]
    apply torsionFree _ hp
    rw [← hpe, ← map_mul, hx, map_zero]
  · obtain ⟨s, z, hz⟩ := dense (p : R) (e x) r
    refine ⟨s, e.symm z, e.injective ?_⟩
    rw [map_add (f := _), map_mul, map_pow, he, hpe, RingEquiv.apply_symm_apply]
    exact hz
  · rw [← dvd_iff (p : R) s r, ← hpe, ← he, ← map_pow, map_dvd_iff]

end GlobalTheory.PrincipalCompletion

namespace GlobalTheory.MemLoc

theorem acris0_torsionFree (l : ℕ) [Fact l.Prime] (s : Per.Acris0 l)
    (hs : (l : Per.Acris0 l) * s = 0) : s = 0 := by
  have hu : IsUnit (l : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) (l : Per.Ainf l)
    rwa [map_natCast] at this
  have h : (l : Per.AinfP l) * (s : Per.AinfP l) = 0 := by
    simpa using congrArg Subtype.val hs
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h)

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ (∀ (x : Per.Acris l) (r : ℕ), ∃ (s : Per.Acris0 l) (z : Per.Acris l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z) ∧ ∀ (s : Per.Acris0 l) (r : ℕ), (l : Per.Acris l) ^ r ∣ algebraMap (Per.Acris0 l) (Per.Acris l) s ↔ (l : Per.Acris0 l) ^ r ∣ s :=
  fun l _ => by
    obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
    exact GlobalTheory.PrincipalCompletion.basic_of_equiv_pt l (Per.Acris0 l) (Per.Acris l)
      (acris0_torsionFree l) e he

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogAdd

open Polynomial

theorem one_add_mul_derivative_trunc {R : Type} [CommRing R] (n : ℕ) (u : R[X]) (hu : u ^ n = 0) :
    (1 + u) * derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (n.factorial : R[X]) * derivative u := by
  have h1 : derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-u) ^ k) * ((n.factorial : R[X]) * derivative u) := by
    rw [derivative_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hd : (k + 1) ∣ n.factorial :=
      Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
    have hc : ((n.factorial / (k + 1) : ℕ) : R[X]) * ((k : R[X]) + 1) = (n.factorial : R[X]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → R[X]) (Nat.div_mul_cancel hd)
    have hs : derivative ((-1 : R[X]) ^ k) = 0 := by
      rcases neg_one_pow_eq_or R[X] k with h | h <;> simp [h]
    rw [derivative_mul, derivative_mul, hs, derivative_natCast, derivative_pow_succ, ← hc, neg_pow u]
    simp only [map_add (f := _), map_natCast, map_one]
    ring
  have h2 : (1 + u) * ∑ k ∈ Finset.range n, (-u) ^ k = 1 := by
    have := mul_neg_geom_sum (-u) n
    rw [sub_neg_eq_add, neg_pow u, hu, mul_zero, sub_zero] at this
    exact this
  rw [h1, ← mul_assoc, h2, one_mul]

theorem trunc_add {R : Type} [CommRing R] (hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R)) (n : ℕ)
    (I : Ideal R) (hI : I ^ n = ⊥) (a b : R) (ha : a ∈ I) (hb : b ∈ I) :
    (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * (a + b + a * b) ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * a ^ (k + 1)) +
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * b ^ (k + 1)) := by
  let F : R[X] → R[X] := fun u => ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)
  let J : Ideal R[X] := I.map (C : R →+* R[X])
  have hJ : ∀ u ∈ J, u ^ n = 0 := by
    intro u hu
    have := Ideal.pow_mem_pow hu n
    rwa [← Ideal.map_pow, hI, Ideal.map_bot, Ideal.mem_bot] at this
  set s : R[X] := C a * X with hs
  set t : R[X] := C b * X with ht
  have hsJ : s ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ ha)
  have htJ : t ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ hb)
  have huJ : s + t + s * t ∈ J := J.add_mem (J.add_mem hsJ htJ) (J.mul_mem_right _ hsJ)
  have e1 : (1 + s) * derivative (F s) = _ := one_add_mul_derivative_trunc n s (hJ _ hsJ)
  have e2 : (1 + t) * derivative (F t) = _ := one_add_mul_derivative_trunc n t (hJ _ htJ)
  have e3 : (1 + (s + t + s * t)) * derivative (F (s + t + s * t)) = _ :=
    one_add_mul_derivative_trunc n _ (hJ _ huJ)
  have hunit : IsUnit (1 + (s + t + s * t)) := IsNilpotent.isUnit_one_add ⟨n, hJ _ huJ⟩
  have hD : derivative (F (s + t + s * t) - F s - F t) = 0 := by
    apply hunit.mul_left_cancel
    rw [derivative_add, derivative_add, derivative_mul (f := s) (g := t)] at e3
    rw [derivative_sub, derivative_sub]
    linear_combination e3 - (1 + t) * e1 - (1 + s) * e2
  have hC : F (s + t + s * t) - F s - F t = C ((F (s + t + s * t) - F s - F t).coeff 0) := by
    ext k
    cases k with
    | zero => simp only [coeff_C_zero]
    | succ k =>
      have h := congrArg (fun (p : R[X]) => p.coeff k) hD
      simp only [coeff_derivative, coeff_zero] at h
      rw [coeff_C_succ]
      have hu : IsUnit ((k : R) + 1) := by exact_mod_cast hR (k + 1) (Nat.succ_ne_zero k)
      exact (hu.mul_left_eq_zero).1 h
  have h0 : (F (s + t + s * t) - F s - F t).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [F, hs, ht, eval_finsetSum]
  rw [h0, map_zero] at hC
  have h1 := congrArg (eval 1) hC
  simp only [F, hs, ht, eval_sub, eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
    eval_natCast, eval_add, eval_C, eval_X, mul_one, eval_zero] at h1
  linear_combination h1

theorem tm_sub_one_mem (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  apply GlobalTheory.RingIface.alg_mem_kerP
  simp [he]

theorem map_mul_sub_one {M A B : Type} [Monoid M] [CommRing A] [CommRing B] (g : M →* A)
    (f : A →+* B) (e e' : M) :
    f (g (e * e') - 1) = f (g e - 1) + f (g e' - 1) + f (g e - 1) * f (g e' - 1) := by
  simp only [map_sub, map_mul, map_one]
  ring

theorem tm_mul_sub_one (l : ℕ) [Fact l.Prime] (e e' : Per.Fl l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm (e * e') - 1) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) *
          algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) :=
  map_mul_sub_one (WittVector.teichmuller l) _ e e'

theorem log_add : ∀ (l : ℕ) [Fact l.Prime], ∀ (e e' : Per.Fl l) (y y' z : Per.BdRp l),
    e.untilt = 1 → e'.untilt = 1 → Per.IsLog l e y → Per.IsLog l e' y' →
      Per.IsLog l (e * e') z → z = y + y' := by
  intro l _ e e' y y' z he he' hy hy' hz
  refine GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_
  let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n) := fun m hm => by
    have := (GlobalTheory.RingBasics.isUnit_nat l m hm).map q
    rwa [map_natCast] at this
  apply (hR _ n.factorial_ne_zero).mul_left_cancel
  rw [map_add (f := _), mul_add, GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy n,
    GlobalTheory.CrisIncl.factorial_mul_ev l e' y' he' hy' n,
    GlobalTheory.CrisIncl.factorial_mul_ev l _ z (by rw [map_mul, he, he', mul_one]) hz n]
  have hI : ((Per.kerP l).map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have key := trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q (tm_sub_one_mem l e he))
    (Ideal.mem_map_of_mem q (tm_sub_one_mem l e' he'))
  rw [tm_mul_sub_one]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = a at key ⊢
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) = b at key ⊢
  change q _ = q _ + q _

  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add (f := _)]
  exact key

end GlobalTheory.MemLoc.LogAdd
end

section

open Formalism.L2.DIV

open Module

namespace GlobalTheory

theorem classFun_char_scalar {G : Type} [Group G] [Fintype G] (e : MonoidAlgebra ℂ G)
    (he : ∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) (ψ : G → ℂ)
    (hψ : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) (x : G) :
    ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  classical
  have hψ' := hψ
  obtain ⟨n, ρ, hρ, rfl⟩ := hψ
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := ℂ) hψ' hψ'
  rw [if_pos rfl] at horth
  rw [horth] at h1
  have hfr : finrank ℂ (ρ.IntertwiningMap ρ) = 1 := by exact_mod_cast h1.symm
  have hnt : Nontrivial (Fin n → ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := hρ.exists_pair_ne
    apply hab
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  let idI : ρ.IntertwiningMap ρ := ⟨LinearMap.id, fun g => by rw [LinearMap.id_comp, LinearMap.comp_id]⟩
  have hid0 : idI ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    intro h
    have := congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) h
    exact hv this
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := ∑ g : G, e.coeff g • ρ g
  have hTI : ∀ h, T ∘ₗ ρ h = ρ h ∘ₗ T := by
    intro h
    show T * ρ h = ρ h * T
    simp only [T, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← map_mul]
    refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    rw [show h⁻¹ * g * h = h⁻¹ * g * h⁻¹⁻¹ by rw [inv_inv], he]
    congr 2
    group
  let TI : ρ.IntertwiningMap ρ := ⟨T, hTI⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' idI hid0).mp hfr TI
  have hT : T = c • LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) hc
    simpa [idI, TI] using this.symm
  have htr : ∀ y : G, ∑ g, e.coeff g * ρ.character (g * y) = c * ρ.character y := by
    intro y
    have h2 : T * ρ y = c • ρ y := by rw [hT, smul_mul_assoc]; exact congrArg _ (LinearMap.id_comp _)
    have h3 := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) h2

    simp only [T, Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, smul_eq_mul] at h3
    simpa only [Representation.character] using h3
  have hx := htr x
  have h1' := htr 1
  simp only [mul_one] at h1'
  rw [hx, h1']
  ring

end GlobalTheory
end

section

open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory

theorem absIrrChar_comp_mem_gxIrrSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K]
    [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ →
    (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  intro G _ _ K _ _ σ χ h
  classical
  obtain ⟨⟨n, ρc, htr⟩, hip⟩ := PI.XgCTieBrWork.Chars.absIrr_isIrr σ h
  have htr' : ∀ x, σ (χ x) = Matrix.trace ((ρc x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := htr
  have hchar : ∀ x, (PI.XgCTieBrWork.Chars.ofGL ρc).character x = σ (χ x) := fun x => by
    rw [PI.XgCTieBrWork.Chars.char_ofGL, htr']
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have hfr := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (PI.XgCTieBrWork.Chars.ofGL ρc) (PI.XgCTieBrWork.Chars.ofGL ρc)
  have hsum : ∑ g : G, (PI.XgCTieBrWork.Chars.ofGL ρc).character g *
      (PI.XgCTieBrWork.Chars.ofGL ρc).character g⁻¹ = (Nat.card G : ℂ) := by
    simp_rw [hchar]
    rw [Nat.card_eq_fintype_card, ← hip]
    unfold Formalism.L2.NT.ipG
    refine Finset.sum_congr rfl fun x _ => ?_
    show σ (χ x) * σ (χ x⁻¹) = σ (χ x) * star (σ (χ x))
    rw [htr' x, htr' x⁻¹, PI.XgCTieBrWork.Chars.star_trace_inv]
  rw [hsum, inv_mul_cancel₀ (NeZero.ne _)] at hfr
  have h1 : Module.finrank ℂ (Representation.IntertwiningMap (PI.XgCTieBrWork.Chars.ofGL ρc)
      (PI.XgCTieBrWork.Chars.ofGL ρc)) = 1 := by
    exact_mod_cast hfr.symm
  exact ⟨n, PI.XgCTieBrWork.Chars.ofGL ρc, PI.XgCTieBrWork.Chars.irr_of_finrank_one _ h1, funext hchar⟩

end GlobalTheory
end
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.centralIdempotent_eq_sum_character_idempotents : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)) (e : MonoidAlgebra ℂ G), (∀ ψ ∈ A, ψ 1 ≠ 0) → (∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0) → (∀ ψ ∈ A, ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x) → e * e = e → e = idemOf (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) := by
  first | exact @GlobalTheory.IdemExpand.eq_idemOf_filter | exact GlobalTheory.IdemExpand.eq_idemOf_filter | (intros; apply GlobalTheory.IdemExpand.eq_idemOf_filter <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop) (π c : 𝓞 E) (T : ℕ),
    (T : 𝓞 F) ∉ v.asIdeal → π * c = (T : 𝓞 E) →
    (∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) → ∀ (y : Fin n → E ⊗[F] v.adicCompletion F),
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  first | exact @GlobalTheory.locL_eq_intV_of_dvd_unit | exact GlobalTheory.locL_eq_intV_of_dvd_unit | (intros; apply GlobalTheory.locL_eq_intV_of_dvd_unit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

theorem _root_.GlobalTheory.T.stepLevel_localGroup_eq_of_agree_off_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))), (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  first | exact @GlobalTheory.stepLevel_uloc_eq_of_agree | exact GlobalTheory.stepLevel_uloc_eq_of_agree | (intros; apply GlobalTheory.stepLevel_uloc_eq_of_agree <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  first | exact @GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding | exact GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding | (intros; apply GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.selfDual_sqrt_smul_comp_of_invariant : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  first | exact @GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint | exact GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint | (intros; apply GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.adic_completion_reduced_of_jacobson : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D] (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  first | exact @GlobalTheory.CompletionReduced.isReduced_adicCompletion | exact GlobalTheory.CompletionReduced.isReduced_adicCompletion | (intros; apply GlobalTheory.CompletionReduced.isReduced_adicCompletion <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.linComb_pow_section_flatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))), ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.linComb_pow_pow_sec | exact GlobalTheory.linComb_pow_pow_sec | (intros; apply GlobalTheory.linComb_pow_pow_sec <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.linComb_pow_section_unflatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.SecPowUnflat.unflat | exact GlobalTheory.SecPowUnflat.unflat | (intros; apply GlobalTheory.SecPowUnflat.unflat <;> assumption)
end
