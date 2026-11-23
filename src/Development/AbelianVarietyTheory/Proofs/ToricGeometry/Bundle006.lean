module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle001
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Finiteness
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

namespace GlobalTheory.NoetherPrimitive

open Polynomial
open scoped nonZeroDivisors

theorem exists_map_eq_C_mul {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (f : K[X]) :
    ∃ s : R, s ≠ 0 ∧ ∃ g : R[X], g.map (algebraMap R K) = C (algebraMap R K s) * f := by
  obtain ⟨s, hs, h⟩ := IsLocalization.integerNormalization_spec R⁰ f
  refine ⟨s, nonZeroDivisors.ne_zero hs, IsLocalization.integerNormalization R⁰ f, ?_⟩
  rw [h, ← smul_eq_C_mul, algebraMap_smul]

theorem exists_C_mem_span {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X]) (hp : (p.map (algebraMap R K)).Separable) :
    ∃ q : R, q ≠ 0 ∧ C q ∈ Ideal.span {p, p.derivative} := by
  obtain ⟨u, v, huv⟩ := hp
  obtain ⟨s, hs, U, hU⟩ := exists_map_eq_C_mul (R := R) u
  obtain ⟨t, ht, V, hV⟩ := exists_map_eq_C_mul (R := R) v
  refine ⟨s * t, mul_ne_zero hs ht, Ideal.mem_span_pair.2 ⟨C t * U, C s * V, ?_⟩⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [derivative_map] at huv
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, map_C, hU, hV, map_mul]
  linear_combination (C (algebraMap R K s) * C (algebraMap R K t)) * huv

theorem exists_common_denominator {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : R[X], algebraMap R A s * b = aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : R[X], algebraMap R A s * b = aeval a r := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator ..)

theorem exists_primitive_element_discriminant_multiple (R A K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra A L]
    [IsFractionRing A L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A R⁰) L := inferInstance
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A R⁰
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨⟨a, ⟨_, t, ht, rfl⟩⟩, hat⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A R⁰) α
  have ht' : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.ne_zero ht)
  have hat' : α = algebraMap K L (algebraMap R K t)⁻¹ * algebraMap A L a := by
    simp only at hat
    rw [← hat, ← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R K L,
      mul_left_comm, ← map_mul, inv_mul_cancel₀ ht', map_one, mul_one]
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have htop : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]
  obtain ⟨q₁, hq₁, h₁⟩ := exists_common_denominator (R := R) a fun b => by
    have hb : algebraMap A L b ∈ Algebra.adjoin K {α} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨f, hf⟩ := hb
    obtain ⟨s, hs, g, hg⟩ := exists_map_eq_C_mul (R := R) (f.comp (C (algebraMap R K t)⁻¹ * X))
    refine ⟨s, hs, g, IsFractionRing.injective A L ?_⟩
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap K, hg, map_mul, map_mul, aeval_C,
      aeval_comp, map_mul, aeval_C, aeval_X, ← hat', ← hf, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨q₂, hq₂, h₂⟩ := exists_C_mem_span (K := K) (minpoly R a) (by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L hint]
    exact Algebra.IsSeparable.isSeparable K _)
  refine ⟨a, q₂ * q₁, mul_ne_zero hq₂ hq₁, ?_, fun b => ?_⟩
  · rw [C_mul]; exact Ideal.mul_mem_right _ _ h₂
  · obtain ⟨r, hr⟩ := h₁ b
    exact ⟨C q₂ * r, by rw [map_mul, map_mul, aeval_C, mul_assoc, hr]⟩

theorem exists_primitive (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  exact exists_primitive_element_discriminant_multiple R A (FractionRing R) (FractionRing A)

end GlobalTheory.NoetherPrimitive

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

theorem GlobalTheory.noetherNormalization_primitive :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) := by
  intro A _ _ _ _
  obtain ⟨d, j, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) A) := hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  obtain ⟨a, q, hq, hq₁, hq₂⟩ := GlobalTheory.NoetherPrimitive.exists_primitive (MvPolynomial (Fin d) ℂ) A
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) a := Algebra.IsIntegral.isIntegral a
  refine ⟨d, j, a, minpoly _ a, q, ?_, hinj, hfin, minpoly.monic hint, minpoly.irreducible hint,
    fun r => minpoly.isIntegrallyClosed_dvd_iff hint r, hq, hq₁, hq₂⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj',
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end

section

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem finite_of_isIntegral_of_birational_of_finite_over_normal
    (R A B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharZero R] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L := FractionRing B
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply A B L]; rfl
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]; exact hBL.comp hAB

  haveI : IsFractionRing A L := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro y
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero y.2))
    · intro z
      obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors B) z
      obtain ⟨a₁, c₁, hc₁, h₁⟩ := hb x
      obtain ⟨a₂, c₂, hc₂, h₂⟩ := hb (y : B)
      have hy : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
      have ha₂ : a₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h₂
        exact mul_ne_zero ((map_ne_zero_iff _ hAB).mpr hc₂) hy h₂
      refine ⟨⟨a₁ * c₂, ⟨c₁ * a₂, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc₁ ha₂)⟩⟩, ?_⟩
      simp only [IsScalarTower.algebraMap_apply A B L, map_mul, ← h₁, ← h₂]
      simp only [map_mul] at hz ⊢
      rw [← hz]; ring
    · intro x y hxy
      exact ⟨1, by rw [hAL hxy]⟩
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R A L]
    exact hAL.comp (FaithfulSMul.algebraMap_injective R A))
  let K := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.trans A
  let f : B →ₐ[R] integralClosure R L :=
    (IsScalarTower.toAlgHom R B L).codRestrict (integralClosure R L)
      (fun b => (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L))
  have hf : Function.Injective f.toLinearMap := fun x y h =>
    hBL (congrArg Subtype.val h)
  haveI : IsNoetherian R (integralClosure R L) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian R B := isNoetherian_of_injective f.toLinearMap hf
  haveI : Module.Finite R B := Module.IsNoetherian.finite R B
  exact Module.Finite.of_restrictScalars_finite R A B

theorem finite_of_isIntegral_of_birational_complex
    (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hg
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  exact finite_of_isIntegral_of_birational_of_finite_over_normal (MvPolynomial (Fin d) ℂ) A B hb

theorem finite_of_isIntegral_of_birational_of_presentation :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) := by
  intro _ A B _ _ _ _ _ _ _ _ _ hb
  exact finite_of_isIntegral_of_birational_complex A B hb

end GlobalTheory
end
