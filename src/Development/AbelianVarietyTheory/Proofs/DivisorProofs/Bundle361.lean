module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModule
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.GenFibLift

open GlobalTheory.LocAcyc

theorem genFibMap_comp {T E F O : Type} [CommRing T] [CommRing E] [CommRing F] [CommRing O]
    [Algebra T E] [Algebra T F] [Algebra T O] (φ : E →ₐ[T] F) (ψ : F →ₐ[T] O) :
    genFibMap (ψ.comp φ) = (genFibMap ψ).comp (genFibMap φ) :=
  genFib_ringHom_ext (fun e => by
    simp only [RingHom.comp_apply, genFibMap_algebraMap, AlgHom.comp_apply])

def den {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    Algebra.algebraMapSubmonoid O (nonZeroDivisors T) :=
  ⟨algebraMap T O t, Submonoid.mem_map_of_mem _ t.2⟩

theorem exists_mk' {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (x : GenFib T O) :
    ∃ (a : O) (t : nonZeroDivisors T), x = IsLocalization.mk' (GenFib T O) a (den t) := by
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
  obtain ⟨t, ht, hm⟩ := Submonoid.mem_map.1 m.2
  refine ⟨a, ⟨t, ht⟩, ?_⟩
  rw [show m = den ⟨t, ht⟩ from Subtype.ext hm.symm]

theorem exists_of_mk'_eq_zero {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (a : O)
    (m : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (h : IsLocalization.mk' (GenFib T O) a m = 0) :
    ∃ t : nonZeroDivisors T, algebraMap T O t * a = 0 := by
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff a m).1 h
  obtain ⟨t, ht, hct⟩ := Submonoid.mem_map.1 c.2
  exact ⟨⟨t, ht⟩, by simpa [hct] using hc⟩

theorem genFibMap_mk' {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) (t : nonZeroDivisors T) :
    genFibMap ψ (IsLocalization.mk' (GenFib T E) e (den t)) =
      IsLocalization.mk' (GenFib T O) (ψ e) (den t) := by
  simp only [genFibMap, IsLocalization.map_mk']
  congr 1
  ext
  exact ψ.commutes t

theorem exists_finitePresentation_lift (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O]
    (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GenFib T O) :
    ∃ (Z : Type) (_ : CommRing Z) (_ : Algebra R Z) (_ : Algebra T Z) (_ : IsScalarTower T R Z)
      (_ : Algebra.FinitePresentation R Z) (g : Z →ₐ[R] O) (w : U →+* GenFib T Z),
      (genFibMap (g.restrictScalars T)).comp w = u := by
  haveI : Algebra.FinitePresentation ℤ U := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, f, hf, s, hs⟩ := Algebra.FinitePresentation.out (R := ℤ) (A := U)

  choose a t ht using fun i : Fin n => exists_mk' (T := T) (u (f (MvPolynomial.X i)))
  let e : MvPolynomial (Fin n) R →ₐ[R] O := MvPolynomial.aeval a
  let θ : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun i => IsLocalization.mk' _ (MvPolynomial.X i : MvPolynomial (Fin n) R) (den (t i)))
  have key : (genFibMap (e.restrictScalars T)).comp θ = u.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int
        (((genFibMap (e.restrictScalars T)).comp θ).comp MvPolynomial.C)
        ((u.comp f.toRingHom).comp MvPolynomial.C)) r
    · intro i
      simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', genFibMap_mk']
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ht i]
      simp [e]

  have hrel : ∀ r : s, ∃ (p : MvPolynomial (Fin n) R) (τ τ' : nonZeroDivisors T),
      θ r = IsLocalization.mk' _ p (den τ) ∧ e (algebraMap T _ τ' * p) = 0 := by
    intro r
    obtain ⟨p, τ, hp⟩ := exists_mk' (T := T) (θ r)
    have h0 : genFibMap (e.restrictScalars T) (θ r) = 0 := by
      have hr : (r : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span r.2
      rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.mem_ker.1 hr, map_zero]
    rw [hp, genFibMap_mk'] at h0
    obtain ⟨τ', hτ'⟩ := exists_of_mk'_eq_zero _ _ h0
    refine ⟨p, τ, τ', hp, ?_⟩
    rw [map_mul, ← hτ']
    simp [IsScalarTower.algebraMap_apply T R (MvPolynomial (Fin n) R),
      IsScalarTower.algebraMap_apply T R O]
  choose p τ τ' hθ he using hrel
  let I : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range fun r : s => algebraMap T _ (τ' r : T) * p r)
  have hIe : ∀ x ∈ I, e x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker e := Ideal.span_le.2 (by rintro _ ⟨r, rfl⟩; exact he r)
    exact hle hx
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R) :=
    Algebra.FinitePresentation.mvPolynomial R R (Fin n)
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  let g : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] O := Ideal.Quotient.liftₐ I e hIe
  let q : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) := Ideal.Quotient.mkₐ R I
  let w0 : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R ⧸ I) :=
    (genFibMap (q.restrictScalars T)).comp θ
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker w0 := by
    rw [← hs, Ideal.span_le]
    intro r hr
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [w0, RingHom.comp_apply]
    rw [hθ ⟨r, hr⟩, genFibMap_mk']
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) R ⧸ I) (GenFib T (MvPolynomial (Fin n) R ⧸ I))
        (algebraMap T _ (τ' ⟨r, hr⟩ : T))) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)) _ (den _)
    refine (hu.mul_right_eq_zero).1 ?_
    rw [← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)),
      ← IsLocalization.mk'_mul, one_mul]
    have hz : (q.restrictScalars T) (algebraMap T _ (τ' ⟨r, hr⟩ : T) * p ⟨r, hr⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    rw [map_mul, AlgHom.commutes] at hz
    rw [hz, IsLocalization.mk'_zero]

  refine ⟨MvPolynomial (Fin n) R ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g, RingHom.liftOfSurjective f.toRingHom hf ⟨w0, hker⟩, ?_⟩
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  have hy : f y = f.toRingHom y := rfl
  rw [RingHom.comp_apply, hy, RingHom.liftOfSurjective_comp_apply]
  have hgq : (g.restrictScalars T).comp (q.restrictScalars T) = e.restrictScalars T := by
    exact AlgHom.ext fun x => AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I e hIe) x
  have hcomp : (genFibMap (g.restrictScalars T)).comp w0 = u.comp f.toRingHom := by
    simp only [w0]
    rw [← RingHom.comp_assoc, ← genFibMap_comp, hgq, key]
  exact RingHom.congr_fun hcomp y

theorem exists_etale_genFib_lift : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  intro T R O _ _ _ _ _ _ _ H U _ _ u
  obtain ⟨Z, _, _, _, _, _, g, w, hw⟩ := exists_finitePresentation_lift T R O U u
  obtain ⟨W, _, _, _, u0, v, hv⟩ := H Z g
  letI : Algebra T W := ((algebraMap R W).comp (algebraMap T R)).toAlgebra
  haveI hTRW : IsScalarTower T R W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, hTRW, inferInstance, v,
    (genFibMap (u0.restrictScalars T)).comp w, ?_⟩
  rw [← RingHom.comp_assoc, ← genFibMap_comp]
  have hvu : (v.restrictScalars T).comp (u0.restrictScalars T) = g.restrictScalars T :=
    AlgHom.ext fun z => AlgHom.congr_fun hv z
  rw [hvu, hw]

end GlobalTheory.GenFibLift
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosureHartogs

theorem closure_hart : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ hHR hinj D _ _ τ hτC a₀ ha₀ n x y hy hid
  set F := GlobalTheory.LocAcyc.GenFib A R
  set C := GlobalTheory.KeyOriginNoeth.closure A R D
  letI : Algebra R D := (GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  have hbase : ∀ r : R, GlobalTheory.KeyOriginNoeth.baseHom A R D r = algebraMap F D (algebraMap R F r) :=
    fun r => rfl
  have hmemC : ∀ z : D, z ∈ C ↔ IsIntegral R z := fun z => Iff.rfl
  have hsmulC : ∀ (r : R) (c : C), ((r • c : C) : D) = GlobalTheory.KeyOriginNoeth.baseHom A R D r * c :=
    fun r c => rfl
  have hτm : ∀ (f : F) (w : D), τ (algebraMap F D f * w) = f * τ w := by
    intro f w; rw [← Algebra.smul_def, τ.map_smul, smul_eq_mul]

  have hunit : ∀ a : A, a ≠ 0 → IsUnit (algebraMap R F (algebraMap A R a)) := by
    intro a ha
    exact IsLocalization.map_units F
      (⟨algebraMap A R a, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ :
        nonZeroDivisors A)⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))

  let N : Submodule R D :=
    { carrier := {d | ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z)}
      add_mem' := by
        intro d₁ d₂ h₁ h₂ z hz
        obtain ⟨r₁, e₁⟩ := h₁ z hz
        obtain ⟨r₂, e₂⟩ := h₂ z hz
        exact ⟨r₁ + r₂, by rw [map_add (f := _), e₁, e₂, add_mul, map_add (f := _)]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro r d h z hz
        obtain ⟨r₁, e₁⟩ := h z hz
        refine ⟨r * r₁, ?_⟩
        rw [Algebra.smul_def, mul_assoc]
        change _ = τ (algebraMap F D (algebraMap R F r) * (d * z))
        rw [hτm, ← e₁, map_mul] }
  have hmemN : ∀ d, d ∈ N ↔ ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z) := fun d => Iff.rfl
  have h1N : (1 : D) ∈ N := by
    intro z hz
    simpa using hτC z hz

  obtain ⟨c₀, hc₀⟩ := hunit a₀ ha₀
  let S : Submodule R D := Submodule.span R (Set.range fun i => algebraMap F D (↑c₀⁻¹ : F) * x i)
  have hNS : N ≤ S := by
    intro d hd
    have hr : ∀ i, ∃ r : R, algebraMap R F r = τ (y i * d) := by
      intro i
      obtain ⟨r, e⟩ := hd (y i) (hy i)
      exact ⟨r, by rw [e, mul_comm]⟩
    choose r hr using hr
    have hd' : d = ∑ i, r i • (algebraMap F D (↑c₀⁻¹ : F) * x i) := by
      have h := hid d
      have h2 : d = algebraMap F D (↑c₀⁻¹ : F) *
          (GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) := by
        rw [hbase, ← mul_assoc, ← map_mul, ← hc₀, Units.inv_mul, map_one, one_mul]
      rw [h2, ← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hr i]
      change _ = algebraMap F D (algebraMap R F (r i)) * _
      ring
    rw [hd']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSnoeth : IsNoetherian R S :=
    isNoetherian_of_fg_of_noetherian S (Submodule.fg_span (Set.finite_range _))

  intro a ha m hm
  obtain ⟨c, hc⟩ := hunit a ha
  set ξ : D := algebraMap F D (↑c⁻¹ : F) * (m : D) with hξ

  have hξN : ∀ d ∈ N, ξ * d ∈ N := by
    intro d hd z hz
    have hmz : (m : D) * z ∈ C := C.mul_mem m.2 hz
    obtain ⟨r₀, e₀⟩ := hd _ hmz
    have hdiv : ∃ r'' : R, r₀ = algebraMap A R a • r'' := by
      apply hHR a ha r₀
      intro p hp hph
      obtain ⟨u, hu, m', hm'⟩ := hm p hp hph
      have hm'z : (m' : D) * z ∈ C := C.mul_mem m'.2 hz
      obtain ⟨r', e'⟩ := hd _ hm'z
      refine ⟨u, hu, r', ?_⟩
      apply hinj
      have hv := congrArg Subtype.val hm'
      rw [hsmulC, hsmulC, hbase, hbase] at hv
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, e₀, e', ← hτm, ← hτm]
      congr 1
      linear_combination (d * z) * hv
    obtain ⟨r'', e''⟩ := hdiv
    refine ⟨r'', ?_⟩
    have : ξ * d * z = algebraMap F D (↑c⁻¹ : F) * (d * ((m : D) * z)) := by
      rw [hξ]; ring
    rw [this, hτm, ← e₀, e'', smul_eq_mul, map_mul, ← hc, ← mul_assoc, Units.inv_mul, one_mul]
  have hpow : ∀ k : ℕ, ξ ^ k ∈ N := by
    intro k
    induction k with
    | zero => simpa using h1N
    | succ k ih => rw [pow_succ']; exact hξN _ ih
  have hadj : Subalgebra.toSubmodule (Algebra.adjoin R {ξ}) ≤ S := by
    rw [Algebra.adjoin_eq_span]
    refine le_trans ?_ hNS
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hw
    exact hpow k
  have hfg : (Subalgebra.toSubmodule (Algebra.adjoin R {ξ})).FG :=
    isNoetherian_submodule.mp hSnoeth _ hadj
  have hξC : ξ ∈ C :=
    (hmemC ξ).mpr (IsIntegral.of_mem_of_fg _ hfg ξ (Algebra.self_mem_adjoin_singleton R ξ))
  refine ⟨⟨ξ, hξC⟩, Subtype.ext ?_⟩
  rw [hsmulC, hbase]
  change (m : D) = algebraMap F D (algebraMap R F (algebraMap A R a)) * ξ
  rw [hξ, ← mul_assoc, ← map_mul, ← hc, Units.mul_inv, map_one, one_mul]

end GlobalTheory.ClosureHartogs
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale :
    ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : _root_.GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (_root_.GlobalTheory.LocAcyc.GenFib A R) D → _root_.GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  intro A R O B _ _ _ _ _ _ _ _ _ _ j β ψ hψ D _ _ hfin hE
  letI : Algebra R D := (_root_.GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI : Algebra R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) :=
    _root_.GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨hEfin, hEet, hEnt⟩ := hE
  haveI := hEfin
  haveI := hEet
  haveI := hEnt
  haveI := hfin
  letI : Algebra R O := j.toAlgebra
  haveI : Module.Free R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) := Module.free_of_flat_of_isLocalRing
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := _root_.GlobalTheory.KeyOriginNoeth.closure A R D)
    ⟨RingHom.ker (algebraMap R (ResidueField O)), RingHom.ker_isPrime _⟩
  have hq' : Ideal.comap (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)) q.asIdeal =
      RingHom.ker (algebraMap R (ResidueField O)) := congrArg PrimeSpectrum.asIdeal hq
  obtain ⟨φ₀⟩ := _root_.GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed q.asIdeal hq'
  obtain ⟨φ, -⟩ := (_root_.GlobalTheory.EtaleHensel.bijective_residue_comp R
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) O).2 φ₀
  letI : Algebra (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  haveI : IsScalarTower R (_root_.GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalization ((Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D))) D := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map
        (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D)
    · intro d
      obtain ⟨⟨m, hm⟩, hmint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) d
        (Algebra.IsIntegral.isIntegral (R := _root_.GlobalTheory.LocAcyc.GenFib A R) d)
      refine ⟨⟨⟨m • d, hmint⟩, ⟨algebraMap R _ m, m, hm, rfl⟩⟩, ?_⟩
      show d * algebraMap R D m = m • d
      rw [Algebra.smul_def, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  have hσ : ∀ r : R, β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r)) =
      ψ (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R) r) := by
    intro r
    rw [φ.commutes]
    exact (RingHom.congr_fun hψ r).symm
  have hunits : ∀ y : (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)), IsUnit ((β.comp φ.toRingHom) y) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    show IsUnit (β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) s)))
    rw [hσ]
    exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map ψ
  refine ⟨IsLocalization.lift (S := D) hunits, ?_⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  ext r
  have hr : algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D (algebraMap R _ r) =
      algebraMap (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D
        (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r) := rfl
  simp only [RingHom.comp_apply]
  rw [hr, IsLocalization.lift_eq]
  exact hσ r

end GlobalTheory.KeyOriginNoeth
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem finite_closure (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D] :
    (letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
     Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D)) := by
  letI iRD : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  haveI : Module.Flat R (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.flat _ M
  haveI : Module.Flat R D := Module.Flat.trans R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization M
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.EssFiniteType R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.EssFiniteType.of_isLocalization _ M
  haveI : Algebra.EssFiniteType R D := Algebra.EssFiniteType.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  have h1 : Module.Finite R (integralClosure R (R ⊗[R] D)) :=
    GlobalTheory.RootFibre.finite_integralClosure R D R
  have e := AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.lid R D)
  have h2 : Module.Finite R (integralClosure R D) := Module.Finite.equiv e.toLinearEquiv
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let f : integralClosure R D ≃ₗ[R] GlobalTheory.KeyOriginNoeth.closure A R D :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        show r • x.1 = (baseHom A R D r) * x.1
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv f

end GlobalTheory.KeyOriginNoeth
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ := by
  first | exact @GlobalTheory.FinWeil.span_translates_vacua | exact GlobalTheory.FinWeil.span_translates_vacua | (intros; apply GlobalTheory.FinWeil.span_translates_vacua <;> assumption)
end

section

open GlobalTheory.FinWeil

theorem _root_.GlobalTheory.T.gaussSum_nondegenerate_finite_hermitian_module : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  first | exact @GlobalTheory.HermitianGauss.gauss_hermitian | exact GlobalTheory.HermitianGauss.gauss_hermitian | (intros; apply GlobalTheory.HermitianGauss.gauss_hermitian <;> assumption)
end

section

open GlobalTheory

theorem _root_.GlobalTheory.T.aeval_surjective_of_cotangent_span_top : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first | exact @GlobalTheory.NakAug.surj | exact GlobalTheory.NakAug.surj | (intros; apply GlobalTheory.NakAug.surj <;> assumption)
end
