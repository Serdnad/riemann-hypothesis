module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle113
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle022
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Tactic.Monotonicity.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Mathlib.RingTheory.Etale.Kaehler
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V), IsLocalHom ψ → ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V, IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  first | exact @GlobalTheory.exists_isLocalHom_adicCompletion_extend | exact GlobalTheory.exists_isLocalHom_adicCompletion_extend | (intros; apply GlobalTheory.exists_isLocalHom_adicCompletion_extend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open KaehlerDifferential TensorProduct

theorem bijective_of_bijective_lTensor_residueField {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N] (l : M →ₗ[R] N)
    (h : Function.Bijective (l.lTensor (ResidueField R))) : Function.Bijective l := by
  have : Module.Free R N := Module.free_of_flat_of_isLocalRing
  refine ⟨?_, ?_⟩
  · obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).mpr h.1
    exact Function.HasLeftInverse.injective ⟨l', LinearMap.congr_fun hl'⟩
  · have hex := lTensor_exact (ResidueField R) (LinearMap.exact_map_mkQ_range l)
      (Submodule.mkQ_surjective _)
    have hsub : Subsingleton (ResidueField R ⊗[R] (N ⧸ LinearMap.range l)) := by
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (ResidueField R) (Submodule.mkQ_surjective _) y
      obtain ⟨z, rfl⟩ := h.2 x
      exact hex.apply_apply_eq_zero z
    rw [IsLocalRing.subsingleton_tensorProduct] at hsub
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp hsub

theorem formallyEtale_of_bijective_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P]
    [CommRing B] [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B]
    [Algebra.FormallySmooth R B] (h : Function.Bijective (mapBaseChange R P B)) :
    Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem bijective_lTensor_baseChange_of_bijective {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (Q : Ideal B) [Q.IsPrime]
    (φ : M →ₗ[B] N) (h : Function.Bijective (φ.lTensor Q.ResidueField)) :
    Function.Bijective ((φ.baseChange (Localization.AtPrime Q)).lTensor
      (ResidueField (Localization.AtPrime Q))) := by
  let BQ := Localization.AtPrime Q
  let k := ResidueField BQ
  let eM := AlgebraTensorModule.cancelBaseChange B BQ k k M
  let eN := AlgebraTensorModule.cancelBaseChange B BQ k k N
  have key : ∀ x, eN ((φ.baseChange BQ).lTensor k x) = φ.lTensor Q.ResidueField (eM x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add (f := _)] at hy hz ⊢; rw [hy, hz]
      | tmul q m => simp [eM, eN]
  have : ⇑((φ.baseChange BQ).lTensor k) = eN.symm ∘ (φ.lTensor Q.ResidueField) ∘ eM := by
    funext x; simp [← key]
  rw [this]
  exact eN.symm.bijective.comp (h.comp eM.bijective)

theorem kaehler_map_map_apply (A C B BQ : Type) [CommRing A] [CommRing C] [CommRing B] [CommRing BQ] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
   [Algebra B BQ] [Algebra A BQ] [Algebra C BQ] [IsScalarTower A B BQ] [IsScalarTower C B BQ] [IsScalarTower A C BQ] (ω : Ω[C⁄A]) :
    map A A B BQ (map A A C B ω) = map A A C BQ ω := by
  have : ((map A A B BQ).restrictScalars C).comp (map A A C B) = map A A C BQ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [map_D, ← IsScalarTower.algebraMap_apply]
  exact LinearMap.congr_fun this ω

theorem exists_etale_away_of_bijective_mapBaseChange : ∀ (A C B : Type) [CommRing A] [CommRing C]
    [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Algebra.Smooth A C]
    [Algebra.Smooth A B] (Q : Ideal B) [Q.IsPrime],
    Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) →
      ∃ f : B, f ∉ Q ∧ Algebra.Etale C (Localization.Away f) := by
  intro A C B _ _ _ _ _ _ _ _ _ Q _ h
  let BQ := Localization.AtPrime Q
  let φ := mapBaseChange A C B
  have hψ₀ : Function.Bijective (φ.baseChange BQ) :=
    bijective_of_bijective_lTensor_residueField _ (bijective_lTensor_baseChange_of_bijective Q φ h)
  let eM := AlgebraTensorModule.cancelBaseChange C B BQ BQ Ω[C⁄A]
  have hbc : IsBaseChange BQ (map A A B BQ) :=
    (isLocalizedModule_iff_isBaseChange Q.primeCompl BQ _).mp
      (isLocalizedModule_map A B BQ Q.primeCompl)
  let eN := hbc.equiv
  have key : ∀ x, mapBaseChange A C BQ (eM x) = eN (φ.baseChange BQ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul q y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add (f := _)] at hy hz ⊢; rw [hy, hz]
      | tmul b ω =>
        simp only [eM, eN, φ, AlgebraTensorModule.cancelBaseChange_tmul, mapBaseChange_tmul,
          LinearMap.baseChange_tmul]
        rw [IsBaseChange.equiv_tmul, map_smul, kaehler_map_map_apply, smul_assoc, smul_comm q b]
  have hψ : Function.Bijective (mapBaseChange A C BQ) := by
    have : ⇑(mapBaseChange A C BQ) = eN ∘ (φ.baseChange BQ) ∘ eM.symm := by
      funext x; simp [← key]
    rw [this]
    exact eN.bijective.comp (hψ₀.comp eM.symm.bijective)
  haveI : Algebra.FormallySmooth B BQ := Algebra.FormallySmooth.of_isLocalization Q.primeCompl
  haveI : Algebra.FormallySmooth A BQ := Algebra.FormallySmooth.comp A B BQ
  haveI : Algebra.IsEtaleAt C Q := formallyEtale_of_bijective_mapBaseChange A C BQ hψ
  haveI : Algebra.FinitePresentation C B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A C B
  exact Algebra.exists_etale_of_isEtaleAt Q

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dvd_of_forall_height_one_exists_dvd_mul {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {h z : A} (hh : h ≠ 0)
    (H : ∀ P : Ideal A, P.IsPrime → P.height = 1 → ∃ s ∉ P, h ∣ s * z) : h ∣ z := by
  let K := FractionRing A
  have hhK : algebraMap A K h ≠ 0 := fun h0 =>
    hh (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K z / algebraMap A K h ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨s, hs, t, ht⟩ := H P hP h1
    refine ⟨s, hs, t, ?_⟩
    rw [← mul_div_assoc, eq_div_iff hhK, ← map_mul, ← map_mul, ht, mul_comm]
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hhK, mul_comm]

section SquareIdeal

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

theorem dvd_mul_of_dvd_sq_of_dvd_sq {h x y : A} (hx : h ∣ x ^ 2) (hy : h ∣ y ^ 2) : h ∣ x * y := by
  have : h ^ 2 ∣ (x * y) ^ 2 := by
    rw [mul_pow, sq h]; exact mul_dvd_mul hx hy
  exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 this

def sqDvdIdeal (h : A) : Ideal A where
  carrier := {x | h ∣ x ^ 2}
  add_mem' := by
    intro x y hx hy
    have hxy := dvd_mul_of_dvd_sq_of_dvd_sq hx hy
    show h ∣ (x + y) ^ 2
    have e : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    rw [e]
    exact dvd_add (dvd_add hx (dvd_mul_of_dvd_right hxy _)) hy
  zero_mem' := by show h ∣ (0 : A) ^ 2; simp
  smul_mem' := by
    intro c x hx
    show h ∣ (c * x) ^ 2
    rw [mul_pow]; exact dvd_mul_of_dvd_right hx _

theorem mem_sqDvdIdeal {h x : A} : x ∈ sqDvdIdeal h ↔ h ∣ x ^ 2 := Iff.rfl

end SquareIdeal

theorem isUnit_mul_sq_of_faithfullyFlat : ∀ (C C' : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing C'] [IsDomain C'] [IsNoetherianRing C'] [IsIntegrallyClosed C'] [Algebra C C'] [Module.FaithfullyFlat C C'] (h : C), h ≠ 0 → (∃ (u : C'ˣ) (f : C'), algebraMap C C' h = u * f ^ 2) → (∀ p : Ideal C, p.IsPrime → p.height = 1 → ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2) → ∃ (u : Cˣ) (a : C), h = u * a ^ 2 := by
  intro C C' _ _ _ _ _ _ _ _ _ _ _ h hh hsq Hp
  obtain ⟨u, f, hf⟩ := hsq
  have hflat : (algebraMap C C').Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let J := sqDvdIdeal h

  have hJf : J.map (algebraMap C C') ≤ Ideal.span {f} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨z, hz⟩ := mem_sqDvdIdeal.1 hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
    refine ⟨(u : C') * algebraMap C C' z, ?_⟩
    rw [← map_pow, hz, map_mul, hf]; ring

  have hcol : (Ideal.span {h}).colon (J : Set C) ≤ J := by
    intro y hy
    rw [Submodule.mem_colon] at hy
    apply mem_sqDvdIdeal.2
    apply dvd_of_forall_height_one_exists_dvd_mul hh
    intro P hP h1
    obtain ⟨a, b, c, hb, hc, habc⟩ := Hp P hP h1
    have hac : a * c ∈ J := mem_sqDvdIdeal.2 ⟨b * c, by linear_combination (-c) * habc⟩
    have hy' := hy (a * c) hac
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hy'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨b * c, fun hm => (hP.mem_or_mem hm).elim hb hc, t ^ 2, ?_⟩
    have e : h * (b * c * y ^ 2) = h * (h * t ^ 2) := by
      linear_combination (c * y ^ 2) * habc + (y * (a * c) + h * t) * ht
    exact mul_left_cancel₀ hh e

  have hfJ : f ∈ J.map (algebraMap C C') := by
    have hm : f ∈ ((Ideal.span {h}).colon (J : Set C)).map (algebraMap C C') := by
      rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_span, Set.image_singleton,
        Submodule.mem_colon]
      intro p hp
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 (hJf hp)
      rw [smul_eq_mul, Ideal.mem_span_singleton, hf]
      exact ⟨((u⁻¹ : C'ˣ) : C') * w, by linear_combination (-(f ^ 2 * w)) * u.mul_inv⟩
    exact Ideal.map_mono hcol hm
  have hJeq : J.map (algebraMap C C') = Ideal.span {f} :=
    le_antisymm hJf ((Ideal.span_singleton_le_iff_mem _).2 hfJ)

  have hY : ((J * J).colon (Ideal.span {h} : Set C)).map (algebraMap C C') = ⊤ := by
    rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_mul, hJeq, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_mul_span_singleton, Ideal.eq_top_iff_one,
      Submodule.mem_colon]
    intro p hp
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 hp
    rw [smul_eq_mul, _root_.one_mul, Ideal.mem_span_singleton, hf]
    exact ⟨(u : C') * w, by ring⟩
  have hhJJ : h ∈ J * J := by
    have e := Ideal.comap_map_eq_self_of_faithfullyFlat (B := C')
      ((J * J).colon (Ideal.span {h} : Set C))
    rw [hY, Ideal.comap_top] at e
    have h1 : (1 : C) ∈ (J * J).colon (Ideal.span {h} : Set C) := e ▸ Submodule.mem_top
    rw [Submodule.mem_colon] at h1
    simpa using h1 h (Ideal.mem_span_singleton_self h)

  by_contra hne
  have hle : J * J ≤ Ideal.span {h} * maximalIdeal C := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨e, he⟩ := dvd_mul_of_dvd_sq_of_dvd_sq (mem_sqDvdIdeal.1 hx) (mem_sqDvdIdeal.1 hy)
    by_cases hem : e ∈ maximalIdeal C
    · rw [he]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self h) hem
    · exfalso
      have heu : IsUnit e := by
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hem; exact hem
      obtain ⟨a, ha⟩ := mem_sqDvdIdeal.1 hx
      obtain ⟨b, hb⟩ := mem_sqDvdIdeal.1 hy
      have hab : a * b = e ^ 2 := by
        have e2 : h ^ 2 * (a * b) = h ^ 2 * e ^ 2 := by
          linear_combination (-(h * b)) * ha - x ^ 2 * hb + (x * y + h * e) * he
        exact mul_left_cancel₀ (pow_ne_zero 2 hh) e2
      have hau : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ heu.pow 2)
      exact hne ⟨hau.unit⁻¹, x, by rw [ha]; linear_combination (-h) * hau.val_inv_mul⟩
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.1 (hle hhJJ)
  have hz1 : z = 1 := mul_left_cancel₀ hh (by rw [hz', _root_.mul_one])
  exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FibreTransfer

theorem exists_residueField_factor (S : Scheme.{0}) (p : S) (K : Type) [Field K] (x : Sp K ⟶ S)
    (hx : x (closedPoint K) = p) :
    ∃ θ : S.residueField p ⟶ CommRingCat.of K, Spec.map θ ≫ S.fromSpecResidueField p = x := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x⟩

theorem isGrpPullback_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    letI : (Over.pullback (S.fromSpecResidueField p)).Monoidal :=
      (Over.instBraidedPullback (f := S.fromSpecResidueField p)).toMonoidal
    letI : GrpObj ((Over.pullback (S.fromSpecResidueField p)).obj G) :=
      Functor.grpObjObj (F := Over.pullback (S.fromSpecResidueField p)) (G := G)
    IsGrpPullback ((Over.pullback (Spec.map θ ≫ S.fromSpecResidueField p)).obj G)
      ((Over.pullback (S.fromSpecResidueField p)).obj G) (Spec.map θ)
      (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
        (by rw [pullback.condition, Category.assoc])) := by
  letI : (Over.pullback (S.fromSpecResidueField p)).Monoidal :=
    (Over.instBraidedPullback (f := S.fromSpecResidueField p)).toMonoidal
  letI : GrpObj ((Over.pullback (S.fromSpecResidueField p)).obj G) :=
    Functor.grpObjObj (F := Over.pullback (S.fromSpecResidueField p)) (G := G)
  refine (isGrpPullback_pullback G (S.fromSpecResidueField p)).cancel
    ((isGrpPullback_pullback G (Spec.map θ ≫ S.fromSpecResidueField p)).congr rfl
      (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

theorem lbIso_fibre {S : Scheme.{0}} (G : Over S) {L : LB G.left} (hL : L.IsLB) (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    LBIso (L.pull (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p)))
      ((L.pull (pullback.fst G.hom (S.fromSpecResidueField p))).pull
        (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
          (by rw [pullback.condition, Category.assoc]))) := by
  have e := GlobalTheory.FibreAmple.lbIso_pull_pull hL
    (pullback.lift (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p))
      (pullback.snd G.hom _ ≫ Spec.map θ) (by rw [pullback.condition, Category.assoc]))
    (pullback.fst G.hom (S.fromSpecResidueField p))
  rw [pullback.lift_fst] at e
  exact e.symm

end GlobalTheory.FibreTransfer


open GlobalTheory.FibreTransfer in
theorem GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  intro S G _ hqc hsep hsm L hL K₁ _ z hP hA hK K _ x hx
  generalize hy : z (closedPoint K₁) = y at hx
  obtain ⟨θ₁, hz⟩ := exists_residueField_factor S y K₁ z hy
  obtain ⟨θ, rfl⟩ := exists_residueField_factor S y K x hx
  clear hy
  subst hz
  haveI := hqc; haveI := hsep; haveI := hsm
  have hLy := pull_isLB hL (pullback.fst G.hom (S.fromSpecResidueField y))
  have i₁ : QuasiCompact ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show QuasiCompact (pullback.snd G.hom _) from inferInstance
  have i₂ : IsSeparated ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show IsSeparated (pullback.snd G.hom _) from inferInstance
  have i₃ : Smooth ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show Smooth (pullback.snd G.hom _) from inferInstance
  letI : (Over.pullback (S.fromSpecResidueField y)).Monoidal :=
    (Over.instBraidedPullback (f := S.fromSpecResidueField y)).toMonoidal
  letI : GrpObj ((Over.pullback (S.fromSpecResidueField y)).obj G) :=
    Functor.grpObjObj (F := Over.pullback (S.fromSpecResidueField y)) (G := G)
  have hd := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (S.residueField y) K₁ θ₁.hom
    ((Over.pullback (S.fromSpecResidueField y)).obj G) ((Over.pullback (Spec.map θ₁ ≫ S.fromSpecResidueField y)).obj G) _
    (isGrpPullback_fibre G y K₁ θ₁) _ _ hLy (pull_isLB hL _) (lbIso_fibre G hL y K₁ θ₁) hP hA hK
  have h₂ := isGrpPullback_fibre G y K θ
  obtain ⟨w, hw⟩ := lbIso_fibre G hL y K θ
  exact ⟨relAmple_pull h₂.1 hLy (pull_isLB hL _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hd.2.1,
    kTriv_pull h₂ hLy (pull_isLB hL _) ((isGen_iff w).1 hw) hd.2.2⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_field_of_point_eq : ∀ (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X), a (closedPoint K₁) = b (closedPoint K₂) → ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b := by
  intro X K₁ K₂ _ _ a b h
  obtain ⟨⟨x, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ X).symm.surjective a
  obtain ⟨⟨y, g⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₂ X).symm.surjective b
  have hxy : x = y := by
    have h1 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₁ X).apply_symm_apply ⟨x, f⟩)
    have h2 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₂ X).apply_symm_apply ⟨y, g⟩)
    exact h1.symm.trans (h.trans h2)
  subst hxy
  letI : Algebra (X.residueField x) K₁ := f.hom.toAlgebra
  letI : Algebra (X.residueField x) K₂ := g.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) K₁ K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) K₁ K₂)
  letI : Field ((TensorProduct (X.residueField x) K₁ K₂) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(TensorProduct (X.residueField x) K₁ K₂) ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := X.residueField x) (A := K₁) (B := K₂)).toRingHom, ?_⟩
  change Spec.map _ ≫ Spec.map f ≫ X.fromSpecResidueField x = Spec.map _ ≫ Spec.map g ≫ X.fromSpecResidueField x
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext c
  change Ideal.Quotient.mk m (TensorProduct.tmul _ (algebraMap _ K₁ c) 1) = Ideal.Quotient.mk m (TensorProduct.tmul _ 1 (algebraMap _ K₂ c))
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.Mum
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bundleIsoOntoPullback_intertwines_transitions : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z) (L : LB Z) (L' : LB Y) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (i i' : L.ι) (k k' : L'.ι) (O O' : Y.Opens) (hO : O ≤ (L.pull φ).U (fun _ => i) ⊓ L'.U k) (hO' : O' ≤ (L.pull φ).U (fun _ => i') ⊓ L'.U k') (hk : O ≤ L'.U k) (hk' : O' ≤ L'.U k') (hu : O ⊓ O' ≤ φ ⁻¹ᵁ (L.U i ⊓ L.U i')), resG Y hu (pullU φ _ (L.g i i')).val * resG Y (inf_le_right : O ⊓ O' ≤ O') (resG Y hO' (w.s (fun _ => i', k')).val) = resG Y (inf_le_left : O ⊓ O' ≤ O) (resG Y hO (w.s (fun _ => i, k)).val) * resG Y (inf_le_inf hk hk') (L'.g k k').val := by
  first | exact @GlobalTheory.LogKSCoc.iso_pull_intertwines | exact GlobalTheory.LogKSCoc.iso_pull_intertwines | (intros; apply GlobalTheory.LogKSCoc.iso_pull_intertwines <;> assumption)
end
