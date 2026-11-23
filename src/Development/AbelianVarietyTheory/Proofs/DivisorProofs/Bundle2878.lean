module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle018
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Mathlib.Algebra.Algebra.ZMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem isJacobsonRing_int_of_dim_one : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_trait_finite_residueField_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  intro B _ _ _ _ m h hm hh
  classical

  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : IsJacobsonRing ℤ := isJacobsonRing_int_of_dim_one
  haveI : Algebra.FiniteType ℤ (B ⧸ m) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m)
  set p := ringChar (B ⧸ m) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (B ⧸ m) 0 := h0 ▸ ringChar.charP (B ⧸ m)
    haveI : CharZero (B ⧸ m) := CharP.charP_to_charZero _
    haveI : Algebra.IsIntegral ℤ (B ⧸ m) := Algebra.IsIntegral.of_finite ℤ _
    exact Int.not_isField
      (isField_of_isIntegral_of_isField (algebraMap ℤ (B ⧸ m)).injective_int (Field.toIsField _))
  haveI : CharP (B ⧸ m) p := ringChar.charP (B ⧸ m)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (B ⧸ m) p).resolve_right hp0⟩
  letI : Algebra (ZMod p) (B ⧸ m) := ZMod.algebra (B ⧸ m) p
  haveI : IsScalarTower ℤ (ZMod p) (B ⧸ m) := AddCommGroup.intIsScalarTower
  haveI : Algebra.FiniteType (ZMod p) (B ⧸ m) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (B ⧸ m)
  haveI : Module.Finite (ZMod p) (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing (ZMod p) (B ⧸ m)
  haveI hfin : Finite (B ⧸ m) := Module.finite_of_finite (ZMod p)
  have hpm : (p : B) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ p
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.mpr hp0

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let R := Localization.AtPrime m
  haveI hRn : IsNoetherianRing R := IsLocalization.isNoetherianRing m.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors m)
  have hx0 : algebraMap B R (h * p) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B R)]; exact fun e => mul_ne_zero hh hpB (hinj e)
  have hxm : algebraMap B R (h * p) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R m _).mpr (m.mul_mem_left h hpm)
  obtain ⟨q, hq, hnq, hdim⟩ := GlobalTheory.T.exists_prime_not_mem_ringKrullDim_quotient_eq_one R (algebraMap B R (h * p)) hx0 hxm
  let D := R ⧸ q
  haveI : IsDomain D := Ideal.Quotient.isDomain q
  haveI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let φ : B →+* D := (Ideal.Quotient.mk q).comp (algebraMap B R)
  have hcompR : Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hcomp : Ideal.comap φ (IsLocalRing.maximalIdeal D) = m := by
    rw [← Ideal.comap_comap, hcompR]; exact Localization.AtPrime.under_maximalIdeal
  have hφh : φ h ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_right _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  have hφp : φ (p : B) ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_left _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  haveI hD0 : CharZero D := by
    haveI : CharP D (ringChar D) := ringChar.charP D
    rcases CharP.char_is_prime_or_zero D (ringChar D) with hl | hl
    · exfalso
      have hlm' : ((ringChar D : ℕ) : B) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal D) := by
        rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]; exact zero_mem _
      have hlm : ((ringChar D : ℕ) : B) ∈ m := hcomp.le hlm'
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hlm
      have hdvd : p ∣ ringChar D := (CharP.cast_eq_zero_iff (B ⧸ m) p _).mp hlm
      have hpl : p = ringChar D :=
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hl).mp hdvd)
      apply hφp; rw [map_natCast, hpl, CharP.cast_eq_zero]
    · haveI : CharP D 0 := hl ▸ ringChar.charP D
      exact CharP.charP_to_charZero D

  have hsurj : Function.Surjective ((IsLocalRing.residue D).comp φ) := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hsR := IsLocalization.surjective_quotientMap_of_maximal_of_localization m.primeCompl R
      (I := IsLocalRing.maximalIdeal R) (J := m)
      (H := le_of_eq Localization.AtPrime.under_maximalIdeal.symm)
      (by rw [Localization.AtPrime.under_maximalIdeal]; exact hm)
    obtain ⟨bb, hb⟩ := hsR (Ideal.Quotient.mk _ r)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bb
    refine ⟨b, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hb
    simp only [RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hb' : algebraMap B R b - r ∈ Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) :=
      hcompR ▸ hb
    simpa [φ, map_sub] using hb'
  have hker : ∀ b ∈ m, ((IsLocalRing.residue D).comp φ) b = 0 := by
    intro b hb
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_comap, hcomp]; exact hb
  haveI hresfin : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_surjective (Ideal.Quotient.lift m _ hker) (by
      intro y; obtain ⟨b, rfl⟩ := hsurj y; exact ⟨Ideal.Quotient.mk m b, rfl⟩)
  obtain ⟨V, _, _, _, hcV, g, hg, hgl, hVfin⟩ :=
    GlobalTheory.exists_complete_dvr_finite_residueField D inferInstance hdim hresfin
  haveI : CharZero V := ⟨fun a b e => by
    apply Nat.cast_injective (R := D); apply hg; rw [map_natCast, map_natCast]; exact e⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, g.comp φ, hcV, hVfin, ?_, ?_⟩
  · rw [RingHom.comp_apply]; intro e; apply hφh; apply hg; rw [e, map_zero]
  · have hgm : Ideal.comap g (IsLocalRing.maximalIdeal V) = IsLocalRing.maximalIdeal D := by
      ext x; simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    rw [← Ideal.comap_comap, hgm, hcomp]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.LocExt

theorem exists_finite_normal_cover_of_finiteDimensional : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'), Function.Injective ρ ∧ ρ.Finite ∧ ((τ.comp (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  intro R _ _ _ _ hcomp K' _ _ _
  have hnorm : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hCN : IsCN R := ⟨inferInstance, hnorm, hcomp, inferInstance⟩
  let K := FractionRing R
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K K' := inferInstance
  let C := integralClosure R K'
  haveI hCf : Module.Finite R C := IsIntegralClosure.finite R K K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRC : Function.Injective (algebraMap R C) := fun x y h => hRK' (congrArg Subtype.val h)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρ, hρf, -, hσρ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) hCN hRC
      (RingHom.finite_algebraMap.2 hCf)
  obtain ⟨hnoeth', hnorm', -, -⟩ := hCN'
  letI : Algebra C R' := σ.toAlgebra
  letI : Algebra R R' := ρ.toAlgebra
  haveI : IsScalarTower R C R' := IsScalarTower.of_algebraMap_eq (fun r => (RingHom.congr_fun hσρ r).symm)
  haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hσ : Function.Injective σ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hker : RingHom.ker σ = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := R)
      ext r
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro h
        apply hρ
        rw [map_zero, ← h]
        exact (RingHom.congr_fun hσρ r).symm
      · rintro rfl; simp
    have : c ∈ RingHom.ker σ := hc
    rw [hker] at this
    exact this
  have hσ' : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσ
  let τ : K' →+* FractionRing R' := IsFractionRing.lift (A := C) hσ'
  refine ⟨R', inferInstance, inferInstance, hnoeth', hnorm', inferInstance, ρ, τ, hρ, hρf, ?_⟩
  ext r
  simp only [RingHom.comp_apply]
  have h1 : algebraMap K K' (algebraMap R K r) = algebraMap C K' (algebraMap R C r) := rfl
  rw [h1]
  simp only [τ, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  rw [← RingHom.comp_apply σ, hσρ]

end GlobalTheory.LocExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SmoothAdic

open TensorProduct

theorem exists_smooth_away_of_quotient_pow_equiv : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  intro R _ _ _ O C _ _ _ _ hO hC hiso q hq hqm
  have hsm : ∀ e : ℕ, Algebra.Smooth (R ⧸ maximalIdeal R ^ (e + 1))
      (TensorProduct R (R ⧸ maximalIdeal R ^ (e + 1)) C) := by
    intro e
    obtain ⟨φ⟩ := hiso e
    let J := maximalIdeal R ^ (e + 1)
    let φ' : (O ⧸ J.map (algebraMap R O)) ≃ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)) :=
      AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective φ
    let ψ : ((R ⧸ J) ⊗[R] O) ≃ₐ[R ⧸ J] ((R ⧸ J) ⊗[R] C) :=
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor O J).symm.trans φ').trans
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C J)
    exact Algebra.Smooth.of_equiv ψ
  haveI := hq
  haveI : Algebra.IsSmoothAt R q :=
    isSmoothAt_of_smooth_quotient_pow R (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top C hsm q hqm
  haveI : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp hC
  obtain ⟨g, hg, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  exact ⟨g, hg, hs⟩

end GlobalTheory.SmoothAdic
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.sections_preimage_affine_baseChange_eq_sum_products : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Scheme.{0}) (p : P ⟶ Sp R) (V : P.Opens), IsAffineOpen V → ∀ x : Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ V), ∃ (n : ℕ) (a : Fin n → Γ(P, V)) (r : Fin n → R₁), x = ∑ i, ((pullback.fst p (spMap ρ)).app V).hom (a i) * ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i)) := by
  first | exact @GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum | exact GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum | (intros; apply GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GrpPullbackPaste

theorem mul_left_congr {B : Scheme.{0}} (Gb : Over B) [GrpObj Gb] {X : Scheme.{0}} (a b : X ⟶ B) (hab : a = b)
    (x y : Over.mk a ⟶ Gb) (x' y' : Over.mk b ⟶ Gb) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    (x * y).left = (x' * y').left := by
  subst hab
  have h1 : x = x' := Over.OverMorphism.ext hx
  have h2 : y = y' := Over.OverMorphism.ext hy
  rw [h1, h2]

end GlobalTheory.GrpPullbackPaste

open GlobalTheory.GrpPullbackPaste in
theorem GlobalTheory.isGrpPullback_paste : ∀ {B S T T' : Scheme.{0}} (Gb : Over B) [GrpObj Gb] (Gs : Over S) [GrpObj Gs] (Gt : Over T) [GrpObj Gt] (Gt' : Over T') [GrpObj Gt'] (fS : S ⟶ B) (fT : T ⟶ B) (g : T' ⟶ T) (h : T' ⟶ S) (φS : Gs.left ⟶ Gb.left) (φT : Gt.left ⟶ Gb.left) (ψ : Gt'.left ⟶ Gt.left), IsGrpPullback Gs Gb fS φS → IsGrpPullback Gt Gb fT φT → IsGrpPullback Gt' Gt g ψ → h ≫ fS = g ≫ fT → ∃ φ : Gt'.left ⟶ Gs.left, IsGrpPullback Gt' Gs h φ ∧ φ ≫ φS = ψ ≫ φT := by
  intro B S T T' Gb _ Gs _ Gt _ Gt' _ fS fT g h φS φT ψ hS hT hψ hcomm
  have hsq : (ψ ≫ φT) ≫ Gb.hom = (Gt'.hom ≫ h) ≫ fS := by
    rw [Category.assoc, hT.1.w, ← Category.assoc, hψ.1.w, Category.assoc, Category.assoc, hcomm]
  refine ⟨hS.1.lift (ψ ≫ φT) (Gt'.hom ≫ h) hsq, ⟨?_, ?_⟩, hS.1.lift_fst _ _ hsq⟩
  · have hpaste := hψ.1.paste_horiz hT.1
    refine IsPullback.of_right ?_ (hS.1.lift_snd _ _ hsq) hS.1
    rw [hS.1.lift_fst _ _ hsq, hcomm]
    exact hpaste
  · intro X x y x₀ y₀ hx hy
    set φ := hS.1.lift (ψ ≫ φT) (Gt'.hom ≫ h) hsq with hφ
    have hφ1 : φ ≫ φS = ψ ≫ φT := hS.1.lift_fst _ _ hsq
    have hφ2 : φ ≫ Gs.hom = Gt'.hom ≫ h := hS.1.lift_snd _ _ hsq
    let mk1 (z : Over.mk (X.hom ≫ h) ⟶ Gs) : Over.mk ((Over.mk (X.hom ≫ h)).hom ≫ fS) ⟶ Gb :=
      Over.homMk (z.left ≫ φS) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hS.1.w, ← Category.assoc, Over.w z]
        rfl)
    let mk2 (z : X ⟶ Gt') : Over.mk (X.hom ≫ g) ⟶ Gt :=
      Over.homMk (z.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hψ.1.w, ← Category.assoc, Over.w z])
    let mk3 (z : Over.mk (X.hom ≫ g) ⟶ Gt) : Over.mk ((Over.mk (X.hom ≫ g)).hom ≫ fT) ⟶ Gb :=
      Over.homMk (z.left ≫ φT) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hT.1.w, ← Category.assoc, Over.w z]
        rfl)
    have e1 := hS.2 (Over.mk (X.hom ≫ h)) x₀ y₀ (mk1 x₀) (mk1 y₀) rfl rfl
    have e2 := hψ.2 X x y (mk2 x) (mk2 y) rfl rfl
    have e3 := hT.2 (Over.mk (X.hom ≫ g)) (mk2 x) (mk2 y) (mk3 (mk2 x)) (mk3 (mk2 y)) rfl rfl
    have hab : (Over.mk (X.hom ≫ h)).hom ≫ fS = (Over.mk (X.hom ≫ g)).hom ≫ fT := by
      simp only [Over.mk_hom, Category.assoc, hcomm]
    have e4 := mul_left_congr Gb _ _ hab (mk1 x₀) (mk1 y₀) (mk3 (mk2 x)) (mk3 (mk2 y))
      (by simp only [mk1, mk2, mk3, Over.homMk_left, hx, Category.assoc, hφ1])
      (by simp only [mk1, mk2, mk3, Over.homMk_left, hy, Category.assoc, hφ1])
    apply hS.1.hom_ext
    · rw [Category.assoc, hφ1, ← e1, e4, e3, ← Category.assoc, e2]
    · rw [Category.assoc, hφ2, ← Category.assoc, Over.w (x * y), Over.w (x₀ * y₀)]
      rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GrpPullPow

theorem isMonHom_of_mul_pts {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  · rw [MonObj.mul_eq_mul G, MonObj.mul_eq_mul H, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd]
    exact h (G ⊗ G) (fst G G) (snd G G)

theorem pr_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr hB hC hpr huniv
  have hw : ∀ a, (φB ≫ (pr a).left) ≫ C.hom = B'.hom ≫ t := fun a => by
    rw [Category.assoc, Over.w (pr a), hB.1.w]
  let pr' : Fin 8 → (B' ⟶ C') := fun a =>
    Over.homMk (hC.1.lift (φB ≫ (pr a).left) B'.hom (hw a)) (hC.1.lift_snd _ _ _)
  have h1 : ∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left := fun a => hC.1.lift_fst _ _ _
  have hpush : ∀ (T₁ : Over T') (x : T₁ ⟶ B') a,
      pushPt hC.1.w (x ≫ pr' a) = pushPt hB.1.w x ≫ pr a := by
    intro T₁ x a
    apply Over.OverMorphism.ext
    show (x.left ≫ (pr' a).left) ≫ χ = (x.left ≫ φB) ≫ (pr a).left
    rw [Category.assoc, h1, Category.assoc]
  refine ⟨pr', h1, fun a => ?_, fun T₁ y => ?_⟩
  · haveI := hpr a
    refine isMonHom_of_mul_pts _ fun T₁ x y => ?_
    apply Over.OverMorphism.ext
    apply hC.1.hom_ext
    · have e1 := hC.2 T₁ (x ≫ pr' a) (y ≫ pr' a) (pushPt hC.1.w (x ≫ pr' a))
        (pushPt hC.1.w (y ≫ pr' a)) rfl rfl
      have e2 := hB.2 T₁ x y (pushPt hB.1.w x) (pushPt hB.1.w y) rfl rfl
      rw [← e1, hpush, hpush, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, h1,
        ← Category.assoc, ← e2]
    · rw [Over.w, Over.w]
  · let T₀ : Over T := Over.mk (T₁.hom ≫ t)
    obtain ⟨x₀, hx₀, hu⟩ := huniv T₀ (fun a => pushPt hC.1.w (y a))
    have wx : x₀.left ≫ B.hom = T₁.hom ≫ t := Over.w x₀
    let X : T₁ ⟶ B' := Over.homMk (hB.1.lift x₀.left T₁.hom wx) (hB.1.lift_snd _ _ _)
    have hX : X.left ≫ φB = x₀.left := hB.1.lift_fst _ _ _
    refine ⟨X, fun a => ?_, fun x' hx' => ?_⟩
    · apply Over.OverMorphism.ext
      apply hC.1.hom_ext
      · show (X.left ≫ (pr' a).left) ≫ χ = (y a).left ≫ χ
        rw [Category.assoc, h1, ← Category.assoc, hX]
        exact congrArg (fun q => q.left) (hx₀ a)
      · rw [Over.w, Over.w]
    · have e : pushPt hB.1.w x' = x₀ := hu _ fun a => by
        rw [← hpush, hx' a]
      apply Over.OverMorphism.ext
      apply hB.1.hom_ext
      · rw [hX]; exact congrArg (fun q => q.left) e
      · rw [Over.w, Over.w]

end GlobalTheory.GrpPullPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.SquareIso

theorem lbIso_pull_further {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem iso_pull_of_square : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  intro X Y Z Y' LA' LA L₁ L₂ ψ φ₁ φ₂ τ hA' hA h₁ h₂ e w₁ w₂ w₃
  have a : LBIso (LA.pull ψ) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₂ ψ e.symm
  have b : LBIso (L₂.pull φ₂) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₃ φ₂ rfl
  exact LBIso.trans hA' (pull_isLB h₁ _) (pull_isLB h₂ _) (LBIso.trans hA' (pull_isLB hA _) (pull_isLB h₁ _) w₁ a) b.symm

end GlobalTheory.Poinc.SquareIso
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_smooth_away_of_quotient_pow_equiv' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  first | exact @GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv | exact GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv | (intros; apply GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_lineBundleIso_pullback_commSquare : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  first | exact @GlobalTheory.Poinc.SquareIso.iso_pull_of_square | exact GlobalTheory.Poinc.SquareIso.iso_pull_of_square | (intros; apply GlobalTheory.Poinc.SquareIso.iso_pull_of_square <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.isGrpPullback_paste_factorisation : ∀ {B S T T' : Scheme.{0}} (Gb : Over B) [GrpObj Gb] (Gs : Over S) [GrpObj Gs] (Gt : Over T) [GrpObj Gt] (Gt' : Over T') [GrpObj Gt'] (fS : S ⟶ B) (fT : T ⟶ B) (g : T' ⟶ T) (h : T' ⟶ S) (φS : Gs.left ⟶ Gb.left) (φT : Gt.left ⟶ Gb.left) (ψ : Gt'.left ⟶ Gt.left), IsGrpPullback Gs Gb fS φS → IsGrpPullback Gt Gb fT φT → IsGrpPullback Gt' Gt g ψ → h ≫ fS = g ≫ fT → ∃ φ : Gt'.left ⟶ Gs.left, IsGrpPullback Gt' Gs h φ ∧ φ ≫ φS = ψ ≫ φT := by
  first | exact @GlobalTheory.isGrpPullback_paste | exact GlobalTheory.isGrpPullback_paste | (intros; apply GlobalTheory.isGrpPullback_paste <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighthPowerProjections_groupPullback : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  first | exact @GlobalTheory.GrpPullPow.pr_pull | exact GlobalTheory.GrpPullPow.pr_pull | (intros; apply GlobalTheory.GrpPullPow.pr_pull <;> assumption)

end
end
