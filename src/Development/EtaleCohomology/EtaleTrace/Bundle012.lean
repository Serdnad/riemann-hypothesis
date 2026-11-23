module

public import Development.EtaleCohomology.EtaleTrace.Bundle009
public import Development.EtaleCohomology.EtaleTrace.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def chartMor {k : Type} [Field k] {X : Scheme.{0}} {N : ℕ} (i : Fin (N + 1)) (U : X.Opens)
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
    (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)) :
    U.toScheme ⟶ PN k N :=
  U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)) ≫
    Proj.awayι _ (MvPolynomial.X i) hx zero_lt_one

def ChartOverK : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  chartMor i U hx φ ≫ PNto k N = U.ι ≫ p

def ChartGenOn : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  GenOn p w U (chartMor i U hx φ)

theorem ChartGen_of (h1 : ChartOverK) (h2 : ChartGenOn) : ChartGen := by
  intro k _ X _ p N w i hi U hx φ hφ
  exact ⟨chartMor i U hx φ, h1 k p N w i hi U hx φ hφ, h2 k p N w i hi U hx φ hφ⟩

theorem GenOutChart_of_two (h1 : ChartOverK) (h2 : ChartGenOn) : GenOutChart :=
  GenOutChart_of_gen (ChartGen_of h1 h2)

end LateralTheory.EtaleTrace.Cov
end
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf

theorem formallyEtale_of_fraction {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.FormallyUnramified A K] : Algebra.FormallyEtale A K := by
  have hAK : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A B K]
    exact (IsFractionRing.injective B K).comp hinj
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hAK
  let := FractionRing.liftAlgebra A K
  have : Algebra.FormallyUnramified (FractionRing A) K :=
    Algebra.FormallyUnramified.of_restrictScalars A _ _
  have : Algebra.EssFiniteType B K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors B)
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A B K
  have : Algebra.EssFiniteType (FractionRing A) K := Algebra.EssFiniteType.of_comp A _ _
  have : Algebra.FormallyEtale (FractionRing A) K := Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FormallyEtale A (FractionRing A) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact Algebra.FormallyEtale.comp A (FractionRing A) K

theorem isEtaleAt_bot {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.FormallyUnramified A K] :
    ∃ _ : (⊥ : Ideal B).IsPrime, Algebra.IsEtaleAt A (⊥ : Ideal B) := by
  refine ⟨Ideal.isPrime_bot, ?_⟩
  have := formallyEtale_of_fraction (A := A) (B := B) (K := K) hinj
  have : IsLocalization (nonZeroDivisors B) (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [← Ideal.primeCompl_bot]; infer_instance
  let φ : K ≃ₐ[B] Localization.AtPrime (⊥ : Ideal B) :=
    IsLocalization.algEquiv (nonZeroDivisors B) _ _
  exact Algebra.FormallyEtale.of_equiv (φ.restrictScalars A)

theorem genEtaleAtBot : GenEtaleAtBot := by
  intro X P _ _ π U hU hne hU' hfin hinj hun
  haveI : Nonempty U := hne.to_subtype
  have hV : Nonempty (π ⁻¹ᵁ U) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hb : π ⁻¹ᵁ U = ⊥ := SetLike.ext' (Set.isEmpty_coe_sort.mp h)
    have : Subsingleton Γ(X, π ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
    exact not_subsingleton Γ(P, U) ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  let _ := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfin
  have hη : genericPoint X ∈ π ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (π ⁻¹ᵁ U).isOpen).mpr (by simpa using hV)
  have hx : π (genericPoint X) ∈ U := hη
  let alS := P.presheaf.algebra_section_stalk ⟨π (genericPoint X), hx⟩
  have hloc := hU.isLocalization_stalk ⟨π (genericPoint X), hx⟩
  have h1 : (P.presheaf.germ U (π (genericPoint X)) hx).hom.FormallyUnramified := by
    have := Algebra.FormallyUnramified.of_isLocalization (Rₘ := P.presheaf.stalk (π (genericPoint X)))
      (hU.primeIdealOf ⟨π (genericPoint X), hx⟩).asIdeal.primeCompl
    exact RingHom.formallyUnramified_algebraMap.mpr this
  have h2 := h1.comp hun
  rw [← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap] at h2
  let algK : Algebra Γ(P, U) X.functionField := (π.app U ≫ X.presheaf.germ _ _ hη).hom.toAlgebra
  haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FormallyUnramified Γ(P, U) X.functionField := h2
  have := functionField_isFractionRing_of_isAffineOpen X (π ⁻¹ᵁ U) hU'
  exact isEtaleAt_bot (K := X.functionField) hinj

theorem GenEtaleAtBot_of : GenEtaleAtBot := genEtaleAtBot

end LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem genAffineData : GenAffineData := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj
  obtain ⟨x⟩ : Nonempty P := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens (show x ∈ (⊤ : P.Opens) from trivial)
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  refine ⟨U, hU, ⟨x, hxU⟩, hU', ?_, ?_, ?_⟩
  · have hft : (r.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) r hr ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    letI := (r.appLE ⊤ U le_top).hom.toAlgebra
    haveI : IsNoetherianRing Γ(S k, ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
    haveI : Algebra.FiniteType Γ(S k, ⊤) Γ(P, U) := hft
    exact Algebra.FiniteType.isNoetherianRing Γ(S k, ⊤) Γ(P, U)
  · haveI : IsAffine U := hU
    have h0 : (π ∣_ U).appTop.hom.Finite := (π ∣_ U).finite_appTop
    rw [morphismRestrict_appTop] at h0
    have gen : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = U →
        RingHom.Finite (π.app W ≫ X.presheaf.map (eqToHom h).op).hom → RingHom.Finite (π.app U).hom := by
      rintro W T h rfl
      subst h
      simp
    exact gen _ _ _ (by simp) h0
  · haveI : IsDominant π := inferInstance
    haveI : IsSchemeTheoreticallyDominant π := .of_isDominant π
    exact π.app_injective U

theorem GenEtale_of_atBot (h : GenEtaleAtBot) : GenEtale := GenEtale_of' genAffineData h

end LateralTheory.EtaleTrace.Cov
end
