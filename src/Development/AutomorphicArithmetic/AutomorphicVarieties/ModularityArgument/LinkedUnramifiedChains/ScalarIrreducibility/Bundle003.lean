module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MainFin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle080
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.Surjective
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.ChevalleyRestriction

private theorem main_fin (A : Type) [CommRing A] [IsDomain A] (s : Finset A) :
    ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B A],
      Algebra.adjoin B (s : Set A) = ⊤ → Function.Injective (algebraMap B A) →
      ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
        y b ≠ 0 → ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra5.main_fin A s

end UpperTheory.V.J.ChevalleyRestriction

theorem UpperTheory.V.J.chev :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
        ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
          ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  intro B A _ _ _ _ _ hft hinj a ha
  obtain ⟨s, hs⟩ := hft.out
  exact UpperTheory.V.J.ChevalleyRestriction.main_fin A s B hs hinj a ha
end

section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

open GroundTheory.Heights₂.Heights in
private theorem cm_of_regular_local (A : Type) [CommRing A] [IsRegularLocalRing A] :
    IsCohenMacaulayLocalRing A := by
  haveI hL : IsLocalRing A := IsRegularLocalRing.toIsLocalRing
  haveI hN : IsNoetherian A A := IsRegularLocalRing.toIsNoetherian
  obtain ⟨rs, hreg, hmax, hlen⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := A)
  refine @IsCohenMacaulayLocalRing.mk A _ hL hN ⟨rs, fun r hr => ?_, hreg.toIsWeaklyRegular, hlen.symm⟩
  rw [← hmax]
  exact Ideal.subset_span hr


open GroundTheory.Heights₂.Heights in
private theorem ass_min_of_surj {A B : Type} [CommRing A] [IsCohenMacaulayLocalRing A] [CommRing B]
    [Nontrivial B] (φ : A →+* B) (hφ : Function.Surjective φ) {k : ℕ} (x : Fin k → A)
    (hx : ∀ i, x i ∈ maximalIdeal A) (hk : RingHom.ker φ = Ideal.span (Set.range x))
    (hd : ringKrullDim B + (k : WithBot ℕ∞) ≤ ringKrullDim A) {P : Ideal B}
    (hP : P ∈ associatedPrimes B B) : P ∈ minimalPrimes B := by
  classical
  set I : Ideal A := Ideal.span (Set.range x) with hI
  let e : A ⧸ I ≃+* B := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have hdimB : ringKrullDim B = ringKrullDim (A ⧸ I) := (ringKrullDim_eq_of_ringEquiv e).symm
  have hs : ((Finset.univ.image x : Finset A) : Set A) = Set.range x := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcard : (Finset.univ.image x).card ≤ k :=
    Finset.card_image_le.trans (Finset.card_fin k).le
  have hle : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) := by
    have h0 := ringKrullDim_le_ringKrullDim_quotient_add_card (R := A) (Finset.univ.image x) (by
      rw [hs, IsLocalRing.ringJacobson_eq_maximalIdeal]
      rintro _ ⟨i, rfl⟩
      exact hx i)
    rw [hs] at h0
    refine h0.trans ?_
    gcongr
  have heq : ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) = ringKrullDim A :=
    le_antisymm (hdimB ▸ hd) hle
  have hCM : IsCohenMacaulayLocalRing (A ⧸ I) :=
    CMParameterQuotient.proof CMRegularElement.proof A k x hx heq
  have : IsCohenMacaulayLocalRing B := IsCohenMacaulayLocalRing.of_ringEquiv e
  exact mem_minimalPrimes_of_mem_associatedPrimes hP

private theorem min_of_localized {R : Type} [CommRing R] (Q : Ideal R) [Q.IsPrime] {P : Ideal R}
    (hP : P ∈ associatedPrimes R R) (hPQ : P ≤ Q)
    (h : ∀ P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q),
      P' ∈ minimalPrimes (Localization.AtPrime Q)) : P ∈ minimalPrimes R := by
  have hPprime : P.IsPrime := hP.1
  have hdis : Disjoint (Q.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    intro a ha haP
    exact ha (hPQ haP)
  set P' : Ideal (Localization.AtPrime Q) := P.map (algebraMap R (Localization.AtPrime Q)) with hP'
  have hcomap : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hPprime hdis
  have hass : P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q) := by
    refine Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      Q.primeCompl (Algebra.linearMap R (Localization.AtPrime Q)) P' ?_
    rw [hcomap]
    exact hP
  have hmin : P' ∈ (Ideal.map (algebraMap R (Localization.AtPrime Q)) (⊥ : Ideal R)).minimalPrimes := by
    rw [Ideal.map_bot]
    exact h P' hass
  rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q) (⊥ : Ideal R)] at hmin
  have key : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' ∈ (⊥ : Ideal R).minimalPrimes := hmin
  rw [hcomap] at key
  exact key

theorem UpperTheory.V.J.unmix :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (N N' : ℕ) (R : Type) [CommRing R]
        (p : MvPowerSeries (Fin N) O →+* R) (f : Fin N' → MvPowerSeries (Fin N) O), Function.Surjective p → RingHom.ker p = Ideal.span (Set.range f) →
        ∀ Q : Ideal R, Q.IsPrime → Q.height + N' ≤ (Q.comap p).height → ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R := by
  intro O _ _ _ _ N N' R _ p f hp hker Q hQ hht P hP hPQ
  set q : Ideal (MvPowerSeries (Fin N) O) := Q.comap p with hq
  haveI : IsRegularLocalRing (MvPowerSeries (Fin N) O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin N)
  haveI : IsRegularLocalRing (Localization.AtPrime q) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime q
  haveI : GroundTheory.Heights₂.Heights.IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
    cm_of_regular_local _
  let φ : Localization.AtPrime q →+* Localization.AtPrime Q := Localization.localRingHom q Q p rfl
  have hφ : Function.Surjective φ := RingHom.surjective_localRingHom_of_surjective p hp Q
  have hkerφ : RingHom.ker φ = (RingHom.ker p).map (algebraMap _ (Localization.AtPrime q)) :=
    IsLocalization.ker_map (M := q.primeCompl) (S := Localization.AtPrime q)
      (Localization.AtPrime Q) p (Submonoid.map_comap_eq_of_surjective hp Q.primeCompl)
  have hkx : RingHom.ker φ = Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (f i))) := by
    rw [hkerφ, hker, Ideal.map_span, ← Set.range_comp]
    rfl
  have hx : ∀ i, algebraMap _ (Localization.AtPrime q) (f i) ∈ maximalIdeal (Localization.AtPrime q) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
    have hfi : f i ∈ RingHom.ker p := by
      rw [hker]
      exact Ideal.subset_span ⟨i, rfl⟩
    show p (f i) ∈ Q
    rw [RingHom.mem_ker.mp hfi]
    exact Q.zero_mem
  have hd : ringKrullDim (Localization.AtPrime Q) + (N' : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
    exact_mod_cast hht
  refine min_of_localized Q hP hPQ ?_
  intro P' hP'
  exact ass_min_of_surj φ hφ _ hx hkx hd hP'
end

section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.htPres :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (N N' : ℕ) (R : Type) [CommRing R]
        (p : MvPowerSeries (Fin N) O →+* R) (f : Fin N' → MvPowerSeries (Fin N) O), Function.Surjective p → RingHom.ker p = Ideal.span (Set.range f) →
        ∀ Q : Ideal R, Q.IsPrime → ((Q.comap p).height : WithBot ℕ∞) + ringKrullDim (R ⧸ Q) = (N + 1 : ℕ) ∧ (Q.comap p).height ≤ Q.height + N' := by
  intro O _ _ _ _ N N' R _ p f hp hker Q hQ
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsCO O O := IsCO.self O
  haveI : IsCO O (MvPowerSeries (Fin N) O) := co_mvps O O (Fin N)
  haveI : IsNoetherianRing (MvPowerSeries (Fin N) O) := MvPowerSeries.isNoetherianRing O
  haveI : NoZeroDivisors (MvPowerSeries (Fin N) O) := inferInstance
  haveI : IsDomain (MvPowerSeries (Fin N) O) := NoZeroDivisors.to_isDomain _
  haveI hP : (Q.comap p).IsPrime := Ideal.comap_isPrime p Q
  have hdim : ringKrullDim (MvPowerSeries (Fin N) O) = ((N + 1 : ℕ) : WithBot ℕ∞) := (CA.cl_cm.1 O N).2
  have hsurj : Function.Surjective ((Ideal.Quotient.mk Q).comp p) :=
    (Ideal.Quotient.mk_surjective).comp hp
  have hk : RingHom.ker ((Ideal.Quotient.mk Q).comp p) = Q.comap p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have eQ : (MvPowerSeries (Fin N) O ⧸ Q.comap p) ≃+* (R ⧸ Q) :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  constructor
  · rw [← ringKrullDim_eq_of_ringEquiv eQ, ← hdim]
    exact co_caten O (MvPowerSeries (Fin N) O) (Q.comap p)
  · set K := RingHom.ker p
    let e : (MvPowerSeries (Fin N) O ⧸ K) ≃+* R := RingHom.quotientKerEquivOfSurjective hp
    have hmap : (Q.comap p).map (Ideal.Quotient.mk K) = Q.comap (e : (MvPowerSeries (Fin N) O ⧸ K) →+* R) := by
      have : Q.comap p = (Q.comap (e : (MvPowerSeries (Fin N) O ⧸ K) →+* R)).comap (Ideal.Quotient.mk K) := by
        rw [Ideal.comap_comap]
        congr 1
      rw [this, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hsub : Set.range f ⊆ (Q.comap p : Set (MvPowerSeries (Fin N) O)) := by
      rintro _ ⟨i, rfl⟩
      have : f i ∈ K := by
        rw [hker]
        exact Ideal.subset_span ⟨i, rfl⟩
      show p (f i) ∈ Q
      rw [RingHom.mem_ker.mp this]
      exact Q.zero_mem
    have h1 := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsub
    rw [← hker, hmap] at h1
    have he : (Q.comap (e : (MvPowerSeries (Fin N) O ⧸ K) →+* R)).height = Q.height :=
      RingEquiv.height_comap e Q
    rw [he] at h1
    refine h1.trans ?_
    gcongr
    calc (Set.range f).encard ≤ (Set.univ : Set (Fin N')).encard := by
          rw [← Set.image_univ]
          exact Set.encard_image_le _ _
      _ = N' := by
          rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.domMin :
    ∀ (A : Type) [CommRing A] (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q) → ∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
  intro A _ q _ hD P hP hPq a ha
  letI : Nontrivial (Localization.AtPrime q) := hD.toNontrivial
  letI : NoZeroDivisors (Localization.AtPrime q) :=
    isCancelMulZero_iff_noZeroDivisors.mp hD.toIsCancelMulZero
  have hK : (RingHom.ker (algebraMap A (Localization.AtPrime q))).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (algebraMap A (Localization.AtPrime q)) ≤ P := by
    intro x hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).1 hx
    have h0 : (m : A) * x ∈ P := by rw [hm]; exact P.zero_mem
    exact (hP.1.1.mem_or_mem h0).resolve_left (fun h => m.2 (hPq h))
  have hge : P ≤ RingHom.ker (algebraMap A (Localization.AtPrime q)) := hP.2 ⟨hK, bot_le⟩ hle
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) a).1 (hge ha)
  exact ⟨m, fun h => m.2 (hPq h), hm⟩
end
