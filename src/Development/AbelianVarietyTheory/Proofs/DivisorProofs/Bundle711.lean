module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle185
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousTo
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOfCurves
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MapOfRealMul
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.Bundle001
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticUnipotentBlockSecondDiag
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

theorem trace_eq_sum_mult_mul_re {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  apply GlobalTheory.CompanionTheory.AdeleCharLocal.trace_eq_sum <;> assumption

end GlobalTheory.TraceRealEmbeddingSum
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMTypeCard

theorem bijective_mk_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  apply GlobalTheory.CMVal.Model.IsCMType.bijective <;> assumption

theorem card_eq_finrank_of_isCMType : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2),
    Fintype.card I = Module.finrank K E := by
  intro K E _ _ _ _ _ _ I _ φ hφ h2
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (bijective_mk_of_isCMType hφ)
  have hE : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have hr : NumberField.InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    omega
  have hKE : Module.finrank ℚ E = Module.finrank ℚ K * Module.finrank K E :=
    (Module.finrank_mul_finrank ℚ K E).symm
  rw [h2] at hKE
  omega

end GlobalTheory.CMTypeCard
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

theorem height_comap_eq_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  apply GlobalTheory.ComplementaryForms.height_under_eq_one <;> assumption

theorem exists_uniformiser (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) :
    ∃ π : A, ∀ [p.IsPrime], p.height = 1 → Irreducible (algebraMap A (Localization.AtPrime p) π) := by
  by_cases h : p.IsPrime ∧ p.height = 1
  · obtain ⟨hp, h1⟩ := h
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one A p h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj p.primeCompl ϖ
    refine ⟨x, fun _ => ?_⟩
    have hu : IsUnit (algebraMap A (Localization.AtPrime p) s) := IsLocalization.map_units _ s
    have e : algebraMap A (Localization.AtPrime p) x = ϖ * algebraMap A (Localization.AtPrime p) s :=
      hxs.symm
    rw [e]
    exact (irreducible_mul_isUnit hu).mpr hϖ
  · exact ⟨1, fun h1 => absurd ⟨inferInstance, h1⟩ h⟩

end GlobalTheory.KummerEnlarge

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

theorem exists_kummer_enlargement : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ a : A, a ≠ 0 →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      ∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π := by
  intro T _ _ _ hT q hq hqT A _ _ _ _ _ _ i hi hloc a ha
  classical
  haveI : IsIntegrallyClosed T := GlobalTheory.VertUnitsNoeth.isIntegrallyClosed_of_absIntClosed' T hT
  choose π hπ using exists_uniformiser A
  have hy : ∀ p : Ideal A, ∃ y : T, y ^ q = i (π p) := by
    intro p
    obtain ⟨y, hy⟩ := hT (X ^ q - C (i (π p))) (monic_X_pow_sub_C _ hq.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hq)
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using hy
  choose y hy using hy
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})
  set S : Finset T := (Algebra.EssFiniteType.finset ℤ A).image i ∪ hfin.toFinset.image y with hS

  have hgen : ∀ z ∈ Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A),
      i z ∈ gen S := by
    intro z hz
    have h2 : i.toIntAlgHom z ∈ (Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A)).map
        i.toIntAlgHom := Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩
    rw [AlgHom.map_adjoin] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro t ⟨u, hu, rfl⟩
    simp only [hS, Finset.coe_union, Finset.coe_image]
    exact Or.inl ⟨u, hu, rfl⟩
  have hmem : ∀ x : A, i x ∈ loc S := by
    intro x
    haveI := Algebra.EssFiniteType.isLocalization ℤ A
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid ℤ A) x
    refine ⟨i (m.1 : A), gen_le_norm S (hgen _ m.1.2), ?_, ?_⟩
    · exact (IsLocalization.map_units A m).map i
    · rw [mul_comm, ← map_mul]
      have e : x * (m.1 : A) = (r : A) := hrm
      rw [e]
      exact gen_le_norm S (hgen _ r.2)
  let f : A →+* loc S := i.codRestrict (loc S) hmem
  have hfinj : Function.Injective f := fun x x' h => hi (congrArg Subtype.val h)
  haveI := loc_isLocalization S
  haveI : IsNoetherianRing (loc S) :=
    IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)
  haveI : IsIntegrallyClosed (norm S) := norm_isIntegrallyClosed S
  haveI : IsIntegrallyClosed (loc S) :=
    isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)
  haveI : IsLocalRing (loc S) := loc_isLocalRing S
  refine ⟨loc S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.VertUnitsNoeth.essFiniteType_loc S, f, (loc S).subtype, hfinj, Subtype.val_injective,
    ⟨fun x hx => isUnit_of_isUnit_coe S x hx⟩, RingHom.ext fun _ => rfl, ?_⟩
  intro p₁ _ hp₁ hfa
  letI : Algebra A (loc S) := f.toAlgebra
  letI : Algebra A T := i.toAlgebra

  have hyint : ∀ p : Ideal A, IsIntegral A (y p) := by
    intro p
    refine ⟨X ^ q - C (π p), monic_X_pow_sub_C _ hq.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy]
    exact sub_self _
  have hgenC : ∀ z ∈ gen S, z ∈ integralClosure A T := by
    intro z hz
    have hle : gen S ≤ (integralClosure A T).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      intro t ht
      simp only [hS, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image] at ht
      rcases ht with ⟨u, -, rfl⟩ | ⟨p, -, rfl⟩
      · exact isIntegral_algebraMap
      · exact hyint p
    exact hle hz
  have hnormint : ∀ x (hx : x ∈ norm S), IsIntegral A (⟨x, norm_le_loc S hx⟩ : loc S) := by
    intro x hx
    let φ : gen S →+* integralClosure A T :=
      (gen S).val.toRingHom.codRestrict (integralClosure A T) (fun z => hgenC _ z.2)
    have h1 : IsIntegral (integralClosure A T) x :=
      IsIntegral.map_of_comp_eq φ (RingHom.id T) rfl hx.1
    have h2 : IsIntegral A x := isIntegral_trans x h1
    let g : loc S →ₐ[A] T := { (loc S).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff g Subtype.val_injective).mp h2
  let B := integralClosure A (loc S)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (fun x x' h => hfinj (congrArg Subtype.val h))
  haveI : Algebra.HasGoingDown A B := inferInstance
  let M : Submonoid B := (IsUnit.submonoid (loc S)).comap (algebraMap B (loc S))
  haveI hML : IsLocalization M (loc S) := by
    refine ⟨fun m => m.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, hsu, hsz⟩ := z.2
      let sB : B := ⟨⟨s, norm_le_loc S hs⟩, hnormint s hs⟩
      let tB : B := ⟨⟨s * z, norm_le_loc S hsz⟩, hnormint _ hsz⟩
      have hsM : sB ∈ M := isUnit_of_isUnit_coe S _ hsu
      refine ⟨(tB, ⟨sB, hsM⟩), Subtype.ext ?_⟩
      change (z : T) * s = s * z
      ring
    · have : u = v := Subtype.val_injective h
      rw [this]
  set P : Ideal B := p₁.comap (algebraMap B (loc S)) with hP
  have hPh : P.height = 1 := by
    rw [hP, ← hp₁]
    exact IsLocalization.height_under M p₁
  have hcomap : p₁.comap f = P.comap (algebraMap A B) := by
    rw [hP, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    rfl
  have hne : P.comap (algebraMap A B) ≠ ⊥ := by
    rw [← hcomap]
    intro h
    have : a ∈ p₁.comap f := hfa
    rw [h, Ideal.mem_bot] at this
    exact ha this
  have hheight : (p₁.comap f).height = 1 := by
    rw [hcomap]
    exact height_comap_eq_one_of_goingDown P hPh hne

  have hmin : p₁.comap f ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hfa⟩, fun r hr hrp => ?_⟩
    obtain ⟨hrprime, har⟩ := hr
    by_contra hlt
    have hlt' : r < p₁.comap f := lt_of_le_of_ne hrp (fun e => hlt (e ▸ le_rfl))
    haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have hr0 : (⊥ : Ideal A) < r := by
      refine bot_lt_iff_ne_bot.mpr fun h => ha ?_
      have : a ∈ r := har (Ideal.mem_span_singleton_self a)
      rw [h, Ideal.mem_bot] at this
      exact this
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hr0
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt'
    rw [hheight] at h2
    have h4 : (1 : ℕ∞) ≤ r.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  have hyS : y (p₁.comap f) ∈ S := by
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hmin))
  refine ⟨hheight, π (p₁.comap f), hπ _ hheight, ⟨y (p₁.comap f), mem_loc_of_mem S hyS⟩, ?_⟩
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact hy _

end GlobalTheory.KummerEnlarge
end
end

section

namespace GlobalTheory.InjectiveAlgebraMapTorsionFree

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem algebraMap_injective_of_ne (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D]
    (hp : (p : D) ≠ 0) : Function.Injective (algebraMap ℤ_[p] D) := by
  by_contra hinj
  have hker : RingHom.ker (algebraMap ℤ_[p] D) ≠ ⊥ := fun h =>
    hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] D) := by
    rw [hn]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact hp (pow_eq_zero_iff'.mp hmem).1

theorem isTorsionFree_of_injective {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.IsTorsionFree R S :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr h

theorem norm_algebraMap_le (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  simpa using PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (x : PadicAlgCl p) (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

theorem exists_injective_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (D : Type) [CommRing D]
    [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D] (hp : (p : D) ≠ 0) :
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d : D, ‖φ d‖ ≤ 1 := by
  have hM : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
    apply algebraMap_injective_of_ne
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI := isTorsionFree_of_injective (algebraMap_injective_of_ne p D hp)
  haveI := isTorsionFree_of_injective hM
  let φ : D →ₐ[ℤ_[p]] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, fun d => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap ℤ_[p] (PadicAlgCl p) a = 0 := by
      rw [← φ.commutes]; exact ha
    exact (map_eq_zero_iff _ hM).mp this
  · exact norm_le_one_of_isIntegral p _ ((Algebra.IsIntegral.isIntegral d).map φ)

end GlobalTheory.InjectiveAlgebraMapTorsionFree
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel

theorem section_ext_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (h : X ⟶ Sp k) {f g : Sp k ⟶ X}
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (pt : Sp k) (e : f pt = g pt) : f = g := by
  apply GlobalTheory.KeyKa.section_ext_of_apply_eq <;> assumption

theorem finite_points_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B) (d : ℕ),
    IsIsogDeg π d → Set.Finite {a : 𝟙_ (Over (Sp k)) ⟶ A | a ≫ π = 1} := by
  intro k _ A B _ π d hπ
  have := hπ.fin
  let pt : Sp k := IsLocalRing.closedPoint k
  have hF := π.left.finite_preimage_singleton ((1 : 𝟙_ (Over (Sp k)) ⟶ B).left pt)
  refine Set.Finite.of_finite_image (f := fun a => a.left pt) (hF.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    change π.left (a.left pt) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, show a ≫ π = 1 from ha]
  · intro a _ b _ hab
    exact Over.OverMorphism.ext (section_ext_of_apply_eq A.hom (Over.w a) (Over.w b) pt hab)

end GlobalTheory.IwLevel
end
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticGaussianNormalised : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  intro l _ _
  have hS : CompanionTheory.ThKR.Mp.SecEx l := CompanionTheory.ThKR.Mp.secEx_of CompanionTheory.ThKR.Mp.mkElt CompanionTheory.ThKR.Mp.nrmUp
  have hO : CompanionTheory.ThKR.Mp.Surj l := CompanionTheory.ThKR.Mp.surj_of CompanionTheory.ThKR.Mp.ddNe hS
  have hC : CompanionTheory.ThKR.Mp.Cover l :=
    CompanionTheory.ThKR.Mp.cover_of CompanionTheory.ThKR.Mp.topG hO CompanionTheory.ThKR.Mp.ker hS CompanionTheory.ThKR.Mp.secDer
  haveI : IsTopologicalGroup (CompanionTheory.ThKR.Mp.G l) := CompanionTheory.ThKR.Mp.topG
  refine ⟨CompanionTheory.ThKR.Mp.G l, inferInstance, inferInstance, inferInstance, CompanionTheory.ThKR.Mp.pr, CompanionTheory.ThKR.Mp.om,
    CompanionTheory.ThKR.Mp.omS, CompanionTheory.ThKR.Mp.MpA.gs l, hC, hO, CompanionTheory.ThKR.Mp.ker, CompanionTheory.ThKR.Mp.continuous_om,
    CompanionTheory.ThKR.Mp.om_rho, CompanionTheory.ThKR.Mp.om_sch, ?_, ?_, ?_⟩
  · intro x
    rw [CompanionTheory.ThKR.Mp.MpA.gs, GroundTheory.Global.gaussianSchwartz_apply]
    have e : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    rw [e, Complex.ofReal_exp]
    push_cast
    ring_nf
  · intro j
    have h := CompanionTheory.ThKR.Mp.MpA.ann_gs (l := l) j
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, one_mulVec, one_mulVec] at h
    exact h
  · intro g P hP
    have h := CompanionTheory.ThKR.Mp.omS_nrm g 1 (CompanionTheory.ThKR.Mp.MpA.gs l) CompanionTheory.ThKR.Mp.MpA.ann_gs
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, Matrix.mul_one, CompanionTheory.ThKR.Mp.MpA.gs_zero, CompanionTheory.ThKR.Mp.MpA.dd_one, one_pow, one_mul] at h
    have eP : P = CompanionTheory.ThKR.Mp.upperParabolic (CompanionTheory.ThKR.Mp.pr g).1 := by
      ext a b; rw [hP]; rfl
    rw [eP]
    exact h

end GlobalTheory
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.latticeDetRelation_herbrand_eigenspace : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  first | exact @GlobalTheory.HerbrandBridge.exForm | exact GlobalTheory.HerbrandBridge.exForm | (intros; apply GlobalTheory.HerbrandBridge.exForm <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.DiscrTower

theorem finrank_mul_padicValInt_discr_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (l : ℕ) (hl : l.Prime) :
    Module.finrank K L * padicValInt l (discr K) ≤ padicValInt l (discr L) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero L)
  rw [h] at hL
  unfold padicValInt
  rw [h, Nat.multiplicity_mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL),
    Nat.multiplicity_pow]
  omega

theorem padicValInt_discr_div_le_delta_vp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime →
      (padicValInt l (discr (maximalRealSubfield E)) : ℝ) / Module.finrank ℚ (maximalRealSubfield E) ≤
        GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E l := by
  intro E _ _ _ l hl
  have h := finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl
  have h2 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E) := by exact_mod_cast Module.finrank_pos
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
  rw [div_le_div_iff₀ hF hE, ← h2]
  have h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤
      padicValInt l (discr E) := by exact_mod_cast h
  push_cast
  nlinarith

end GlobalTheory.DiscrTower
end
