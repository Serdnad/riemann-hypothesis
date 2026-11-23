module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle232
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Unramified.LocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.RingTheory.Unramified.Finite
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory.EtalePolyDvr

theorem isDiscreteValuationRing_atPrime_of_etale_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ p _ hp hP
  classical
  haveI hE : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing A[X] E
  haveI hR : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ hE
  haveI hLPn : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hR
  let Q' : Ideal E := P.comap (algebraMap E (Localization.AtPrime Q))
  haveI hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl
      (Localization.AtPrime P) P
  let e : Localization.AtPrime Q' ≃ₐ[E] Localization.AtPrime P :=
    IsLocalization.algEquiv Q'.primeCompl _ _
  haveI hAp : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  haveI hApd : IsDiscreteValuationRing (Localization.AtPrime p) :=
    GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp _
  have hAL : ∀ a : A, algebraMap A (Localization.AtPrime Q') a =
      algebraMap E (Localization.AtPrime Q') (algebraMap A E a) := fun a =>
    IsScalarTower.algebraMap_apply A E _ a
  have hALP : ∀ a : A, algebraMap A (Localization.AtPrime P) a =
      algebraMap E (Localization.AtPrime P) (algebraMap A E a) := fun a => by
    rfl
  have he : ∀ a : A, e (algebraMap A (Localization.AtPrime Q') a) =
      algebraMap A (Localization.AtPrime P) a := by
    intro a; rw [hAL, hALP, e.commutes]
  have hunder : Q'.comap (algebraMap A[X] E) = p.map C := by
    rw [← hP]
    show Ideal.comap _ (Ideal.comap _ P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have hunderA : ∀ a : A, algebraMap A E a ∈ Q' ↔ a ∈ p := by
    intro a
    rw [IsScalarTower.algebraMap_apply A A[X] E, ← Ideal.mem_comap, hunder,
      Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    refine ⟨fun h => by simpa using h 0, fun h n => ?_⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem
  have hcomp : (algebraMap A[X] (Localization.AtPrime Q')).comp C =
      algebraMap A (Localization.AtPrime Q') := by
    ext a
    simp only [RingHom.comp_apply]
    rw [hAL, IsScalarTower.algebraMap_apply A A[X] E, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A[X] E (Localization.AtPrime Q')]
  have hun : Algebra.IsUnramifiedAt A[X] Q' := inferInstance
  let p0 : Ideal A[X] := Q'.under A[X]
  let := Localization.AtPrime.algebraOfLiesOver p0 Q'
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq A[X] p0 Q').mp hun).2
  have hp0 : p0 = p.map C := hunder
  have hunit : ∀ a : A, a ∉ p → IsUnit (algebraMap A (Localization.AtPrime Q') a) := by
    intro a ha
    by_contra h
    apply ha
    rw [← hunderA, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q') Q', ← hAL]
    exact h
  haveI hflatE : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI hflatL : Module.Flat A (Localization.AtPrime Q') := Module.Flat.trans A E _
  have key : ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
    intro π hπ
    have hπp : π ∈ p := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p π]
      exact hπ.not_isUnit
    have hπ0 : π ≠ 0 := by rintro rfl; exact hπ.ne_zero (map_zero _)
    have hmAp := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
    have hmL : maximalIdeal (Localization.AtPrime Q') =
        Ideal.span {algebraMap A (Localization.AtPrime Q') π} := by
      rw [← hm, hp0, Ideal.map_map, hcomp]
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        have h1 : algebraMap A (Localization.AtPrime p) a ∈ maximalIdeal _ :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr ha
        rw [hmAp, Ideal.mem_span_singleton'] at h1
        obtain ⟨c, hc⟩ := h1
        obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
        have h2 : algebraMap A (Localization.AtPrime p) (a * s) =
            algebraMap A (Localization.AtPrime p) (b * π) := by
          rw [map_mul, map_mul, ← hc, mul_right_comm, IsLocalization.mk'_spec]
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists p.primeCompl _).mp h2
        have hts : (t : A) * s ∉ p := p.primeCompl.mul_mem t.2 s.2
        rw [Ideal.mem_comap, Ideal.mem_span_singleton,
          ← (hunit _ hts).dvd_mul_right, ← map_mul]
        have h3 : a * ((t : A) * s) = π * ((t : A) * b) := by linear_combination ht
        rw [h3, map_mul]
        exact dvd_mul_right _ _
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ hπp
    have hreg : ∀ x : Localization.AtPrime Q', algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime Q')
        (mem_nonZeroDivisors_of_ne_zero hπ0)
      exact this (show π • x = π • (0 : Localization.AtPrime Q') by
        rw [smul_zero, Algebra.smul_def, hx])
    have hmem : ∀ y : Localization.AtPrime Q',
        e y ∈ maximalIdeal (Localization.AtPrime P) ↔ y ∈ maximalIdeal _ := by
      intro y
      simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    have hmLP : maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap A (Localization.AtPrime P) π} := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hmem, hmL, Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← he, map_dvd_iff]
    have hregP : ∀ x : Localization.AtPrime P, algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [← he, ← map_mul, map_eq_zero_iff _ e.injective] at hx
      rw [hreg y hx, map_zero]
    exact GlobalTheory.Pat.dvr_of_maximalIdeal_eq_span hmLP hregP
  refine ⟨?_, fun π hπ => (key π hπ).2.2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl ϖ
  have ha : Irreducible (algebraMap A (Localization.AtPrime p) a) := by
    have h := IsLocalization.mk'_spec (Localization.AtPrime p) a s
    rw [← h]
    exact (irreducible_mul_isUnit (IsLocalization.map_units _ s)).mpr hϖ
  obtain ⟨hd, hdvr, -⟩ := key a ha
  exact ⟨hd, hdvr⟩

end GlobalTheory.EtalePolyDvr
end

section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HtVal

theorem dvr_val (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (K : Type) [Field K]
    [Algebra S K] [IsFractionRing S K] :
    ∃ w : Kˣ →* Multiplicative ℤ, ∀ x : Kˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔ (x : K) ∈ (algebraMap S K).range := by
  let v0 : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨IsLocalRing.maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  refine ⟨(WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹, fun x => ?_⟩
  have key : 0 ≤ Multiplicative.toAdd ((WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹ x) ↔ v0.valuation K x ≤ 1 := by
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, toAdd_inv, Left.nonneg_neg_iff]
    generalize hu : WithZero.unitsWithZeroEquiv.toMonoidHom
      ((Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom) x) = u
    have hc : v0.valuation K x = (u : WithZero (Multiplicative ℤ)) := by
      rw [← hu, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
      rfl
    rw [hc, ← WithZero.coe_one (α := Multiplicative ℤ), WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]
  rw [key]
  constructor
  · intro h
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_
    have : v = v0 := by
      ext1
      exact IsLocalRing.eq_maximalIdeal v.isMaximal
    rw [this]; exact h
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact v0.valuation_le_one y

theorem exists_val (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (h1 : P.height = 1) :
    ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔
        ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
  obtain ⟨w, hw⟩ := dvr_val (Localization.AtPrime P) (FractionRing R)
  refine ⟨w, fun x => (hw x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨s, s.2, r, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime P) (FractionRing R)) hrs
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at this
    rw [← this, hy, mul_comm]
  · rintro ⟨s, hs, r, hr⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl), ?_⟩
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
      rintro rfl; exact hs P.zero_mem
    apply mul_left_cancel₀ hs0
    rw [← hr, IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) s,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) r, ← map_mul]
    congr 1
    rw [mul_comm]
    exact IsLocalization.mk'_spec (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl)

theorem val_eq_zero_of_notMem (R : Type) [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsPrime]
    (w : (FractionRing R)ˣ →* Multiplicative ℤ)
    (hw : ∀ x : (FractionRing R)ˣ, 0 ≤ Multiplicative.toAdd (w x) ↔
      ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range)
    (u : (FractionRing R)ˣ) (a : R) (ha : (u : FractionRing R) = algebraMap R _ a) (haP : a ∉ P) :
    Multiplicative.toAdd (w u) = 0 := by
  have h1 : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hp : 0 ≤ Multiplicative.toAdd (w u) := (hw u).2 ⟨1, h1, a, by rw [map_one, one_mul, ha]⟩
  have hn : 0 ≤ Multiplicative.toAdd (w u⁻¹) := (hw u⁻¹).2 ⟨a, haP, 1, by
    rw [map_one, ← ha, Units.mul_inv]⟩
  rw [map_inv, toAdd_inv] at hn
  omega

theorem exists_vals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by
  intro R _ _ _ _ J _ g
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
        0 ≤ Multiplicative.toAdd (w x) ↔
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range :=
    fun P _ h1 => exists_val R P h1
  choose W hW using key
  have hsurj := fun j => IsLocalization.surj (nonZeroDivisors R) (g j : FractionRing R)
  choose nd hnd using hsurj
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hd0 : ∀ j, ((nd j).2 : R) ≠ 0 := fun j => nonZeroDivisors.coe_ne_zero _
  have hn0 : ∀ j, (nd j).1 ≠ 0 := by
    intro j h
    have := hnd j
    rw [h, map_zero] at this
    exact (mul_ne_zero (g j).ne_zero ((map_ne_zero_iff _ hinj).2 (hd0 j))) this
  have hc0 : (∏ j, (nd j).1 * ((nd j).2 : R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hn0 j) (hd0 j)
  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one hc0
  let T := hfin.toFinset
  let e := T.equivFin.symm
  have hmemT : ∀ i : Fin T.card, (e i : Ideal R).IsPrime ∧ (e i : Ideal R).height = 1 ∧
      (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ (e i : Ideal R) := fun i => hfin.mem_toFinset.1 (e i).2
  refine ⟨T.card, fun i => W (e i) (hmemT i).1 (hmemT i).2.1, ?_, ?_⟩
  · intro i x r hx
    refine (hW _ _ _ x).2 ⟨1, fun h => (hmemT i).1.ne_top ((Ideal.eq_top_iff_one _).2 h), r, ?_⟩
    rw [map_one, one_mul, hx]
  · intro x hx hv
    refine (fun h => ⟨h.choose, h.choose_spec.symm⟩)
      (ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (x : FractionRing R) ?_)
    intro P hP h1
    by_cases hcP : (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ P
    · obtain ⟨i, hi⟩ := e.surjective ⟨P, hfin.mem_toFinset.2 ⟨hP, h1, hcP⟩⟩
      have gen : ∀ (Q : Ideal R) (hQ : Q.IsPrime) (hQ1 : Q.height = 1), Q = P →
          0 ≤ Multiplicative.toAdd (W Q hQ hQ1 x) →
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
        rintro Q hQ hQ1 rfl h
        exact (hW Q hQ hQ1 x).1 h
      exact gen _ _ _ (congrArg Subtype.val hi) (hv i)
    · have hnP : ∀ j, (nd j).1 ∉ P ∧ ((nd j).2 : R) ∉ P := by
        intro j
        obtain ⟨k, hk⟩ : (nd j).1 * ((nd j).2 : R) ∣ ∏ j, (nd j).1 * ((nd j).2 : R) :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        refine ⟨fun h => hcP ?_, fun h => hcP ?_⟩
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_right _ h)
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_left _ h)
      have hker : Subgroup.closure (Set.range g) ≤ (W P hP h1).ker := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        let un : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ (nd j).1) ((map_ne_zero_iff _ hinj).2 (hn0 j))
        let ud : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ ((nd j).2 : R)) ((map_ne_zero_iff _ hinj).2 (hd0 j))
        have hgu : g j = un * ud⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact Units.ext (hnd j)
        have hn := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) un _ rfl (hnP j).1
        have hd := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) ud _ rfl (hnP j).2
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hgu, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, hn, hd, toAdd_one]
        simp
      have h0 : W P hP h1 x = 1 := hker hx
      exact (hW P hP h1 x).1 (by rw [h0, toAdd_one])

end GlobalTheory.HtVal
end
end

section

open IsLocalRing


theorem _root_.GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr : ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B), Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) → ∀ (p : Ideal C), p.IsPrime → ∀ f : B, (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) → ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  first | exact @GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | exact GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | (intros; apply GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_mod_f_of_surj (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hsurj : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (x : A' ⊗[A] A') :
    ∃ (c : A) (v : A' ⊗[A] A'), x = algebraMap A (A' ⊗[A] A') c + algebraMap A (A' ⊗[A] A') f * v := by
  set P : A' ⊗[A] A' → Prop := fun x => ∃ (c : A) (v : A' ⊗[A] A'),
    x = algebraMap A (A' ⊗[A] A') c + algebraMap A (A' ⊗[A] A') f * v with hP
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨c₁, v₁, rfl⟩ ⟨c₂, v₂, rfl⟩
    exact ⟨c₁ + c₂, v₁ + v₂, by rw [map_add (f := _)]; ring⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨c₁, v₁, rfl⟩ ⟨c₂, v₂, rfl⟩
    refine ⟨c₁ * c₂, algebraMap A (A' ⊗[A] A') c₁ * v₂ + v₁ * algebraMap A (A' ⊗[A] A') c₂
      + algebraMap A (A' ⊗[A] A') f * v₁ * v₂, ?_⟩
    rw [map_mul]; ring
  have himg : ∀ (g : A' →ₐ[A] A' ⊗[A] A') (a' : A'), P (g a') := by
    intro g a'
    obtain ⟨a, ha⟩ := hsurj a'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨a, g y, ?_⟩
    have : a' = algebraMap A A' a + y * algebraMap A A' f := by rw [hy]; ring
    rw [this, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes]; ring
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a b =>
    have h : a ⊗ₜ[A] b = (Algebra.TensorProduct.includeLeft (S := A) a) *
        (Algebra.TensorProduct.includeRight b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h]
    exact hmul _ _ (himg _ _) (himg _ _)
  | add x y hx hy => exact hadd _ _ hx hy

theorem etale_diag_complement (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A) :
    (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    ∃ e u : A' ⊗[A] A', (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) ∧
      algebraMap A (A' ⊗[A] A') f * u = 1 - e := by
  intro hsurj hinj
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := A')).1
    inferInstance
  obtain ⟨c, v, hcv⟩ := tensor_mod_f_of_surj A A' f hsurj (1 - t)
  have h0 : algebraMap A A' c + algebraMap A A' f * Algebra.TensorProduct.lmul' A v = 0 := by
    have := congrArg (Algebra.TensorProduct.lmul' A (S := A')) hcv
    rw [map_sub, map_one, ht1, sub_self, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes] at this
    exact this.symm
  have hc : algebraMap A A' c ∈ Ideal.span {algebraMap A A' f} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨-Algebra.TensorProduct.lmul' A v, by linear_combination -h0⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (hinj c hc)
  refine ⟨t, algebraMap A (A' ⊗[A] A') c' + v, ?_, ?_⟩
  · intro a
    rw [← neg_sub, neg_mul, ht a, neg_zero]
  · rw [hcv, ← hc', map_mul]; ring

end GlobalTheory
end

section

open scoped TensorProduct Polynomial

theorem _root_.GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat : ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by
  first | exact @GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | exact GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | (intros; apply GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.bijective_residue_comp_etale_henselian : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B], Function.Bijective (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  first | exact @GlobalTheory.EtaleHensel.bijective_residue_comp | exact GlobalTheory.EtaleHensel.bijective_residue_comp | (intros; apply GlobalTheory.EtaleHensel.bijective_residue_comp <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem bijective_baseChange_residueField_of_finiteEtale :
    ∀ (R A B : Type) [CommRing R] [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A]
      [Algebra R B] [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B]
      [Module.Finite R B],
      Function.Bijective (fun φ : A →ₐ[R] B =>
        Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) φ) :=
  fun R A B _ _ _ _ _ _ _ _ _ _ => bijective_baseChange_residueField_of_etale R A B

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.algHom_localizationAtPrime_factors_through_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p) (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift (algebraMap B (Localization.AtPrime p)) g (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  first | exact @GlobalTheory.FactorAway.factor_away | exact GlobalTheory.FactorAway.factor_away | (intros; apply GlobalTheory.FactorAway.factor_away <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K] (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  first | exact @GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | exact GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | (intros; apply GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ → Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) → ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  first | exact @GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | exact GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | (intros; apply GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq <;> assumption)
end
