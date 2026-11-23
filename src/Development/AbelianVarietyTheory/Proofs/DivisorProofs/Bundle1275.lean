module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Data.Matrix.Block
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NumFin

theorem finite_bdd_denom_conj_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  intro E _ _ d hd
  have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  set S := {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} with hS
  have hF := NumberField.Embeddings.finite_of_norm_le E ℂ (d : ℝ)
  have himg : (fun z : E => (d : E) * z) '' S ⊆ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ)} := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((d : E) * z) fun w => by
        have h := hz1 w
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        convert h using 2
        rw [← map_natCast (algebraMap E (w.adicCompletion E)) d, ← map_mul]
        rfl
      show IsIntegral ℤ ((d : E) * z)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      calc (d : ℝ) * ‖φ z‖ ≤ (d : ℝ) * 1 := by gcongr; exact hz2 φ
        _ = d := mul_one _
  have hinj : Set.InjOn (fun z : E => (d : E) * z) S := fun a _ b _ h => mul_left_cancel₀ hd0 h
  exact Set.Finite.of_finite_image (hF.subset himg) hinj

end GlobalTheory.NumFin
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.ZariskiDescent

theorem dvr_dvd_pow_of_mem_maximalIdeal {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] (x y : V) (hx : x ∈ IsLocalRing.maximalIdeal V) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨n, ⟨z ^ n * ↑u⁻¹, ?_⟩⟩
  rw [hu, mul_pow]
  have : (↑u * ↑u⁻¹ : V) = 1 := Units.mul_inv u
  linear_combination (-(z ^ n * ϖ ^ n)) * this

theorem mem_of_nonunits_of_localization {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] {A : Type} [CommRing A] (ι : A →+* L) (hι : Function.Injective ι)
    (hV : ∀ a, ι a ∈ V)
    (hloc : ∀ s ∈ V, ∃ b d : A, ι d ≠ 0 ∧ (ι d)⁻¹ ∈ V ∧ s = ι b / ι d)
    (P₁ : Ideal A) [P₁.IsPrime] (hne : P₁ ≠ ⊥) (hP₁ : ∀ z ∈ P₁, ι z ∈ V.nonunits) :
    ∀ x, ι x ∈ V.nonunits → x ∈ P₁ := by
  intro x hx
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hyV : (⟨ι y, hV y⟩ : V) ≠ 0 := by
    intro h
    apply hy0
    apply hι
    simpa using congrArg Subtype.val h
  have hxV : (⟨ι x, hV x⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp hx
  obtain ⟨n, w, hw⟩ := dvr_dvd_pow_of_mem_maximalIdeal V _ _ hxV hyV
  obtain ⟨b, d, hd0, hdinv, hwbd⟩ := hloc (w : L) w.2
  have hL : ι x ^ n = ι y * (ι b / ι d) := by
    have := congrArg Subtype.val hw
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul] at this
    rw [this, ← hwbd]
    rfl
  have hA : x ^ n * d = y * b := by
    apply hι
    rw [map_mul, map_mul, map_pow, hL]
    field_simp
  have hmem : x ^ n * d ∈ P₁ := by
    rw [hA]; exact P₁.mul_mem_right b hyP
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact Ideal.IsPrime.mem_of_pow_mem ‹_› n h
  · exfalso
    have := (ValuationSubring.mem_nonunits_iff_or (A := V)).mp (hP₁ d h)
    rcases this with h1 | h1
    · exact hd0 h1
    · exact h1 hdinv

end GlobalTheory.ZariskiDescent

namespace GlobalTheory.ZariskiDescent

theorem comap_nonunits_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L)
    (x : K) : x ∈ (V.comap φ).nonunits ↔ φ x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem height_le_one_of_going_down :
    ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L)
      [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) →
      R ≤ (V.comap φ).toSubring → ∀ t : Finset L,
      (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) →
      (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t),
        ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) →
      ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) →
      ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := by
  intro K L _ _ φ c V _ R _ hc hRV t ht hloc p hp hp0 hpq
  letI : Algebra R L := (φ.comp R.subtype).toAlgebra
  have halg : ∀ r : R, algebraMap R L r = φ r := fun r => rfl
  set S : Subalgebra R L := Algebra.adjoin R (t : Set L) with hSdef
  have hinjRL : Function.Injective (algebraMap R L) := by
    intro a b h
    rw [halg, halg] at h
    exact Subtype.ext (φ.injective h)
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjRL
    have := congrArg Subtype.val h
    simpa using this
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin (fun x hx => by
    obtain ⟨-, q, hq, hqx⟩ := ht x hx
    exact ⟨q, hq, hqx⟩)
  haveI : Algebra.HasGoingDown R S := inferInstance

  have hSV : ∀ z ∈ S, z ∈ V := by
    intro z hz
    have hz' : z ∈ S.toSubring := hz
    rw [hSdef, Algebra.adjoin_eq_ring_closure] at hz'
    refine (Subring.closure_le (t := V.toSubring)).mpr ?_ hz'
    rintro w (⟨r, rfl⟩ | hw)
    · exact (ValuationSubring.mem_comap).mp (hRV r.2)
    · exact (ht w hw).1

  have hclS : Subring.closure (Set.range (φ.comp c) ∪ ↑t) ≤ S.toSubring := by
    rw [Subring.closure_le]
    rintro w (⟨a, rfl⟩ | hw)
    · have : (φ.comp c) a = algebraMap R L ⟨c a, hc a⟩ := rfl
      rw [this]
      exact S.algebraMap_mem _
    · exact Algebra.subset_adjoin hw
  let ι : S →+* L := algebraMap S L
  have hι : Function.Injective ι := Subtype.val_injective
  let f : S →+* V := ι.codRestrict V (fun z => hSV z.1 z.2)
  let P : Ideal S := Ideal.comap f (IsLocalRing.maximalIdeal V)
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hPmem : ∀ z : S, z ∈ P ↔ (z : L) ∈ V.nonunits := by
    intro z
    show f z ∈ IsLocalRing.maximalIdeal V ↔ _
    exact ValuationSubring.coe_mem_nonunits_iff.symm
  let q : Ideal R := P.comap (algebraMap R S)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver q := ⟨rfl⟩
  have hqmem : ∀ r : R, r ∈ q ↔ (r : K) ∈ (V.comap φ).nonunits := by
    intro r
    show algebraMap R S r ∈ P ↔ _
    rw [hPmem, comap_nonunits_iff]
    rfl
  have hpq' : p ≤ q := fun r hr => (hqmem r).mpr (hpq r hr)
  obtain ⟨P₁, hP₁P, hP₁, hP₁o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) P hpq'
  have hpover : p = P₁.comap (algebraMap R S) := hP₁o.over
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    apply hp0
    rw [hpover, h, eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    apply hinjRL
    have := congrArg Subtype.val hr
    simpa using this
  have key := mem_of_nonunits_of_localization V ι hι (fun a => hSV a.1 a.2)
    (by
      intro s hs
      obtain ⟨b, hb, d, hd, hd0, hdinv, rfl⟩ := hloc s hs
      exact ⟨⟨b, hclS hb⟩, ⟨d, hclS hd⟩, hd0, hdinv, rfl⟩)
    P₁ hP₁ne (fun z hz => (hPmem z).mp (hP₁P hz))
  intro r hr
  rw [hpover, Ideal.mem_comap]
  apply key
  exact (hPmem _).mp ((hqmem r).mpr hr)

end GlobalTheory.ZariskiDescent
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.EssFiniteDescent

theorem essFiniteType_of_eq_div : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  intro K _ c R hcR E hcE hRE hft hloc
  let f : R →+* E :=
    { toFun := fun r => ⟨(r : K), hRE r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Submonoid R :=
    { carrier := {s | (s : K) ≠ 0 ∧ (s : K)⁻¹ ∈ E}
      mul_mem' := by
        rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
        refine ⟨by simpa using mul_ne_zero ha0 hb0, ?_⟩
        have : ((a * b : R) : K)⁻¹ = (b : K)⁻¹ * (a : K)⁻¹ := by
          push_cast; exact mul_inv_rev _ _
        rw [this]; exact E.mul_mem _ _ hb ha
      one_mem' := ⟨by simp, by simpa using E.one_mem⟩ }
  letI : Algebra ℂ R := (c.codRestrict R hcR).toAlgebra
  letI : Algebra R E := f.toAlgebra
  letI : Algebra ℂ E := (c.codRestrict E hcE).toAlgebra
  haveI : IsScalarTower ℂ R E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType ℂ R := hft
  haveI : IsLocalization M E := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs0, hs⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hs⟩, ?_⟩
      apply Subtype.ext
      change (s : K) * (s : K)⁻¹ = 1
      exact mul_inv_cancel₀ hs0
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, s, hs, hsE, rfl⟩ := hloc e he
      by_cases hs0 : s = 0
      · refine ⟨(0, 1), ?_⟩
        apply Subtype.ext
        change a / s * ((1 : M) : R) = (((0 : R)) : K)
        simp [hs0]
      · refine ⟨(⟨a, ha⟩, ⟨⟨s, hs⟩, by simpa using hs0, hsE⟩), ?_⟩
        apply Subtype.ext
        change a / s * s = a
        exact div_mul_cancel₀ a hs0
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : K) = y := congrArg (fun z : E => (z : K)) hxy
      simp [Subtype.ext this]
  haveI : Algebra.EssFiniteType R E := Algebra.EssFiniteType.of_isLocalization E M
  have h : Algebra.EssFiniteType ℂ E := Algebra.EssFiniteType.comp ℂ R E
  exact h

end GlobalTheory.EssFiniteDescent
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem fractions_unit_denominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro L _ ψ V P s₀ h1 h2
  classical
  choose b d hb hd hd0 hdV hx using h1
  let t : Finset L := (s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))
  refine ⟨t, ?_, ?_⟩
  · intro x hx'
    simp only [t, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩
    · exact hb y hy
    · exact hd y hy
  · let S : Subring L := Subring.closure (Set.range ψ ∪ (t : Set L))
    have hVone : (1 : L)⁻¹ ∈ V := by simpa using V.one_mem
    let F : Subring L :=
      { carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d}
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_mul_div_comm]
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂),
            d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_add_div _ _ h₁ h₂]
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        neg_mem' := by
          rintro _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩
          exact ⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }
    have htS : ∀ x ∈ t, x ∈ S := fun x hx' => Subring.subset_closure (Or.inr hx')
    have hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F := by
      rw [Subring.closure_le]
      rintro x (⟨c, rfl⟩ | hx')
      · exact ⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩
      · refine ⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
    intro s hs
    obtain ⟨B, hB, D, hD, hD0, hDV, rfl⟩ := h2 s hs
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩ := hle hB
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩ := hle hD
    have hd₁0 : d₁ ≠ 0 := by
      rintro rfl; exact hD0 (by simp)
    have hd₁V : d₁⁻¹ ∈ V := by
      have : d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹ := by
        field_simp
      rw [this]; exact mul_mem hDV hd₂V
    refine ⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩
    · rw [mul_inv]; exact mul_mem hb₂V hd₁V
    · rw [div_div_div_eq]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.fromBlocks_unitary_transfer : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  intro A O _ _ ι γ c n P K JL hinj hγ hP M G hM hG
  have hmul : ∀ {m : Type} [Fintype m] (X Y : Matrix m m O), (X * Y).map ι = X.map ι * Y.map ι := by
    intro m _ X Y; ext i j; simp [Matrix.mul_apply, map_sum]
  have hneg : (-JL).map ι = -(JL.map ι) := by ext i j; simp
  have hD : (Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ
      = (Matrix.fromBlocks JL 0 0 (-JL)).map ι := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hneg, ← hP]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  have hc : (G.map c).map ι = (G.map ι).map γ := by
    ext i j; simp [hγ]
  apply Matrix.map_injective hinj
  show (Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c).map ι = (Matrix.fromBlocks JL 0 0 (-JL)).map ι
  rw [hmul, hmul, Matrix.transpose_map, hc]
  conv_lhs => rw [← hD]
  have hG' : (Matrix.fromBlocks P 0 0 P * G.map ι).map γ = (Matrix.fromBlocks P 0 0 P).map γ * (G.map ι).map γ := by
    rw [Matrix.map_mul]
  calc (G.map ι)ᵀ * ((Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ) * (G.map ι).map γ
      = (Matrix.fromBlocks P 0 0 P * G.map ι)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P * G.map ι).map γ := by
        rw [hG', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (M * Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (M * Matrix.fromBlocks P 0 0 P).map γ := by rw [hG]
    _ = (Matrix.fromBlocks P 0 0 P)ᵀ * (Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ) * (Matrix.fromBlocks P 0 0 P).map γ := by
        rw [Matrix.map_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hD]
end
